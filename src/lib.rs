#![no_std]

use core::{iter::once, mem::MaybeUninit, ops::ControlFlow};

use either::Either;

#[cfg(feature = "alloc")]
extern crate alloc;
pub trait ValSer<V>: Sized {
    type Kind;
    fn from_kind<T: Default>(
        k: Self::Kind,
        i: &mut impl Iterator<Item = ControlFlow<T, V>>,
    ) -> ControlFlow<T, Self>;
    fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind);
}
pub trait AnyKind {
    type Value<V>: ValSer<V, Kind = Self>;
}
#[repr(transparent)]
pub struct Value<V> {
    pub value: V,
}
impl<V> ValSer<V> for Value<V> {
    type Kind = ();

    fn from_kind<T: Default>(
        k: Self::Kind,
        i: &mut impl Iterator<Item = ControlFlow<T, V>>,
    ) -> ControlFlow<T, Self> {
        match i.next() {
            Some(a) => ControlFlow::Continue(Value { value: a? }),
            None => ControlFlow::Break(Default::default()),
        }
    }

    fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind) {
        (once(self.value), ())
    }
}
impl AnyKind for () {
    type Value<V> = Value<V>;
}
impl<V, A: ValSer<V>, B: ValSer<V>> ValSer<V> for (A, B) {
    type Kind = (A::Kind, B::Kind);

    fn from_kind<T: Default>(
        k: Self::Kind,
        i: &mut impl Iterator<Item = ControlFlow<T, V>>,
    ) -> ControlFlow<T, Self> {
        let a = A::from_kind::<T>(k.0, i)?;
        let b = B::from_kind::<T>(k.1, i)?;
        ControlFlow::Continue((a, b))
    }

    fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind) {
        let (a, ak) = self.0.to_values();
        let (b, bk) = self.1.to_values();
        (a.chain(b), (ak, bk))
    }
}
impl<A: AnyKind, B: AnyKind> AnyKind for (A, B) {
    type Value<V> = (A::Value<V>, B::Value<V>);
}
impl<V, A: ValSer<V>, B: ValSer<V>> ValSer<V> for Either<A, B> {
    type Kind = Either<A::Kind, B::Kind>;

    fn from_kind<T: Default>(
        k: Self::Kind,
        i: &mut impl Iterator<Item = ControlFlow<T, V>>,
    ) -> ControlFlow<T, Self> {
        match k {
            Either::Left(k) => ControlFlow::Continue(Either::Left(A::from_kind(k, i)?)),
            Either::Right(k) => ControlFlow::Continue(Either::Right(B::from_kind(k, i)?)),
        }
    }

    fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind) {
        match self {
            Either::Left(a) => {
                let (i, k) = a.to_values();
                (Either::Left(i), Either::Left(k))
            }
            Either::Right(a) => {
                let (i, k) = a.to_values();
                (Either::Right(i), Either::Right(k))
            }
        }
    }
}
impl<A: AnyKind, B: AnyKind> AnyKind for Either<A, B> {
    type Value<V> = Either<A::Value<V>, B::Value<V>>;
}
impl<V, A: ValSer<V>, const N: usize> ValSer<V> for [A; N] {
    type Kind = [A::Kind; N];

    fn from_kind<T: Default>(
        k: Self::Kind,
        i: &mut impl Iterator<Item = ControlFlow<T, V>>,
    ) -> ControlFlow<T, Self> {
        let mut xs = [const { MaybeUninit::uninit() }; N];
        for (k, x) in k.into_iter().zip(xs.iter_mut()) {
            x.write(A::from_kind(k, i)?);
        }
        ControlFlow::Continue(xs.map(|x| unsafe { x.assume_init() }))
    }

    fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind) {
        let mut is = [const { MaybeUninit::uninit() }; N];
        let mut ks = [const { MaybeUninit::uninit() }; N];
        for ((x, io), ko) in self.into_iter().zip(is.iter_mut()).zip(ks.iter_mut()) {
            let (i, k) = x.to_values();
            io.write(i);
            ko.write(k);
        }
        let is = is.map(|a| unsafe { a.assume_init() });
        (
            is.into_iter().flatten(),
            ks.map(|k| unsafe { k.assume_init() }),
        )
    }
}
impl<A: AnyKind, const N: usize> AnyKind for [A; N] {
    type Value<V> = [A::Value<V>; N];
}
#[cfg(feature = "alloc")]
const _: () = {
    use alloc::{
        collections::btree_map::BTreeMap,
        vec::{self, Vec},
    };

    impl<V, A: ValSer<V>> ValSer<V> for Vec<A> {
        type Kind = Vec<A::Kind>;

        fn from_kind<T: Default>(
            k: Self::Kind,
            i: &mut impl Iterator<Item = ControlFlow<T, V>>,
        ) -> ControlFlow<T, Self> {
            let mut a = Vec::new();
            for k in k.into_iter() {
                a.push(A::from_kind(k, i)?);
            }
            return ControlFlow::Continue(a);
        }

        fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind) {
            let mut is = Vec::new();
            let mut ks = Vec::new();
            for a in self.into_iter() {
                let (i, k) = a.to_values();
                is.push(i);
                ks.push(k);
            }
            (is.into_iter().flatten(), ks)
        }
    }
    impl<A: AnyKind> AnyKind for Vec<A>{
        type Value<V> = Vec<A::Value<V>>;
    }
    impl<K: Ord, V, A: ValSer<V>> ValSer<V> for BTreeMap<K, A> {
        type Kind = BTreeMap<K, A::Kind>;

        fn from_kind<T: Default>(
            k: Self::Kind,
            i: &mut impl Iterator<Item = ControlFlow<T, V>>,
        ) -> ControlFlow<T, Self> {
            let mut a = BTreeMap::new();
            for (l, k) in k.into_iter() {
                a.insert(l, A::from_kind(k, i)?);
            }
            return ControlFlow::Continue(a);
        }

        fn to_values(self) -> (impl Iterator<Item = V>, Self::Kind) {
            let mut is = Vec::new();
            let mut ks = BTreeMap::new();
            for (l, a) in self.into_iter() {
                let (i, k) = a.to_values();
                is.push(i);
                ks.insert(l, k);
            }
            (is.into_iter().flatten(), ks)
        }
    }
    impl<K: Ord,A: AnyKind> AnyKind for BTreeMap<K,A>{
        type Value<V> = BTreeMap<K,A::Value<V>>;
    }
};
