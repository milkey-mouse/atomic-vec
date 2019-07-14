use std::convert::From;
use std::ops::{CoerceUnsized, DispatchFromDyn};
use std::fmt;
use std::hash;
use std::marker::{PhantomData, Unsize};
use std::mem;
use std::cmp::Ordering;
use std::ptr::{NonNull, Unique};

/// A wrapper around a raw non-null `*mut T` that indicates that the possessor
/// of this wrapper owns the referent. Useful for building abstractions like
/// `Box<T>`, `Vec<T>`, `String`, and `HashMap<K, V>`.
///
/// Unlike `*mut T`, `AtomicUnique<T>` behaves "as if" it were an instance of `T`.
/// It implements `Send`/`Sync` if `T` is `Send`/`Sync`. It also implies
/// the kind of strong aliasing guarantees an instance of `T` can expect:
/// the referent of the pointer should not be modified without a AtomicUnique path to
/// its owning AtomicUnique.
///
/// If you're uncertain of whether it's correct to use `AtomicUnique` for your purposes,
/// consider using `AtomicNonNull`, which has weaker semantics.
///
/// Unlike `*mut T`, the pointer must always be non-null, even if the pointer
/// is never dereferenced. This is so that enums may use this forbidden value
/// as a discriminant -- `Option<AtomicUnique<T>>` has the same size as `AtomicUnique<T>`.
/// However the pointer may still dangle if it isn't dereferenced.
///
/// Unlike `*mut T`, `AtomicUnique<T>` is covariant over `T`. This should always be correct
/// for any type which upholds AtomicUnique's aliasing requirements.
#[repr(transparent)]
pub struct AtomicUnique<T: ?Sized> {
    pointer: *const T,
    // NOTE: this marker has no consequences for variance, but is necessary
    // for dropck to understand that we logically own a `T`.
    //
    // For details, see:
    // https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data
    _marker: PhantomData<T>,
}

impl<T: ?Sized> fmt::Debug for AtomicUnique<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

/// `AtomicUnique` pointers are `Send` if `T` is `Send` because the data they
/// reference is unaliased. Note that this aliasing invariant is
/// unenforced by the type system; the abstraction using the
/// `AtomicUnique` must enforce it.
unsafe impl<T: Send + ?Sized> Send for AtomicUnique<T> { }

/// `AtomicUnique` pointers are `Sync` if `T` is `Sync` because the data they
/// reference is unaliased. Note that this aliasing invariant is
/// unenforced by the type system; the abstraction using the
/// `AtomicUnique` must enforce it.
unsafe impl<T: Sync + ?Sized> Sync for AtomicUnique<T> { }

impl<T: Sized> AtomicUnique<T> {
    /// Creates a new `AtomicUnique` that is dangling, but well-aligned.
    ///
    /// This is useful for initializing types which lazily allocate, like
    /// `Vec::new` does.
    ///
    /// Note that the pointer value may potentially represent a valid pointer to
    /// a `T`, which means this must not be used as a "not yet initialized"
    /// sentinel value. Types that lazily allocate must track initialization by
    /// some other means.
    // FIXME: rename to dangling() to match AtomicNonNull?
    pub const fn empty() -> Self {
        unsafe {
            AtomicUnique::new_unchecked(mem::align_of::<T>() as *mut T)
        }
    }
}

impl<T: ?Sized> AtomicUnique<T> {
    /// Creates a new `AtomicUnique`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null.
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        AtomicUnique { pointer: ptr as _, _marker: PhantomData }
    }

    /// Creates a new `AtomicUnique` if `ptr` is non-null.
    pub fn new(ptr: *mut T) -> Option<Self> {
        if !ptr.is_null() {
            Some(unsafe { AtomicUnique { pointer: ptr as _, _marker: PhantomData } })
        } else {
            None
        }
    }

    /// Acquires the underlying `*mut` pointer.
    pub const fn as_ptr(self) -> *mut T {
        self.pointer as *mut T
    }

    /// Dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&*my_ptr.as_ptr()`.
    pub unsafe fn as_ref(&self) -> &T {
        &*self.as_ptr()
    }

    /// Mutably dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&mut *my_ptr.as_ptr()`.
    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut *self.as_ptr()
    }
}

impl<T: ?Sized> Clone for AtomicUnique<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for AtomicUnique<T> { }

impl<T: ?Sized, U: ?Sized> CoerceUnsized<AtomicUnique<U>> for AtomicUnique<T> where T: Unsize<U> { }

impl<T: ?Sized, U: ?Sized> DispatchFromDyn<AtomicUnique<U>> for AtomicUnique<T> where T: Unsize<U> { }

impl<T: ?Sized> fmt::Pointer for AtomicUnique<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T: ?Sized> Into<Unique<T>> for AtomicUnique<T> {
    #[inline]
    fn into(self) -> Unique<T> {
        unsafe { Unique::new_unchecked(self.pointer as *mut T) }
    }
}

impl<T: ?Sized> Into<NonNull<T>> for AtomicUnique<T> {
    #[inline]
    fn into(self) -> NonNull<T> {
        unsafe { NonNull::new_unchecked(self.pointer as *mut T) }
    }
}

impl<'a, T: ?Sized> From<Unique<T>> for AtomicUnique<T> {
    fn from(p: Unique<T>) -> Self {
        unsafe { AtomicUnique { pointer: p.as_ptr(), _marker: PhantomData } }
    }
}

impl<'a, T: ?Sized> From<NonNull<T>> for AtomicUnique<T> {
    fn from(p: NonNull<T>) -> Self {
        unsafe { AtomicUnique { pointer: p.as_ptr(), _marker: PhantomData } }
    }
}

impl<T: ?Sized> From<&mut T> for AtomicUnique<T> {
    fn from(reference: &mut T) -> Self {
        unsafe { AtomicUnique { pointer: reference as *mut T, _marker: PhantomData } }
    }
}

impl<T: ?Sized> From<&T> for AtomicUnique<T> {
    fn from(reference: &T) -> Self {
        unsafe { AtomicUnique { pointer: reference as *const T, _marker: PhantomData } }
    }
}

impl<'a, T: ?Sized> From<AtomicNonNull<T>> for AtomicUnique<T> {
    fn from(p: AtomicNonNull<T>) -> Self {
        unsafe { AtomicUnique { pointer: p.pointer, _marker: PhantomData } }
    }
}

/// `*mut T` but non-zero and covariant.
///
/// This is often the correct thing to use when building data structures using
/// raw pointers, but is ultimately more dangerous to use because of its additional
/// properties. If you're not sure if you should use `AtomicNonNull<T>`, just use `*mut T`!
///
/// Unlike `*mut T`, the pointer must always be non-null, even if the pointer
/// is never dereferenced. This is so that enums may use this forbidden value
/// as a discriminant -- `Option<AtomicNonNull<T>>` has the same size as `*mut T`.
/// However the pointer may still dangle if it isn't dereferenced.
///
/// Unlike `*mut T`, `AtomicNonNull<T>` is covariant over `T`. If this is incorrect
/// for your use case, you should include some [`PhantomData`] in your type to
/// provide invariance, such as `PhantomData<Cell<T>>` or `PhantomData<&'a mut T>`.
/// Usually this won't be necessary; covariance is correct for most safe abstractions,
/// such as `Box`, `Rc`, `Arc`, `Vec`, and `LinkedList`. This is the case because they
/// provide a public API that follows the normal shared XOR mutable rules of Rust.
///
/// Notice that `AtomicNonNull<T>` has a `From` instance for `&T`. However, this does
/// not change the fact that mutating through a (pointer derived from a) shared
/// reference is undefined behavior unless the mutation happens inside an
/// [`UnsafeCell<T>`]. The same goes for creating a mutable reference from a shared
/// reference. When using this `From` instance without an `UnsafeCell<T>`,
/// it is your responsibility to ensure that `as_mut` is never called, and `as_ptr`
/// is never used for mutation.
///
/// [`PhantomData`]: ../marker/struct.PhantomData.html
/// [`UnsafeCell<T>`]: ../cell/struct.UnsafeCell.html
#[repr(transparent)]
pub struct AtomicNonNull<T: ?Sized> {
    pointer: *const T,
}

/// `AtomicNonNull` pointers are not `Send` because the data they reference may be aliased.
// N.B., this impl is unnecessary, but should provide better error messages.
impl<T: ?Sized> !Send for AtomicNonNull<T> { }

/// `AtomicNonNull` pointers are not `Sync` because the data they reference may be aliased.
// N.B., this impl is unnecessary, but should provide better error messages.
impl<T: ?Sized> !Sync for AtomicNonNull<T> { }

impl<T: Sized> AtomicNonNull<T> {
    /// Creates a new `AtomicNonNull` that is dangling, but well-aligned.
    ///
    /// This is useful for initializing types which lazily allocate, like
    /// `Vec::new` does.
    ///
    /// Note that the pointer value may potentially represent a valid pointer to
    /// a `T`, which means this must not be used as a "not yet initialized"
    /// sentinel value. Types that lazily allocate must track initialization by
    /// some other means.
    #[inline]
    pub const fn dangling() -> Self {
        unsafe {
            let ptr = mem::align_of::<T>() as *mut T;
            AtomicNonNull::new_unchecked(ptr)
        }
    }
}

impl<T: ?Sized> AtomicNonNull<T> {
    /// Creates a new `AtomicNonNull`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null.
    #[inline]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        AtomicNonNull { pointer: ptr as _ }
    }

    /// Creates a new `AtomicNonNull` if `ptr` is non-null.
    #[inline]
    pub fn new(ptr: *mut T) -> Option<Self> {
        if !ptr.is_null() {
            Some(unsafe { Self::new_unchecked(ptr) })
        } else {
            None
        }
    }

    /// Acquires the underlying `*mut` pointer.
    #[inline]
    pub const fn as_ptr(self) -> *mut T {
        self.pointer as *mut T
    }

    /// Dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&*my_ptr.as_ptr()`.
    #[inline]
    pub unsafe fn as_ref(&self) -> &T {
        &*self.as_ptr()
    }

    /// Mutably dereferences the content.
    ///
    /// The resulting lifetime is bound to self so this behaves "as if"
    /// it were actually an instance of T that is getting borrowed. If a longer
    /// (unbound) lifetime is needed, use `&mut *my_ptr.as_ptr()`.
    #[inline]
    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut *self.as_ptr()
    }

    /// Cast to a pointer of another type
    #[inline]
    pub const fn cast<U>(self) -> AtomicNonNull<U> {
        unsafe {
            AtomicNonNull::new_unchecked(self.as_ptr() as *mut U)
        }
    }
}

impl<T: ?Sized> Clone for AtomicNonNull<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for AtomicNonNull<T> { }

impl<T: ?Sized, U: ?Sized> CoerceUnsized<AtomicNonNull<U>> for AtomicNonNull<T> where T: Unsize<U> { }

impl<T: ?Sized, U: ?Sized> DispatchFromDyn<AtomicNonNull<U>> for AtomicNonNull<T> where T: Unsize<U> { }

impl<T: ?Sized> fmt::Debug for AtomicNonNull<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T: ?Sized> fmt::Pointer for AtomicNonNull<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T: ?Sized> Eq for AtomicNonNull<T> {}

impl<T: ?Sized> PartialEq for AtomicNonNull<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

impl<T: ?Sized> Ord for AtomicNonNull<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

impl<T: ?Sized> PartialOrd for AtomicNonNull<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_ptr().partial_cmp(&other.as_ptr())
    }
}

impl<T: ?Sized> hash::Hash for AtomicNonNull<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_ptr().hash(state)
    }
}

impl<T: ?Sized> Into<NonNull<T>> for AtomicNonNull<T> {
    #[inline]
    fn into(self) -> NonNull<T> {
        unsafe { NonNull::new_unchecked(self.pointer as *mut T) }
    }
}

impl<T: ?Sized> From<NonNull<T>> for AtomicNonNull<T> {
    #[inline]
    fn from(non_null: NonNull<T>) -> Self {
        unsafe { AtomicNonNull { pointer: non_null.as_ptr() } }
    }
}

impl<T: ?Sized> From<AtomicUnique<T>> for AtomicNonNull<T> {
    #[inline]
    fn from(atomic_unique: AtomicUnique<T>) -> Self {
        unsafe { AtomicNonNull { pointer: atomic_unique.as_ptr() } }
    }
}

/*impl<T: ?Sized> From<Unique<T>> for AtomicNonNull<T> {
    #[inline]
    fn from(unique: Unique<T>) -> Self {
        unsafe { NonNull { pointer: unique.pointer } }
    }
}*/

impl<T: ?Sized> From<&mut T> for AtomicNonNull<T> {
    #[inline]
    fn from(reference: &mut T) -> Self {
        unsafe { AtomicNonNull { pointer: reference as *mut T } }
    }
}

impl<T: ?Sized> From<&T> for AtomicNonNull<T> {
    #[inline]
    fn from(reference: &T) -> Self {
        unsafe { AtomicNonNull { pointer: reference as *const T } }
    }
}
