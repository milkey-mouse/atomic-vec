#![feature(alloc_layout_extra)]
#![feature(coerce_unsized)]
#![feature(const_fn)]
#![feature(dispatch_from_dyn)]
#![feature(dropck_eyepatch)]
#![feature(optin_builtin_traits)]
#![feature(ptr_cast)]
#![feature(ptr_internals)]
#![feature(unsize)]

macro_rules! global_alloc {
    ([$($t:tt)*] Alloc $($rest:tt)*) => {
        global_alloc! { [ $($t)* Alloc = Global ] $($rest)* }
    };
    ([$($t:tt)*] $first:tt $($rest:tt)*) => {
        global_alloc! { [ $($t)* $first ] $($rest)* }
    };
    ([$($t:tt)*]) => {
        $($t)*
    };
    ($($t:tt)*) => {
        global_alloc! { [] $($t)* }
    };
}

mod atomic_ptr;
mod raw_vec;
