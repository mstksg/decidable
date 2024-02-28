Changelog
=========

Version 0.3.1.1
---------------

*February 27, 2024*

<https://github.com/mstksg/functor-products/releases/tag/v0.3.1.1>

*   Remove upper bounds and deprecated pragmas

Version 0.3.1.0
---------------

*July 4, 2023*

<https://github.com/mstksg/functor-products/releases/tag/v0.3.1.0>

*   Now requires singletons-3.0 and above, and GHC 9.2 and above

Version 0.3.0.0
---------------

*Feburary 2, 2020*

<https://github.com/mstksg/decidable/releases/tag/v0.3.0.0>

*   Update to work with *singletons-2.6*, the type family update
*   Change `Evident` to now be a defunctionalization symbol for `Sing`, instead
    of a type synonym with `TyPred`, to match with *singletons-2.6*.  Most code
    in practice should be the same.
*   Fix instances for `FProd`s: now can prove and decide any `FProd f (Wit p)`,
    and can prove and decide and auto any `FProd f WrappedSing`.

Version 0.2.1.0
---------------

*August 24, 2019*

<https://github.com/mstksg/decidable/releases/tag/v0.2.1.0>

*   Add `autoTC` for convenient usage of `auto` with type constructors.

Version 0.2.0.0
---------------

*August 12, 2019*

<https://github.com/mstksg/decidable/releases/tag/v0.2.0.0>

*   Full restructuring of the Universe system, pulling it all out into a new
    package, *functor-products*.

Version 0.1.5.0
---------------

*March 6, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.5.0>

*   Add `allToAny` to *Data.Type.Predicate.Quantification*.
*   Add `PPMapV`, `EqBy`, and `IsTC` to *Data.Type.Predicate.Param*.
*   Kind-indexed singletons for indices in *Data.Type.Universe*.

Version 0.1.4.0
---------------

*October 29, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.4.0>

*   Added `tripleNegation` and `negateTwice` to *Data.Type.Predicate.Logic*,
    for more constructivist principles.
*   Renamed `excludedMiddle` to `complementation`.
*   Add `TyPP`, `SearchableTC`, `searchTC`, `SelectableTC`, `selectTC` to
    *Data.Type.Predicate.Param*, to mirror `TyPred` and the
    `DecidableTC`/`ProvableTC` interface from *Data.Type.Predicate*

Version 0.1.3.1
---------------

*October 26, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.3.1>

*   *BUGFIX* Remove overlapping `Auto` instances for `IsNothing` and `IsLeft`.

Version 0.1.3.0
---------------

*October 24, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.3.0>

*   Added a type and `Universe` for universe disjunction or summing, `:+:`,
    with appropriate `Elem` and `Auto` instances.
*   Added `Universe` instances (and appropriate `Elem` and `Auto` instances)
    for `Proxy` (the null universe) and `Identity`.
*   `Auto` instances for `IsNothing` and `IsLeft`.


Version 0.1.2.0
---------------

*October 14, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.2.0>

*   New `:.:` for universe composition, with `Elem` and `Universe` instances,
    and associated functions for working with them alongside `Any`, `All`.
*   Many of the `Elem` instances and indices in *Data.Type.Universe* have had
    their name changed to be more consistent with their role as indices.
    `IsJust` is now `IJust`, `IsRight` is `IRight`, `Snd` is `ISnd`.
*   Convenience predicates for alternate universes, such as `IsJust`, `IsLeft`,
    `IsNothing`, etc.
*   `NotAll` quantifier added alongside `None`.
*   Many new implications added to *Data.Type.Predicate.Quantification*,
    converting not-any and all-not, etc.
*   `NotFound p` added as a convenience predicate synonym for `Not (Found p)`.
*   Some implications showing the equivalence between `Found (InP f)` and
    `NotNull f` added to *Data.Type.Predicate.Param*.
*   Many new deduction rules added to *Data.Type.Predicate.Auto*.  Please see
    module documentation for a detailed list of new rules and classes in this
    version.
*   Convenient combinators for dealing with `Refuted` and `Decision` added to
    *Data.Type.Predicate*: `elimDisproof` and `mapRefuted`.


Version 0.1.1.0
---------------

*October 12, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.1.0>

*   `flipDecision`, `forgetDisproof`, `forgetProof`, `isProved`, and
    `isDisproved` added to *Data.Type.Predicate* module.
*   `ProvableTC`, `DeccidableTC`, `proveTC`, and `decideTC` helper functions
    and constraints
*   *Data.Type.Predicate.Auto* module, for generating witnesses at
    compile-time.
*   Instances for injection and projection out of `&&&` and `|||`, with some
    tricks to prevent overlapping instance issues.

Version 0.1.0.0
---------------

*October 10, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.0.0>

*   Initial release.

