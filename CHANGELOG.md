Changelog
=========

Version 0.1.4.0
---------------

*October 29, 2018*

<https://github.com/mstksg/decidable/releases/tag/v0.1.4.0>

*   Added `tripleNegative` and `negateTwice` to *Data.Type.Predicate.Logic*,
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

