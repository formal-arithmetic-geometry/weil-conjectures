# PR #1743 classification

The successful 4.35.0 cut prefixes in [Before.lean](Before.lean) and
[After.lean](After.lean) isolate `map_supportedRestrictionIntegral_comp`.
The old prefix takes 579.86 user CPU seconds and 3,729,204 KB peak RSS; the
fixed prefix takes 10.09 seconds and 3,550,928 KB. Kernel checking is only
3.40 versus 3.89 seconds. The old `refine` and `exact` consume 223 and 349
seconds. **Phase: elaboration, not a Kernel A-F case.**

The old `Adjunction.map_mateEquiv_app_comp` application makes elaboration match
the concrete `σ.hom.app` and full-subcategory composite against its generic
parameters. The [PR diagnosis](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1743)
identifies the old pair as `σ.hom.app` versus named `s.app`, with subsequent
`Meta.isDefEq` work inside `CategoryStruct.comp`. The fixed application uses
`map_mateEquiv_app_comp_of_hom_eq`, passes equalities of whole morphisms, and
finishes with `with_reducible exact`. The old call and phase reproduce here;
the inner Meta pair is cited from the historical diagnosis rather than dumped
again on 4.35.0.
