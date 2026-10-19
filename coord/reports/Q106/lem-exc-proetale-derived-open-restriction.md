## Worker report

Repair of independent stage-2 review of head 0c217f8c18c2 (H3/H4). The module
`Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction` now uses one coherent intrinsic
finite-coefficient interface throughout. The original DAG statement is unchanged.
Only the item's `lean` record changes; comparison with the current shared node found
no differences in other fields. The required initial saved-packet dry run passed at
2ad0d10b2d, but the semantic defects in the return still required the following repair.

The declaration `proEtaleOpenRestrictionComparison` is exactly the `.hom` of the
published `sfProperOpenDerivedRestriction`, specialized to the chosen pullback.
That definition derives `sfProperOpenPullbackRestriction`, itself the canonical
sectionwise fibre-product comparison with the exact intrinsic pullback coordinates.
Its construction inserts the right-derived composition comparisons and the
right-derived/exact-descent comparisons, using the instances that direct image and
open restriction preserve K-injectives. Thus the sectionwise normalization is real
construction data, not just a docstring attached to a different exchange mate.
No properness instance is required by that published definition.

The new `proEtaleOpenRestrictionLambdaInverse` is the natural transformation
`Rr_*η` followed by inverse restriction at `k_!M`:

```
whiskerRight (exceptionalOpenAdjunction k A).unit (proEtaleConstantDerivedDirectImage r A)
  ≫ whiskerLeft (sfIntrinsicDerivedOpen A k) (sfProperOpenDerivedRestriction ...).inv
```

Its source is `Rr_*`, and its target is `k_! ⋙ Rp_* ⋙ i^*`. The final theorem
conjunct is `IsIso (proEtaleOpenRestrictionLambdaInverse p i A)`. Taking its inverse
gives exactly the node's specified λ, namely ρ at `k_!M` followed by `Rr_*η⁻¹`.
This is the explicit inverse formulation authorized by the return. There is no
existentially chosen isomorphism, arbitrary map, or unused unit-isomorphism definition.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`.
* Schemes are `{V T W : Scheme.{u}}`; the arbitrary morphism is `(p : V ⟶ T)`.
  The arbitrary open is `(i : W ⟶ T) [IsOpenImmersion i]`. No properness,
  cohomological-dimension, boundedness, or etale-origin binder occurs.
* `U`, `k`, and `r` are respectively `pullback p i`, `pullback.fst p i`, and
  `pullback.snd p i`. The square is `(IsPullback.of_hasPullback p i).flip`.
  The open-immersion instance for `k` is inherited by base change.
* Ordinary constant-A module sheaves and their uncompleted unbounded derived categories
  are `proEtaleRingModules X (proEtaleConstantRing X A)` and
  `proEtaleDerivedCategory X A`. The source of ρ is
  `proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicDerivedPullback A i`;
  the target is `sfIntrinsicDerivedPullback A k ⋙ proEtaleConstantDerivedDirectImage r A`.
  These are the finite-coefficient intrinsic realization of the recorded operations,
  reexported by `ProEtaleConstantRingOperations`, rather than mixing those operations
  with the separately constructed arbitrary-ring pullback.
* `IsIso (proEtaleOpenRestrictionComparison p i A)` asserts the natural comparison is
  invertible. `∀ L, IsIso ((...).app L)` explicitly retains every unbounded object.
  Naturality is part of the actual natural transformation, not additional chosen data.
* The termwise same-fibre-product normalization is inherited by directly using
  `sfProperOpenDerivedRestriction`. Its exact construction uses
  `sfProperOpenFixedRestrictionIso`, induced by `Over.pullbackMapComparison`, together
  with scalar-normalized coefficient realization. It preserves restrictions and actions.
* Preservation of K-injectives by `k^*` is used in that definition through
  `(sfIntrinsicOpenAdjunction A k).preservesKInjectiveComplexes`. Its left adjoint is
  precisely `sfIntrinsicExtensionByZero k A`, whose exactness is the recorded theorem.
* Exact derived extension by zero is `sfIntrinsicDerivedOpen A k`. Its unit η is
  `(exceptionalOpenAdjunction k A).unit`; this is the termwise localization of the
  same canonical open adjunction, in the pullback coordinates used by ρ. The sheaf
  open-unit theorem supplies the invertibility in the proof plan. The specified λ is
  retained through its explicitly defined inverse, whose `IsIso` is asserted.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and its base-change
  instance; `Mathlib.AlgebraicGeometry.Pullbacks`: `pullback` and its projections.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`;
  `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` (Mathlib `SheafOfModules`).
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded ordinary
  coefficient operations and its reexported finite interface;
  `ProEtaleIntrinsicFiniteOperations.sfIntrinsicDerivedPullback` and
  `ProEtaleConstantDerivedDirectImage.proEtaleConstantDerivedDirectImage`.
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero` and `sfIntrinsicModuleEquivalence`;
  `ProEtaleIntrinsicExtensionByZeroAdjunction.sfIntrinsicExtensionByZeroAdjunction`;
  `ProEtaleIntrinsicExtensionByZeroExact.sfIntrinsicExtensionByZero_exact`;
  `ProEtaleIntrinsicOpenUnit.sfIntrinsicOpenUnit_isIso`.
* `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`;
  proof-dependency imports include the recorded K-injective resolutions, total-derived,
  Hom-derived, preservation, and weakly-etale localization interfaces.
* Reused helpers: `Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange`,
  `sfProperOpenDerivedRestriction` and `sfProperOpenPullbackRestriction`;
  `ProEtaleProperOpenSheafComparison.sfProperOpenFixedRestrictionIso`;
  `IntrinsicDerivedOpenAdjunction.exceptionalOpenAdjunction`;
  `ProEtaleOpenSquareExchange.sfIntrinsicDerivedOpen` and `sfIntrinsicOpenAdjunction`.

Import-cycle note: the reusable Q100 construction is in the consumer module
`ProperExceptionalOpenBaseChange`. It contains no import of this item, and is now
imported to share its canonical helper. Adding this item's future proof import back
into that consumer would close a cycle, so that reverse proof-only import must be
omitted under stages/2-statements.md §3.7. No Q100 theorem is used to construct ρ;
the definition only derives the existing sheaf comparison. No new DAG dependency
on the downstream proposition is added.

Searches performed:

* `msearch.py ... leanfinder "unbounded derived direct image of pro-etale module sheaves commutes with restriction to an open scheme"` returned eight Mathlib hits about generic scheme-module restriction and no fixed-coefficient unbounded pro-etale comparison.
* `msearch.py ... loogle "IsIso"` returned no hit (`unknown identifier 'IsIso'`); this is recorded as an unavailable/nonmatching Loogle search, not as evidence of an existing declaration.
* `msearch.py ... grep "proEtale.*Derived.*DirectImage|AmbientRingedExchange" AlgebraicGeometry` returned no direct target match.
* `rg` over the source and project searched `proEtale.*OpenRestriction`, `DerivedOpenRestriction`, and the target id. The existing `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_openImmersion` is etale-only and bounded-below, so it is not this pro-etale unbounded statement. The generic `proEtaleOpenRestriction_isRightAdjoint` and `proEtaleRingOpenExtension` are underived constructions, not the target comparison theorem.

Additional repair searches: `rg` for `sfProperOpenDerivedRestriction`,
`exceptionalOpenAdjunction`, `sfIntrinsicDerivedOpen`, and `sfIntrinsicDerivedPullback`
in `lean/Sheaf` located the coherent Q100 interface and its underlying constructions.
The full declarations and docstrings of these definitions were read, including the
canonical fixed-section map, exact descent, open adjunction and coefficient transports.
The old `proEtaleIntrinsicOpenUnitIso` duplicated `sfProperOpenUnitIso` and was removed.
The old `ChosenCartesianSquare` and ambient ringed-exchange wrappers were also removed.

Edge cases checked: identity open, empty open, identity `p`, zero coefficient ring,
non-quasi-compact opens, and complexes unbounded in both directions. The pullback,
sectionwise restriction and derived adjunction unit exist in every case; no bound or
extra scheme property is needed. The inverse formulation includes every M in D(U,A).

No new nodes, dependency repairs, or statement corrections are needed. No
STATEMENT-DISPUTED flag remains. Definitions contain actual data; the only `sorry`
is the named main theorem with its source and full natural-language proof plan.

## Second reading by Q106

I reread the node, the repaired module, and the Q100 and intrinsic adjunction source
signatures. The returned H3 defect was the existential third conjunct: it did not fix λ.
It is replaced by invertibility of the explicit inverse composite of the actual derived
unit and the inverse of exactly the ρ used by the first two conjuncts. The returned H4
defect was a mismatch between two pullback/direct-image presentations and an ambient
exchange map without termwise normalization. The first two conjuncts now refer to the
published normalized restriction using `proEtaleConstantDerivedDirectImage` and
`sfIntrinsicDerivedPullback`; the extension composite uses `sfIntrinsicDerivedOpen`
and `exceptionalOpenAdjunction`, so its middle terms compose directly.
The initial compiler check found only missing qualification for the functor whiskering
operations; opening `CategoryTheory.Functor` fixes that namespace issue.
The ring, morphism and open hypotheses, chosen fibre product, naturality, unboundedness,
sectionwise K-injective normalization, exact extension and canonical unit match every
clause as listed above. The `lean.statement` field is extracted verbatim from the
repaired theorem signature. This was a self-check by the dispatcher-started worker;
no other agent was started.

Validation: final `scompile.py Q106 lem-exc-proetale-derived-open-restriction
lean/Sheaf/SecSmoothPurity/ProEtaleDerivedOpenRestriction.lean` passed both the sandbox
check (5.4 seconds) and exact library-path check (54.0 seconds), with no errors or
warnings. A local metadata check verified all three declarations are recorded, the
stored theorem signature is verbatim, every Lean line is at most 100 characters,
and the only postponed proof is the main theorem.
