## Worker report

The accepted declaration is already present on the current newtargets-dag base; this packet records the Q98 worker reading and revalidates it. The dependency
node `def-weil-derived-complete.json` is restored byte for byte from the current
shared `newtargets-dag`: Q21's reviewed `WeilConjectures.IntegralOnSlice.IsComplete`
in `Sheaf.Paper.DerivedCompleteOnSlices`. Its `U = none` branch is definitionally
`IsDerivedCompleteUnrestricted`; the item's statement uses no completeness
predicate. The accepted Lean module, theorem signature and eight-declaration
record are retained. The delivery wrapper rebases the packet on current
`newtargets-dag`.

`Sheaf.Paper.CompletedScalarShift` states
`WeilConjectures.completedScalarComparison_commutesWithShift`. It retains the
prime `l`, `[Fact l.Prime]`, fields `E,L`, their `ℚ_[l]` algebra and finite-dimension
instances, inclusion `ι : E →ₐ[ℚ_[l]] L`, and arbitrary scheme `Y`. Scheme and
coefficient universes `t,u` remain independent. Completed coefficient sheaves,
quotient maps, scalar restriction, strict towers, ordinary extension, the
universal derived counit, and the specified comparison are the existing recorded
constructions. No new coefficient, site, cone, or comparison is chosen.

The clauses of the node are rendered as follows.

- The product D(P), its transitions, and h=1-s are the product of
  `integralScalarTowerFunctor` and `completedScalarRoosEndomorphism`. Each finite
  level is the recorded tensor functor `integralScalarReduction`, followed by
  `integralOperationsRestrict`.
- `completedScalarShiftLevelIso` fixes the finite-level identification using
  `mapCochainComplexShiftIso` twice: first for ordinary quotient tensor, then for
  the underlying restriction-of-scalars functor. Its components are degreewise
  identities. `completedScalarShiftProductIso` is their product followed by
  `PreservesProduct.iso.symm`. There is no existential tower reindexing.
- C(P) is exactly `integralScalarComplexFunctor`, whose definition is the recorded
  mapping cocone of h. Its coordinates are the `mappingCocone.inl` and
  `mappingCocone.inr` summands, detected respectively by `fst` and `snd`.
  `completedScalarShiftConeFormula` states coefficient one on **inl** and
  `m.negOnePow` on **inr**, with explicit degree reindexing in the target. This
  uses the mapping cocone directly; it does not apply the unshifted cone's
  standard shift isomorphism or its opposite sign normalization.
- The quantified `eC : integralScalarComplexFunctor.CommShift ℤ` provides alpha
  as the *same* natural isomorphism `(eC.commShiftIso m).app P` in every subsequent
  clause. The first conjunct applies `completedScalarShiftConeFormula` to eC itself, and that
  predicate fixes the two components of its shift-isomorphism hom.
  Naturality is the naturality of `eC.commShiftIso m` on every chain map;
  `eC.commShiftIso_zero` identifies alpha_0 with `Functor.CommShift.isoZero`,
  and `eC.commShiftIso_add m n` identifies alpha_(m+n) with
  `Functor.CommShift.isoAdd`. Thus chain-level naturality and the zero/successive
  laws refer to this componentwise normalized alpha, not just to derived maps.
- `completedScalarShiftChainEquation` is the actual equality of chain maps
  `tensorShift.hom.app P ≫ χ_P[m] = χ_(P[m]) ≫ alpha.hom`, where tensorShift is
  explicitly `completedOrdinaryScalarExtension.mapCochainComplexShiftIso` and
  χ is `completedScalarChainComparison`. The dependency fixes χ by its quotient
  components and zero `mappingCocone.snd` component; it is not an arbitrary
  morphism completing a triangle.
- For each flat-term K-flat representative `P` and integer `m`,
  `completedScalarShiftIntegralNormalization` supplies
  `hP : integralOperationsGoodComplex ... (P.obj⟦m⟧)`.
  `completedScalarShiftOrdinaryNormalization` normalizes `eE` using
  `completedScalarCounit`, `Q.commShiftIso`, and
  `Q.map` of the degreewise tensor shift. The integral normalization fixes `eL`
  using `integralScalarExtensionComparisonOfUniverses`, `Q.commShiftIso`, and
  `Q.map` of exactly the same alpha from `eC`.
- The final conjunct is `NatTrans.CommShift (completedScalarComparison ...) ℤ`
  for those normalized `eE,eL`. The representative normalizations quantify over
  every good representative, so the descended assertion is independent of the
  resolution and applies in particular to every derived-complete K. The node's
  proof explicitly observes that the chain construction works without the
  completeness assumption. The retained dependency's
  `IntegralOnSlice.IsComplete` at `U = none` is definitionally
  `IsDerivedCompleteUnrestricted`; no change to that dependency is needed.

These component equations remove the simultaneous (-1)^m twisting defect:
changing alpha's first component changes the first equation, whose product
identification is fixed. The counit and strict-localization normalizations
likewise fix the two derived comparisons, rather than merely asking for some
shift structures.

Dependency interfaces read and used: `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
(`completedOrdinaryScalarExtension`, `completedOrdinaryScalarComplex`,
`completedDerivedScalarExtension`, `completedScalarCounit`,
`completedScalarRoosEndomorphism`, `completedScalarChainComparison`,
`completedScalarComparison`);
`Sheaf.Paper.IntegralScalarExtensionUniverses`
(`integralScalarExtensionOfUniverses`,
`integralScalarExtensionComparisonOfUniverses`);
`Sheaf.Paper.IntegralScalarExtensionWellDefined`
(`integralScalarReduction`, `integralScalarFiniteComplex`, `integralScalarLevel`,
`integralScalarTowerFunctor`, `integralScalarComplexFunctor`);
`Sheaf.Paper.IntegralOperationsWellDefined`
(`integralOperationsRestrict`, `integralOperationsGoodComplex`,
`integralOperationsRoos`). The existing completeness interface is
`Sheaf.Paper.DerivedCompleteOnSlices`,
`WeilConjectures.IntegralOnSlice.IsComplete`; it needs no repair.
The coefficient-extension, completed-coefficient, general ringed-site module and
K-flat-resolution dependency records and their source signatures were reread.
Mathlib's `Scheme.ProEt`, `DerivedCategory`, `SheafOfModules.restrictScalars`,
`Functor.mapCochainComplexShiftIso`, `Functor.CommShift`, `NatTrans.CommShift`,
and the mapping-cocone inclusions/projections are used without copying them.

Edge cases: for m=0 both coordinates are identity; for m=1 and m=-1 only the
second coordinate is negated; for m=2 both signs are positive. On coordinates,
the two differentials are (e dx,-e dy-hx) and (e dx,-e dy-e hx); (1,e)
intertwines them, whereas (e,1) gives the old unwanted overall sign on χ.
For successive shifts e_n e_m=e_(m+n), so the same coordinate map has the
standard addition law. Empty schemes and zero complexes require no extra
hypothesis. All integers and every flat-term K-flat representative are included;
no boundedness, Noetherian or finite-field datum is imposed.

Searches retained from the saved packet and repeated during repair:

- `msearch.py ... leanfinder "completed scalar comparison commutes with cochain shifts strict Roos cone"`: eight generic mapping-cone hits, no specified completed scalar comparison.
- `msearch.py ... loogle "Functor.mapCochainComplexShiftIso, NatTrans.CommShift"`: zero hits; the service reports the first identifier unknown.
- `msearch.py ... grep "mapCochainComplexShiftIso|mappingCocone.*shift" Mathlib/Algebra/Homology`: zero service hits. Direct `rg` finds the canonical tensor reindexing in Mathlib/Algebra/Homology/HomotopyCategory/Shift.lean:247 and the mapping-cocone coordinate API in MappingCocone.lean.
- `rg` over project `WeilConjectures/` and `lean/Sheaf/` for `completedScalarShift` and `completedScalarComparison_commutesWithShift`: no existing declaration of this statement.

The module docstrings now describe the cocone coordinates, fixed reindexing,
chain equation, chain coherences, and both derived normalizations accurately.
No node-statement correction or new DAG notion is needed.

Verification: the final source passed `scompile.py` in both sandbox and library
module contexts, with no errors or warnings and within the per-file limit.
The final packet is also checked by the delivery dry run before pushing.

## Second reading by Q98

Self-check of the repaired node and file, as required by the dispatcher (no
additional agent started): all coefficient and scheme binders are retained,
and the universes are still independent. I checked the two coordinate equations
against `mappingCocone.inl_v_fst_f`, `inr_v_snd_v`, the cross-component zero
identities, and `id_X`; together they fix alpha uniquely degree by degree. The
unshifted-cone formula and its unconstrained tower isomorphism have been removed.
In particular the sign now lies on cocone **inr**, while χ's nonzero quotient
component lies on cocone **inl**.

I traced every occurrence of alpha: the component predicate, chain equation and
strict derived normalization all use the same `eC.commShiftIso`. Its naturality,
zero and addition laws are part of that chain-level `CommShift` structure.
The coordinate predicate takes eC itself and reads its shift-isomorphism hom
directly. Thus the components belong to that isomorphism, including its inverse
and coherence data; no additional unnormalized map is quantified.
The ordinary derived square uses the actual universal counit and the actual
degreewise tensor identification. The strict derived square uses the recorded
localization comparison and Q.map(alpha). The final NatTrans.CommShift therefore
cannot be satisfied by unrelated sign twists of eE/eL. This repairs H3(1)-(4).
The rewritten coordinate explanation and proof docstring repair H11. The existing
completeness dependency remains Q21's reviewed slice-general record, with the
global branch definitionally equal to `IsDerivedCompleteUnrestricted`. No data
definition uses sorry and the only postponed theorem is the item's named theorem.

## Return repair

H2/H13 of immutable head 30b2207628cb: restored the complete dependency node
`def-weil-derived-complete.json` from current `newtargets-dag`, including Q21's
reviewed slice-general Lean record. It introduces no delivery delta. Removed the
previous dependency-repair claim and checked the actual `IsComplete` definition:
`none` gives `IsDerivedCompleteUnrestricted`, while `some V` gives `RoosComplete`.
The accepted `CompletedScalarShift.lean` is unchanged. Its theorem uses no
completeness predicate, so neither its statement nor its imports need adjustment.
