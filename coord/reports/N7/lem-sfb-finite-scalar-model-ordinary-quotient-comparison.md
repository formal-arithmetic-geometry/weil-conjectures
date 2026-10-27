## Worker report

The module `Sheaf.Paper.FiniteScalarOrdinaryQuotientComparison` states the canonical
comparison of total right-derived limits of strict derived and ordinary reductions.
The theorem has a `sorry` proof, as required for stage 2. Its auxiliary theorem
`powers_naturality` also has a `sorry` proof: it is the scalar-power square in the
node's last proof step, used to construct the actual maps occurring in the naturality
clause. Every other declaration has actual construction data. All declarations are
listed in `lean.declarations` and carry the owning node's source and blueprint tag.
The elementary tower/cone/cokernel constructions are first written for an arbitrary
abelian category and natural scalar endomorphism, then specialized in the theorem
to `scalar l E V`. This avoids repeatedly elaborating the entire concrete sheaf
module instance stack in each categorical construction, without adding a hypothesis.

The previous worker's stage-1 refusal is not applicable: `coord/brief-stage2.md` §0
explicitly permits a reviewed stage-1 split to receive its stage-2 statement. The live
node is split/reviewed and has no Lean record. No repair note for this item exists.
The accepted statement, dependencies, and proof are preserved verbatim.

### Hypotheses and clauses

- A prime ell is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type u`
  with `[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  The valuation ring and chosen uniformizer are the existing
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`,
  through `IntegralQuotient.integral` and `IntegralQuotient.multiplication ... 0`.
- `V : Scheme.{u}` is arbitrary. `Modules l E V` is literally the internal module
  category over `condensedRingObj (IntegralQuotient.integral l E) V` on
  `Scheme.ProEt.topology V`. `integral` uses the existing continuous-function
  condensed valuation ring, with the spectral/adic topology, not a discrete replacement.
- The finite scalar local-model hypothesis is the recorded
  `HasFiniteConstantLocalModel (IntegralQuotient.integral l E) V M`. Its cover and
  finite scalar presentations are existential locally; no simultaneous bound or
  global finiteness hypothesis is added. No separate constructibility or Tor-amplitude
  assumption is substituted for this predicate.
- Both `[HasDerivedCategory.{w} ...]` parameters specify only the chosen localization
  and morphism universe, for modules and strict towers, respectively. They do not
  constrain the geometry or require exact ordinary countable products. The small
  pro-etale site has its original object universe `u+1` and morphism universe `u`;
  the additive coefficient universe is `u+1`. No equality of these two site universes
  is imposed.
- `L`, `η`, and `[L.IsRightDerivedFunctor η (HomologicalComplex.quasiIso ...)]`
  specify total right-derived inverse limit on strict tower complexes. This is the
  universal property from the recorded strict-tower dependency. Quantification over
  any such normalized derived functor avoids choosing an arbitrary existential
  witness as construction data. The theorem is independent of the choice of model.
- Positive index n is represented by `n+1` with `n : ℕ`. `source M` has terms M and
  transition pi; `constant M` has terms M and identity transitions. `powers M` has
  components pi^(n+1). Its naturality equation is pi pi^(n+1) = pi^(n+2).
- `derivedTower M` is the mapping cone of `singleFunctor.map (powers M)` in the
  abelian category of strict towers. Evaluation gives `[M --pi^(n+1)--> M]`
  in degrees -1 and 0; its cone transition is (pi,identity). This is a strict tower
  complex, not merely a diagram in the derived category.
- `quotientTower M` is `singleFunctor.obj (cokernel (powers M))`. Cokernels of
  functor categories are levelwise cokernels in the sheaf module category, so these
  are the ordinary sheaf quotients M/pi^(n+1)M with the actual quotient transitions.
- `comparison M` is `mappingCone.descShortComplex` of this power map and its
  actual cokernel projection. It vanishes on the shifted source, is the cokernel
  quotient on the target, and is an actual strict chain map.
- The first conjunct of `finiteScalarOrdinaryQuotientComparison` is exactly
  `IsIso (L.map (DerivedCategory.Q.map (comparison M)))` for every such M.
- For every actual module map `f : M ⟶ N`, `sourceMap f` has components f and
  `constantMap f` is the constant transformation. `derivedMap f` is the induced
  cone map (f,f), and `quotientMap f` is the induced cokernel map, with the same
  scalar-power square. The second conjunct is the commuting square after Q and L.
  Thus naturality covers every actual map between finite scalar local models;
  it does not ask f to be an isomorphism or a chosen model presentation map.
- `derivedUnit M` is the cone inclusion of the target M[0], hence the identity
  in degree zero. `quotientUnit M` is the single complex of the cokernel projection.
  `diagonal M` uses `constLimAdj.unit` and the canonical single/limit-complex
  isomorphism. `limitUnit L η M a` is Q(diagonal), followed by η on the constant
  tower complex, then L(Q(a)). The third conjunct says precisely that the
  derived augmentation followed by L(Q(comparison)) equals the actual quotient
  augmentation. No identification of Rlim(constant M[0]) with M[0] is assumed.
- There are no quasi-compactness, Noetherianity, characteristic, ell-invertibility,
  torsion-freeness, completeness, or global torsion-exponent assumptions. The result
  does not assert a levelwise isomorphism or that M itself is complete.

### Dependency declarations and sources read

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its public import
  `Sheaf.NumberTheory.Padics.CoefficientExtension` supplies the actual integer
  ring, extended absolute value, and chosen uniformizer.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and
  `Scheme.ProEt.topology`, preserving the small pro-etale site.
- `def-weil-size-convention` is the metatheoretic convention node, implemented by
  the explicit universe levels and derived-localization parameters above.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, with the
  continuous coefficient constructors publicly retained by its imports.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, and the transported commutativity instance.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and
  `CondensedRing.moduleObjectDerivedPullback`; ordinary uncompleted derived categories.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, not the stronger stratified constructibility predicate.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`, with all transition maps retained.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, including
  the total right-derived unit, natural Roos triangle, and pro-zero cone criterion.
  Its coefficient universe is independent of the site's morphism universe. The
  fixed internal/section-action equivalence in
  `InternalAbelianSheafModule.sectionModuleEquivalence` identifies the two ordinary
  module encodings. No duplicated definition of the module category is introduced.

Proof dependencies are imported for stage 3: `Module.FinitePresentation` in
`Mathlib.Algebra.Module.FinitePresentation`; `DerivedCategory` and Q in
`Mathlib.Algebra.Homology.DerivedCategory.Basic`;
`Submodule.exists_smith_normal_form_of_le` in `Mathlib.LinearAlgebra.FreeModule.PID`;
`ConstantFiniteFreePresentationExtension.constantFiniteFreePresentationExtension`
in `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension`;
`IntegralQuotient.integral_quotient_resolution_normalization` in
`Sheaf.Paper.IntegralQuotientResolutionNormalization`;
`CategoryTheory.sliceRestrictionStrictDerivedLimit` in
`Sheaf.Targets.SliceRestrictionStrictDerivedLimit`;
`Padic.extension_integers_dvr` in `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`;
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` in
`Mathlib.RingTheory.DiscreteValuationRing.Basic`;
`condensed_cover_restriction_conservative` in
`Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative`.
Their signatures/docstrings and the node's six proof steps were read. None of these
imports closes an import cycle: this is a new leaf module.

The latest blueprint refinement proof was opened. It does not itself state this
extracted comparison; the node explicitly identifies the proof as agent formulated.
The proof docstring follows the accepted node's local torsion-kernel argument rather
than claiming that the blueprint already supplies it.

### Edge cases

Checked before writing: M=0, zero free rank, an empty scheme/cover, free models,
P=A/pi^b (including b=0), and infinite disjoint unions with unbounded local b.
For P=A/pi^b, the degree -1 kernel prevents levelwise invertibility, but its transition
pi^b vanishes, exactly the pro-zero criterion used in the node. The source and target
are ordinary derived limits; the statement does not erase this kernel levelwise.
On each member of an infinite cover the proof has its own bound c; the theorem has
no global bound parameter. The first quotient level is exponent one. The diagonal
normalization avoids any need to identify a constant tower's derived limit with M.
No statement fault or `STATEMENT-DISPUTED` issue was found.

### Searches

- `msearch.py ... leanfinder` query: “The derived inverse limit of derived uniformizer
  reductions of a finite scalar local model equals the derived inverse limit of its
  ordinary quotients naturally and compatibly with augmentation.” Eight results:
  perfectoid untilt congruences and ordinary AdicCompletion evaluation/factorization
  lemmas, none the sheaf tower comparison.
- `msearch.py ... loogle '"DerivedCategory", "lim"'`: zero hits.
- `msearch.py ... grep 'ordinaryQuotient|strict.*tower|derived.*completion'`:
  25 hits, mainly scalar towers and unrelated algebra; no match.
- `rg` on `lean/WeilConjectures` for the exact node id: no declaration.
- `rg` on `lean/Sheaf` and `lean/WeilConjectures` for finite-scalar/ordinary-quotient
  comparison and the proposed namespace/declaration: no exact match.
- Read nearby existing `PrincipalKoszulQuotientTowers`,
  `PrincipalReductionConeCalculus`, `PrincipalReductionDerivedNormalization`,
  `IntegralAugmentedQuotientTowers`, and `StrictScalarCompletionUnit`. They address
  coefficient Koszul towers, derived-reduction normalization, augmented scalar-change
  towers with different geometric hypotheses, or completion units, respectively;
  none states this local-model comparison of the two strict limits.
- Searched the related DAG chapters for cone/cokernel, finite-scalar, and ordinary
  quotient comparisons. The assigned node is the one for this exact statement.
  The auxiliary declarations belong to this node's specified maps and naturality,
  not independent new notions requiring additional definition nodes.

### Validation

All compilation uses the prescribed `scompile.py`, with its 60-second per-file limit.
Final clean compilation and delivery preflight are recorded by the delivery wrapper.
No library, shared-repository, launcher-script, or direct Git mutation was performed.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
