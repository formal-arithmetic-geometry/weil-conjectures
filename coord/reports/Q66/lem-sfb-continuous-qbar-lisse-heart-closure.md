## Worker report

The module Sheaf.Paper.ContinuousQbarLisseHeartClosure states the node without changing
its mathematical statement, statement dependencies, or proof plan. It defines the
real-data predicate ContinuousQbarLisseHeartClosure to package the requested assertions,
then states continuousQbar_lisse_heart_closure and its final-clause corollary
continuousQbar_lisse_heart_closure_of_immersion. Both theorem proofs are sorry. The helper
belongs to this node and is listed in lean.declarations; it introduces no independent
mathematical notion. There are no new nodes or dependency repairs.

Source read: the local PDF Hemo--Richarz--Scholbach arXiv:2305.18131, pp. 7--8 and 16--18:
Definition 3.3 and its stable-subcategory observation, Definition 6.1, Theorem 6.2(2), and
Corollaries 6.3 and 6.11. The module docstrings carry all six steps of the DAG proof.
The referenced Theorem 4.13 supplies the local-perfect-model input through the recorded
CondensedDualizableLocalPerfectModels module.

Hypothesis and clause correspondence:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]` in both theorems.
- A fixed algebraic closure of Q_ell: `(Ω : Type u) [NormedField Ω]`,
  `[NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`. The normed algebra structure expresses
  extension of the ell-adic norm, while IsAlgClosure gives algebraicity and algebraic
  closedness. There is no Completeness, finite-dimensionality, or finite-field binder.
- All continuous coefficients: `Profinite.continuousCoefficientRingObj Ω` has sections
  `ULift C(P, Ω)` with precomposition and pointwise ring operations. Its sheaf and monoid
  structure are definitionally those of the recorded
  `Profinite.continuousMapRingObjOfUniverse.{u,u} Ω`. The shared canonical ring interface
  supplies the commutative monoid instance. No bounded-image construction is used.
- On the small pro-etale site of T, R_T is
  `condensedRingObj (Profinite.continuousCoefficientRingObj Ω) T`, the underlying ring
  object of `coefficientRing`. The ambient category is `Mod (Sheaf
  (Scheme.ProEt.topology T) Ab.{u+1}) R_T`, the recorded internal-module construction.
- T is any scheme with Noetherian underlying topological space:
  `(T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]`. This is Mathlib's well-founded
  order on opens, equivalently the descending-chain condition on closed sets. It does
  not add local Noetherianity of scheme rings, separation, or connectedness.
- Lisse is exactly the recorded `IsLisseCoefficientModule`, whose pro-etale cover has a
  possibly varying natural-number rank and uses `Mod.IsFree`; Fin 0 is permitted.
- The first conjunct of ContinuousQbarLisseHeartClosure quantifies over every ambient
  module M and states `HasFiniteConstantLocalModel ... T M ↔ IsLisseCoefficientModule ... M`.
  The recorded finite-presentation-on-the-point construction gives precisely the scalar
  finite-constant models of the node, rather than arbitrary local coefficient matrices.
- Zero is `ObjectProperty.ContainsZero`; in conjunction with
  `ObjectProperty.IsClosedUnderIsomorphisms`, this includes every ambient zero object,
  including the chosen zero. The definitions were read in ObjectProperty/ContainsZero.
- Isomorphism closure is `ObjectProperty.IsClosedUnderIsomorphisms` of the lisse predicate.
- Kernel closure is `ObjectProperty.IsClosedUnderKernels` of that same predicate. Its
  definition quantifies over ambient kernel forks for maps whose two ends are lisse.
- Cokernel closure is `ObjectProperty.IsClosedUnderCokernels`, using ambient cokernel coforks.
  Together with isomorphism closure these are exactly the chosen ambient kernel/cokernel
  assertions, and impose no constant-rank hypothesis.
- Extensions are `ObjectProperty.IsClosedUnderExtensions`. Its field takes an ambient
  `ShortComplex`, its `ShortExact` proof, and lisse X1 and X3, and concludes lisse X2;
  the middle module has no lisse hypothesis.
- The final theorem has `{T X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]`
  and `(i : T ⟶ X) [IsImmersion i]`, and concludes all the same assertions on T.
  These are exactly a locally closed subscheme of a Noetherian scheme. No additional
  hypothesis is imposed on T. Its proof docstring gives the subspace argument.

Dependency declarations read and used:

- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosure (full class and docstring), and
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure: AlgebraicClosure. The statement uses
  arbitrary IsAlgClosure, rather than restricting to the particular constructed closure.
- Mathlib.NumberTheory.Padics.PadicNumbers: Padic, the completion by the padic norm.
- Sheaf.Topology.ContinuousMapCondensedRing: continuousMapRingSheafOfUniverse and
  continuousMapRingObjOfUniverse, with their canonical MonObj and commutativity interfaces.
  Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse and ContinuousCoefficientCommRing
  supply the definitionally identical common-universe presentation and its instance.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: coefficientRing,
  coefficientRing_X, condensedRingObj, and isCommMonObj_condensedRingObj.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and Scheme.ProEt.topology.
- Mathlib.CategoryTheory.Monoidal.Mod: Mod, ModObj and action-compatible morphisms.
- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Sheaf.Paper.CoefficientHeartStratificationDefs: IsLisseCoefficientModule;
  WeilConjectures.CategoryTheory.ModuleObjects.Free: Mod.IsFree and Mod.finiteFree.
- Sheaf.Paper.CondensedConstantConstructibility: HasFiniteConstantLocalModel (the full
  finite-presentation-on-the-point definition and its source docstring).
- Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian; Mathlib.Topology.Defs.Filter:
  CompactSpace. The latter imposes no separation condition.

Every recorded proof dependency with a module is imported, including
InternalAbelianSheafModuleEquivalence, TAdmissibleDualizableTruncations,
CondensedDualizableLocalPerfectModels, the upstream TStructure.Homology and Mathlib's
DerivedCategory.ShortExact. The Mathlib leaf proof dependencies are imported through
FreeModule.PID, Dimension.Free, RingTheory.Flat.Basic and AlgebraicGeometry.Noetherian
(which imports Topology.NoetherianSpace).

Edge cases checked before writing: the empty scheme satisfies the topological hypothesis;
empty locally closed subschemes are included; rank zero is Fin 0 in Mod.finiteFree;
ranks vary on cover members; zero maps between lisse modules have the expected lisse
kernel/cokernel; identity maps have zero kernel/cokernel; extensions quantify over
arbitrary middle terms and zero ends are allowed. There is no completeness assumption
on Ω, no finite-subextension-valued restriction, and no finite coefficient-field choice.
A common universe u is used for scheme carriers and Ω, with site objects in u+1,
morphisms in u and abelian coefficients in u+1 as in the recorded framework. Enlarging
the common universe accommodates independent initial sizes and imposes no mathematical
size equality on the original objects.

Searches actually run:

- msearch.py leanfinder: "Lisse sheaves for all continuous algebraic closure of Q_l
  coefficients are closed under kernels cokernels and extensions on a Noetherian scheme".
  Eight hits, on general abelian/Grothendieck categories of schemes and condensed modules;
  none states this local-model equivalence or closure result.
- msearch.py loogle: `"lisse", "kernel"`. Zero hits.
- msearch.py grep: `lisse|tAdmissible|t_admissible`. Four unrelated hits (height admissibility
  and separated-relation names), no match.
- rg on lean/WeilConjectures and lean/Sheaf for the node id: no match.
- rg on both source roots for lisse/kernel/cokernel combinations, followed by reading
  CoefficientHeartClosure and FieldCoefficient/Abelian: the former restricts coefficients
  to finite extensions or the finite-subextension-valued algebraic closure; the latter
  uses ordinary field-function sheaves and constant-rank/stratified closure statements.
  Neither states this node for pulled-back all-continuous internal coefficients.
- Read ContinuousQbarConstructibleGenerators: it proves a derived generation assertion
  for the right full continuous coefficients, not the ambient-heart closure assertion.
  Its coefficient presentation is reused here.

No statement correction or disputed statement was needed. The initial compile found
invalid field notation for closure classes on a bare function; these are now written
with fully qualified ObjectProperty names. The corrected module compiled cleanly through
scompile.py, both as a sandbox module and under its library module name.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
