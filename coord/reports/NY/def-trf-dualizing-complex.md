## Worker report

The module `Sheaf.Paper.TraceFormulaDualizingComplex` defines the dualizing complex,
the contravariant Verdier functor, its tensor--Hom bijection, and its evaluation.
This is definition-only work: every object and arrow is constructed; there are no
new theorems, axioms, or postponed proofs in this module. The earlier sandbox held
only a draft module, with no report or node record. Its monoidal evaluation and
ambient-only object assignment have been replaced with the recorded intrinsic
operations, the full finite-Tor source, and an actual contravariant functor.

Clause-by-clause correspondence:

- Global datum and coefficient conventions: `T : TraceFormulaCoefficientConventions`;
  `T.datum` is `FiniteFieldDatum`, including p, a, q, k₀ and k. `T.coefficients`
  stores the prime ℓ, its primality and `different : ℓ ≠ p`, and a fixed algebraic
  closure of Qℓ. `T.extension`, `T.coefficientField`, `T.level` and `T.level_pos`
  give precisely E and n ≥ 1; `T.coefficientRing` is the existing quotient A_{E,n}.
  No data is replaced by an unspecified coefficient ring. The extra X₀ stored in
  the recorded conventions is not used to constrain the arbitrary Y of this node.
- s = Spec k and the structure map: `Y : Over (Spec (CommRingCat.of T.datum.k))`,
  with `Y.left` and `Y.hom`. Every such Y is permitted, independently of T.X₀.
- Separated finite type: `[IsSeparated Y.hom]`, `[LocallyOfFiniteType Y.hom]`,
  `[QuasiCompact Y.hom]`. Finite type is the conjunction of the last two recorded
  Mathlib properties, not properness or smoothness.
- Exceptional admissibility: the definition uses the specified constructible
  exceptional construction, publicly reexported from the recorded dependency
  `FixedFiniteExceptionalAt`. `sfFiniteExceptional` is its existing intrinsic
  constant-ring presentation (the dependency explicitly retains that interface).
  `TraceExceptionalAdmissibility` identifies the relevant finite-Tor restriction.
  Availability is a theorem, as the node says, so neither an ambient FullCD datum
  nor a new adjoint/preservation assumption is added. The compactification needed
  to evaluate this specified functor is obtained by the existing
  `hasCompactification_of_finiteType_over_field`; it is not an input parameter.
- Ambient D(Y,A): `traceFormulaDerivedCategory T Y.left` abbreviates the recorded
  `proEtaleDerivedCategory Y.left T.coefficientRing`, with constant ring sheaf on
  the actual small pro-etale site. Object and morphism universes are u+1 and u;
  coefficients and module values use the existing u+1 lift. They are not forced
  to be the same universe as the site arrows.
- A_s: in the reused `integralDualizingFiniteTerm`, the input
  `(DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)` is the regular
  constant coefficient module on s concentrated in degree zero.
- ω_{Y,A}: `traceFormulaDualizingComplex` specializes the existing
  `integralDualizingFiniteTerm` at level T.level-1. This existing object applies
  `ProEtale.sfFiniteExceptional` to A_s: Rν_* followed by the ordinary etale
  exceptional adjoint and exact ν*, with the specified canonical realization
  equivalences. Thus even the dualizing object is reused, not defined again.
- D^b_ctf(Y,A): `traceFormulaFiniteTorCategory` abbreviates precisely
  `finiteTorConstructibleCategory ℓ E n hn Y`. The underlying predicate is the
  intersection of `intrinsicFiniteTorsionConstructible` (bounded, constructible
  cohomology) with `HasFiniteProEtaleTorAmplitude`; neither condition is dropped.
- RHom: `traceFormulaDerivedInternalHom` is the recorded
  `derivedInternalHomOfUniverses` over the constant A ring sheaf. It is exactly
  the intrinsic Hom used by `finiteIntrinsicDerivedInternalHom`, at n = (n-1)+1.
- D_Y: `traceFormulaVerdierDual` has type `(D^b_ctf(Y,A))ᵒᵖ ⥤ D(Y,A)`.
  It composes the opposite of the full inclusion with the curried Hom bifunctor
  flipped and evaluated at ω. Consequently an object is RHom(M,ω), and an arrow
  u : M → N acts as RHom(u,id_ω), in the required reverse direction. The codomain
  is ambient; no constructible-preservation or biduality theorem is asserted.
- Tensor--Hom adjunction: `traceFormulaClosed` is the existing
  `finiteIntrinsicClosed` at the same positive level, transported along the
  arithmetic equality. Its tensor is the recorded `finiteIntrinsicDerivedTensor`.
  `finiteIntrinsicTensorModels` characterizes its adjunction by ordinary K-flat
  evaluation, so this is the canonical external bijection from the cited currying
  and global-Hom comparisons, not an arbitrary Nonempty adjunction.
- Displayed bijection: `traceFormulaVerdierHomEquiv` is the recorded closed
  `transpose` at (D_Y M, M, ω). Its source and target are the two Hom sets in the
  node, in the same order, and no extra boundedness assumption is imposed on ω.
- Evaluation: `traceFormulaVerdierEvaluation T Y M` has source
  `(traceFormulaClosed T Y.left).tensor.obj (D_Y M, M.obj)` and target ω.
  Its body is literally `(traceFormulaVerdierHomEquiv T Y M).symm (𝟙 _)`.
  Thus it is the specified transpose of the identity, including its normalization.

Dependency declarations read and used:

- `Sheaf.Paper.TraceExceptionalAdmissibility`: `trfExceptional`,
  `TrfExceptionalStage`, `IsExceptionallyAdmissibleAt`, `IsExceptionallyAdmissible`;
  the specified constructible restriction is explained above, with no ambient datum.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions`, `coefficientField`, `coefficientRing`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicClosed`,
  `finiteIntrinsicDerivedInternalHom`, `finiteIntrinsicDerivedTensor`,
  `finiteIntrinsicTensorModels`, `finiteIntrinsicTranspose`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt` and
  its reexported intrinsic presentation `ProEtale.sfFiniteExceptional` from
  `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`.
- `Sheaf.SixFunctors.FiniteDualizing`: `integralDualizingFiniteTerm`, the existing
  intrinsic finite-level dualizing object; its formula and full signature were read.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`,
  `finiteTorConstructibleCategory`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`, through the finite-Tor predicate.
- Mathlib `AlgebraicGeometry.Morphisms.Proper`, `Morphisms.FiniteType`, and
  `Sites.Proetale`: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`:
  `SignedRingedHom.normalizedAdjunction_existsUnique`, the representative-normalized
  tensor--Hom interface; the intrinsic independent-universe finite calculus is used
  for the actual site sizes.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`:
  `rhom_global_sectionsOfUniverses`, the natural global-Hom identification.

Edge cases checked against the definitions: n=1 gives index n-1=0 and quotient
exponent 1; n=0 is excluded by exactly the source's n≥1. Zero objects and zero
maps are allowed in the full source, and evaluation is still the closed transpose
of its identity. Y empty, Y=s, nonproper separated Y, singular Y, non-smooth Y and
non-geometrically-descended Y are not excluded. The coefficient ring at n>1 need
not be a field; the finite-Tor condition remains a separate domain condition.
No smoothness, projectivity, nonemptiness, dimension or ambient adjoint datum occurs.

Searches (2026-10-18):

- `msearch.py leansearch`, query “Dualizing complex of a scheme is exceptional
  inverse image of the constant coefficient sheaf and Verdier duality is internal
  Hom into it”: eight unrelated Picard/linear-dual/opposite-complex hits; no match.
- `msearch.py leanfinder`, query “Dualizing complex exceptional inverse image
  coefficient unit Verdier dual contravariant functor derived internal Hom and
  evaluation”: eight general derived-category/exact-functor hits; no match.
- `msearch.py loogle`, query `CategoryTheory.ihom.ev`: twelve generic closed
  evaluation/currying hits. These do not supply this finite constructible
  exceptional construction or its intrinsic Hom and tensor normalization.
- `msearch.py grep`, query `dualizingComplex|verdierDual|Verdier dual|dualizing complex`:
  zero Mathlib hits.
- `rg` in the source library and `lean/Sheaf` for dualizing/Verdier names found
  `ProEtale.Derived.Duality`, `SixFunctors.FiniteDualizing`, and related finite-etale
  and relative coherent dualizing constructions. The upstream `dualizingComplex`
  and `verdierDual` require `HasBoundedBelowUpperShriek` and use fixed-scalar Hom;
  they do not give this intrinsic finite-Tor contravariant functor and normalized
  evaluation. `integralDualizingFiniteTerm` already supplies the positive-level
  intrinsic dualizing object: the final module reuses it directly, specializing
  its index n-1 to the coefficient conventions. The missing functor and normalized
  evaluation are supplied on top of that existing object.
- `rg def-trf-dualizing-complex` in the source library: no exact attachment.
- `rg` of every newly introduced full-name stem in `dag/lean_names_upstream.json`,
  the source library and `lean/Sheaf`: no declaration-name collision.

No statement correction, new DAG node, dependency rebind, or disputed statement.
The module helpers are the owning node's aliases, adjunction and Hom bijection,
recorded together in `lean.declarations`, not separate mathematical notions.

## Second reading by NY

No second reading by a worker: the dispatcher expressly requires direct worker
delivery without starting agents. The maintainer's independent delivery review
is the independent reading. The resumed worker has reread the node and module
against the clause correspondence above, including the finite-Tor source,
contravariant morphism action and identity-transpose evaluation. No mathematical
change to the node is required.
