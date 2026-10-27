## Worker report

The module `Sheaf.Paper.NormScalarTestAssembly` states
`AlgebraicGeometry.ProEtale.norm_scalar_test_assembly`, with its whole proof `sorry`.
All ten accompanying helpers have real definitions. They package the coefficient sheaf,
actual section restriction, its total right derived transformation, the principal-open
test, the canonical H^0 identification, and the three clauses of the conclusion. There
are no new independent notions, new DAG nodes, or dependency repairs. The item node
changes only in `lean`; its mathematical statement and all graph fields are unchanged.

The preserved sandbox contained only dispatcher brief markers. Q144's existing report
and ledger entry are a stage-1 split, with no `lean` or `reviewed_lean` record on the item.
They are not an existing stage-2 statement. The previous blocked explanation confused
the stages; this delivery supplies the missing stage-2 work.

### Every hypothesis and clause

- Distinct primes p and ell: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)`.
- Characteristic-p field: `(k : Type u) [Field k] [CharP k p]`.
- Finite extension E of Q_ell with its extending norm:
  `[NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`.
  A normed algebra between normed fields makes the algebra map isometric.
- Algebraic closure Omega with extended norm:
  `[NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]`.
  There is no completeness instance on Omega, no colimit topology, and no finite-field
  descent condition on its continuous functions.
- Small directed poset with least element: `(I : Type u) [PartialOrder I] [OrderBot I]
  [IsDirected I (· ≤ ·)]`; the element called 0 in the node is `⊥`.
- Affine inverse system: `(R : I ⥤ CommRingCat.{u})`; stages are `Spec (R.obj i)`,
  with inverse transition `Spec.map (R.map (homOfLE h))`. Passing to coordinate rings
  is the affine anti-equivalence, not a restriction on the geometric inverse system.
- k-scheme structure and compatibility: the natural transformation
  `κ : (Functor.const I).obj (CommRingCat.of k) ⟶ R`.
- Regularity of each stage: `hregular : ∀ i, IsRegularScheme (Spec (R.obj i))`.
  The recorded definition includes local Noetherianity, not only regular stalks.
- Finite type over k: `hfiniteType` is the conjunction of `LocallyOfFiniteType` and
  `QuasiCompact` for `Spec.map (κ.app i)`, exactly the recorded finite-type convention.
- Finite locally free transitions: `hfiniteFlat` is `IsFinite ∧ Flat` on each inverse
  transition. This is equivalent here: every target stage is Noetherian (regular affine
  finite type over k), so a finite coordinate module is finitely presented; flat and
  finitely presented is locally finite free. Conversely locally finite free is finite
  and flat on an affine quasi-compact target. No finite-presentation hypothesis is added.
- Initial section and stagewise nonzerodivisors: `f₀ : R.obj ⊥` and
  `hregularElement`, using `nonZeroDivisors` on each `R.obj i` after the initial map.
- X is literally `Spec (colimit R)` with `[HasColimit R]`, the existence of this
  filtered coordinate-ring colimit. Its section f is literally
  `(Scheme.ΓSpecIso (colimit R)).inv ((colimit.ι R ⊥).hom f₀)`.
- Every affine weakly contractible pro-etale test: each of the two assumptions and
  the conclusion quantifies over `V : (Spec (colimit R)).ProEt`, `[IsAffine V.left]`,
  and the recorded `topology.IsWeaklyContractible.{u + 1} V`. The structural morphism
  is V.hom and is weakly etale by its site-object structure. No affineness of V -> X
  beyond the affine source is imposed.
- W and T: `normScalarPuncturedTest X f V` is the basic open of V at `V.hom.appTop f`,
  with its composed map to X. Thus it is the canonical base change V x_X X[1/f].
  `normScalarPuncturedInclusion` is the actual inclusion over X.
- The cyclic degree-zero assumption: `htorsion` is `Function.Bijective` on the
  actual presheaf restriction of the constant abelian sheaf of `ULift (ZMod ℓ)`.
  This is the constant Z/ell sheaf, not a continuous-function assumption substituted
  for it. Lifting changes only the value universe.
- Every complete nonarchimedean normed extension: `hcomplete` quantifies over
  `(B : Type u) [NormedField B] [NormedAlgebra ℚ_[ℓ] B] [CompleteSpace B]
  [IsUltrametricDist B]`. It asserts `IsIso` of the canonical derived restriction
  on `normScalarCoefficient X B`. B lives in the same sufficiently large universe as
  the scheme and fields; in particular the completion of Omega is available there.
- C_F and its pullback: `normScalarCoefficient X F` is exactly
  `(upperStarFromPoint X).obj (Profinite.continuousMapRingObjOfUniverse.{u, u} F)`,
  using the dependency's own recorded continuous-map sheaf construction and the
  point inverse-image functor used by `coefficientRing`. Ring structure is forgotten
  only because the statement concerns ordinary abelian sheaves.
- Actual derived restriction in D(Ab): `NormScalarTestResult` first asserts `IsIso`
  of `normScalarDerivedRestriction`. This helper derives `normScalarSectionRestriction`
  by `Functor.rightDerivedFunctorNatTrans` and evaluates it on the specified coefficient
  sheaf in degree zero. Source and target are objects of `DerivedCategory AddCommGrpCat`,
  not merely lists of isomorphic cohomology groups. The total right derived functors
  use K-injectives in the Grothendieck category of abelian sheaves.
- Degree-zero restriction of all continuous functions: the second clause gives a
  sheaf realization e into the actual existing continuous-function sheaf. Its adjoint
  on every profinite test is normalized by `g ↦ g.comp (profiniteTestProjection X S)`;
  this is the uniqueness characterization of the recorded realization theorem, so e
  cannot be an arbitrary unrelated isomorphism. The displayed square uses
  `normScalarH0SectionsIso`, constructed from the unbounded/classical derived comparison
  and `rightDerivedZeroIsoSelf`, and identifies the H^0 map with the continuous sheaf's
  restriction. By `continuousCoefficientRingPresheaf.map`, the latter is exactly
  precomposition by the underlying principal-open inclusion, on every continuous map.
- Positive cohomology on T vanishes: the last clause is `∀ q : ℤ, 0 < q → IsZero`
  of the q-th homology object of the actual T derived sections.
- Both fields: the final conjunction is `NormScalarTestResult ... E ∧
  NormScalarTestResult ... Ω` for every test V.
- Empty tests and identity opens are permitted by the basic-open and site definitions;
  no nonempty scheme, nonzero rank, or proper-open hypothesis is present.

### Dependencies and canonical constructions

Every statement dependency was opened, including its full recorded signature/docstring
or Mathlib match. The principal declarations used are:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse`, using its own continuous-map presheaf.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.upperStarFromPoint`, the underlying construction of
  recorded `coefficientRing` and `condensedRingObj`; its adjunction comparisons are also
  used in the canonical degree-zero normalization.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`:
  `AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf`, solely as the target of
  the normalized continuous-function realization, not a replacement coefficient.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`, `ProEt.mk`.
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`:
  `GrothendieckTopology.IsWeaklyContractible`, in the section-value universe u+1.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `singleFunctor`,
  `homologyFunctor`; `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`:
  `Functor.rightDerivedFunctorNatTrans`; its `PlusCompatibility` module supplies the
  canonical homology comparison used in the H^0 isomorphism.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from the recorded finite-type interface.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`;
  `Mathlib.NumberTheory.Padics.PadicNumbers`: `Padic`.
- The recorded `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses` module is
  imported for the proof/interface comparison. The item explicitly requires ordinary
  abelian sheaves, so its actual derived sections use abelian evaluation rather than
  changing the category to modules over C_F.

All already-stated proof-dependency modules are imported, including the clopen-component
criterion, continuous realization, exact weakly contractible evaluation, finite constant
representation, ring-sheaf Grothendieck input, site localization, and negative-vanishing
and plus-compatibility interfaces. Mathlib proof matches import field completion,
spectral norms, affine qcqs, and spectral spaces. The existing positive completion
cohomology injection node has no Lean declaration; it is retained in the seven-step
proof docstring as the future proof obligation, not assumed as an extra hypothesis.
The definition of every canonical map is real; no theorem with an unregistered sorry
has been added as a helper. There is precisely one postponed theorem, matching this item.

### Edge cases and fidelity

Checked empty V and consequently empty T: continuous function groups are the zero
abelian group and the component argument chooses no points. T empty with V nonempty
cannot satisfy the cyclic bijection, since 0 and 1 are distinct constant sections for
prime ell. Checked the identity open, including a unit f and the singleton index poset.
The zero coordinate ring/empty stages are not excluded: `nonZeroDivisors` has its usual
multiplicative-regular meaning. The zero section on a nonempty stage fails the specified
nonzerodivisor condition. Checked ell=2: idempotents of the cyclic field still detect
clopens. The poset is necessarily nonempty because it has a least element. No arbitrary
independent smaller test universe can make the coefficient assumptions vacuous. All
universe variables are explicitly bound, and both auto-implicit options are disabled.

The blueprint paragraph (3), Q67's preserved original steps 6--7, and Q144's seven-step
split were read. The source is agent-formulated as the node says; the completion injection
is not attributed to a paper that proves only a different coefficient topology. No
statement correction or STATEMENT-DISPUTED finding is introduced.

### Searches and reuse

The prescribed msearch.py calls were actually run (full query/result summaries also in
the sandbox's searches.jsonl):

- LeanFinder: `Derived restriction of all continuous norm valued coefficient sheaves for
  finite l adic extension and its algebraic closure from complete field restriction tests`.
  Eight hits, including BDeRhamPlus, spectralNorm.completeSpace and adic-completion
  declarations. No scalar sheaf restriction theorem. Digest fbac36b861fcdba0.
- Loogle: `"Sheaf", "Completion"`. Zero hits. Digest 4f53cda18c2baa0c.
- Mathlib grep: `(cohomology|Sheaf).*(Completion|clopen)|(Completion|clopen).*(cohomology|Sheaf)`.
  Two incidental cocompletion documentation hits in Limits/Presheaf.lean.
  Digest 45cb4427fd683402.
- LeanSearch: `Derived restriction of continuous norm topological algebraic closure
  coefficient sheaves from complete field scalar tests`. Eight scalar-restriction
  declarations for normed spaces/linear maps; no sheaf or derived-open scalar theorem.
  Digest aae5a7f22a234694.
- Source rg over `lean/WeilConjectures` and `lean/Sheaf` for the item id, norm scalar
  assembly names, coefficient restriction, and derived evaluation. No existing item
  statement; the parent `torsionAcyclic_normCoefficient_test` has a different hypothesis
  (all finite cyclic derived units) and a different lisse-module conclusion. Its real
  `normTestLimitSection` is rendered directly as the same expression here rather than
  importing a downstream theorem module and creating a future proof-import cycle.
- The existing coefficient, canonical realization, K-injective derived transformation,
  H^0 comparison and site-object constructors were read and reused. None is copied
  under a private name.

### Validation

The final module was checked using the prescribed scompile.py against the live published
server build, in both sandbox and library module forms, without errors or warnings.
Every definition is a composition of recorded constructions; the theorem is stated only.
Delivery preflight and per-file compilation are run by the prescribed deliver2.py wrapper.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
