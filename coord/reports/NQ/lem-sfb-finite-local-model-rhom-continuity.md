## Worker report

The module `Sheaf.Paper.FiniteLocalModelRHomContinuity` states
`AlgebraicGeometry.ProEtale.finite_local_model_rhom_continuity`, with one postponed
proof (`sorry`). It introduces no definitions, copies no existing notion, and leaves
the natural-language statement unchanged. The docstring supplies all nine DAG proof
steps, including the actual finite-sum Hom model, cocone normalization, and descent.

Hypothesis and clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The existing coefficient constructions use
  `Padic.coefficientExtensionAbsoluteValue`, hence the extension topology.
- The two permitted coefficient rings are the disjunction `_hΛ`, identifying the
  bundled ring `Λ : Profinite.CondensedRing` with `Mon.mk` of either
  `FiniteConstantModel.integralCoefficients l E` or
  `FiniteConstantModel.rationalCoefficients l E`. The former uses
  `Padic.coefficientExtensionIntegers l E`. `IsCommMonObj Λ.X` records their
  commutative structure, rather than an arbitrary extra coefficient condition.
- Any scheme T is `(T : Scheme.{u})`, with no Noetherian, separated, qcqs,
  characteristic, or invertibility assumption.
- B_T is exactly `condensedRingObj Λ.X T`, the underlying ring of
  `coefficientRing T Λ = (upperStarFromPoint T).mapMon.obj Λ`.
- The module L is an object of `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1})
  (condensedRingObj Λ.X T)`. `_hL : HasFiniteConstantLocalModel Λ.X T L`
  uses the recorded predicate: a pro-etale cover and a finite presentation on the
  point pulled back on each chart. Finite presentations on the point are finite
  scalar matrices, giving exactly B_W tensor over constant A with constant P.
  Arbitrary local coefficient-function matrices are not substituted for this notion.
- `DerivedCategory` is the ordinary unbounded localization; L[0] is
  `(DerivedCategory.singleFunctor _ 0).obj L`.
- The site is the recorded `Scheme.ProEt`; its object universe is u+1 and its
  morphism universe is u. Values are `Ab.{u+1}` and diagrams have
  `(I : Type (u+1)) [SmallCategory I] [IsFiltered I]`, in the fixed module universe.
  Filteredness includes nonemptiness. No site universes are equated.
- The diagram is `N : I ⥤ CochainComplex (...) ℤ`. Its bound is
  `∀ i, (DerivedCategory.Q.obj (N.obj i)).IsGE c`, which by
  `DerivedCategory.isGE_iff` is exactly H^r(N_i)=0 for every r<c.
  It does not impose termwise vanishing on the input representatives.
- The original termwise sheaf-colimit cocone is `colimit.cocone N`.
  The functor applied to it is `DerivedCategory.Q ⋙
  (CondensedRing.derivedHom Λ.X T).obj (op L[0]) ⋙
  DerivedCategory.homologyFunctor _ n`. Thus each leg is H^n of actual derived-Hom
  postcomposition with the original cocone leg. These are the evaluation-transpose
  maps of the given closed structure; there is no arbitrary comparison-map binder.
- Continuity is `∀ n, Nonempty (IsColimit (...mapCocone (colimit.cocone N)))`.
  This is an equivalent cohomology-sheaf formulation of the requested isomorphism:
  for any functorial complex model F of RHom(L[0],-), exact filtered sheaf colimits
  give H^n(colim F(N_i)) = colim H^n(F(N_i)). The image cocone is colimiting iff
  the canonical map from that colimit to H^n(F(colim N)) is invertible.
  `DerivedCategory.isIso_iff` then identifies the assertion in every n with
  invertibility of the original derived comparison. This formulation retains its
  cocone legs and is independent of the functorial model by quasi-isomorphism
  invariance and exact filtered colimits. It does not assert existence of arbitrary
  categorical filtered colimits in the derived category.
- The second conjunct quantifies over every `N : DerivedCategory (...)` and says
  `N.IsGE c → (RHom(L[0],N)).IsGE c`. It is independent of the filtered diagram
  and applies to derived objects, not just the particular complex representatives.
- No torsion-freeness hypothesis is present on the scalar modules.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, with the
  public continuous-coefficient constructors. Its imported sectionwise construction
  has continuous-function sections and precomposition restriction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and
  `upperStarFromPoint`. Their full definitions implement the pulled-back ring.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, for the
  dependency's total-derived convention. The actual category used is Mathlib's
  `DerivedCategory`, as the convention record specifies.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`, read with its full
  cover/presentation/pullback definition and docstring. The stronger constructible
  stratification predicate is not imposed here.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom`, defined as the closed
  structure's `MonoidalClosed.internalHom`, and `derivedTensorHomAdjunction`.
- Mathlib `AlgebraicGeometry.Scheme` / `Scheme.Hom`,
  `Scheme.ProEt` / `ProEt.topology`, `CochainComplex`, `Cocone`, `IsColimit`,
  `colimit.cocone`, `IsFiltered`, `DerivedCategory.Q`,
  `DerivedCategory.singleFunctor`, `DerivedCategory.homologyFunctor`,
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsGE` and `isGE_iff`.
- `def-weil-size-convention` is a metatheoretic convention; its record has no Lean
  declaration. The explicit universes above implement it.
- `Sheaf.Paper.FiniteConstantModelResolution`:
  `AlgebraicGeometry.ProEtale.FiniteConstantModel.integralCoefficients` and
  `rationalCoefficients`. Their owning definition node is the existing
  `def-sfb-finite-constant-model-data` (`existing: true`, same module), which is
  added to `stmt_deps`. These are plain abbreviations, independent of the
  resolution theorem. `lem-sfb-finite-constant-model-two-term-free-resolution`
  remains in `proof_deps` for step 4. Nothing else in the node changes except
  `lean` and this added definition dependency.

All stated proof-dependency modules are imported without `public`, except the
resolution module also used in the statement. The mathematical proof remains entirely
postponed. Sources read include the node's proof, the current blueprint's
`sk-def-sfb-constructible/_section.md`, Stacks sites-cohomology's
`lemma-Rhom-strictly-perfect` (08JH),
`lemma-Rhom-complex-of-direct-summands-finite-free` (08JI), and
`lemma-restriction-RHom-to-U` (08JB). The explicit length-one resolution is the
already recorded node, not a newly assumed resolution or flatness assertion.

Edge cases checked before writing:

- Empty schemes and L=0 are admitted. Finite free ranks may be zero; the covering
  predicate accommodates the empty scheme. All assertions then hold in the zero
  module category.
- Integral torsion P=A/(pi) is allowed. Its two-term resolution in degrees -1,0
  puts Ext^1 in degree +1; the lower bound is c, not c-1. The Hom model has terms
  (C^n)^b plus (C^(n-1))^a, confirming the sign of the degree shift.
- For A=E take a=0. The field and integral cases both include the zero module.
- Any integer c is allowed, including negative c and c=0.
- A filtered index category cannot be empty, by `IsFiltered`; the terminal index
  category gives the identity comparison, as expected.
- Cohomologically bounded-below complexes may have nonzero acyclic tails below c.
  The input uses `IsGE` and admits those complexes unchanged.
- T can be non-Noetherian and can have characteristic ell; neither restriction
  is present in the coefficient/local-resolution setting or in the signature.

Searches actually run:

- `msearch.py ... leanfinder`: "Derived internal Hom from a module sheaf with
  finite constant local models commutes with filtered colimits of uniformly
  bounded below complexes". Eight hits, including light-condensed closedness,
  locally constant module functors, `CondensedMod.ofSheafCompHaus` and `Sheaf.H`;
  none states the continuity theorem with its lower bound.
- `msearch.py ... loogle`: `"derivedHom", "colimit"`: zero hits.
- `msearch.py ... grep`:
  `(derivedHom|internalHom).*(colimit|filtered)|(colimit|filtered).*(derivedHom|internalHom)`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: "Derived internal Hom locally finite constant module
  filtered colimits bounded below complexes". Eight hits: ordinary filtered module
  colimits, homological-complex filtered-colimit infrastructure and presentability;
  no matching derived internal-Hom assertion.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for derivedHom/RHom/internalHom
  with colimit/continuity found the parent `ConstructibleInternalHomContinuity`
  (Noetherian T, constructible source, termwise target bound), older ringed-site
  continuity, and external/global Hom continuity. None matches this node with its
  arbitrary T, finite constant local model, cohomological input bound, and sharp
  lower-bound conclusion. The parent was read in full; its cocone-on-cohomology
  formulation is reused, without redeclaring its theorem.
- `rg` for the exact item id in `lean/WeilConjectures`: no hits. The proposed
  declaration name does not occur in Mathlib, `WeilConjectures`, or `Sheaf`.
- `dag/lean_names_upstream.json` was searched for finite local-model names;
  the listed canonical transport/comparison declarations are different notions.

Validation: `scompile.py NQ lem-sfb-finite-local-model-rhom-continuity` compiled
this file cleanly in sandbox and library modes (9.1 s and 8.6 s), with no errors
or warnings. No local/global build was run. All variables and the universe are
explicitly bound, with `autoImplicit false` in the module. No statement dispute,
statement correction, new definition node, or dependency repair is needed.

## Returned delivery repair

The independent review of immutable head `87d1ccfe9637` upheld H2: the added
statement dependency named the resolution theorem, while the signature uses only
its module's coefficient abbreviations. Replaced that added dependency with
`def-sfb-finite-constant-model-data`, whose existing Lean record owns both
`FiniteConstantModel.integralCoefficients` and `rationalCoefficients` in
`Sheaf.Paper.FiniteConstantModelResolution`. The resolution theorem remains in
`proof_deps`; no Lean code, theorem signature, mathematical statement, proof steps,
or other node fields changed. The declaration docstrings and their complete
abbreviation bodies were re-read: each constructs the continuous coefficient ring
using the specified extension absolute value, without choosing resolution data.

Self-check: compared the retained packet with the current shared node and checked
that the only non-`lean` change is adding the owning definition node to
`stmt_deps`. Verified the recorded signature against the Lean source, every
explicit binder and universe, the unchanged `sorry` proof, and the unchanged
resolution proof dependency. The initial saved-packet dry run passed before this
metadata repair. After the repair, `scompile.py` compiled the delivered module
cleanly in sandbox mode (9.1 s) and library mode (8.6 s), with no diagnostics.
The repaired delivery also undergoes the required `deliver2.py --no-push` check
before pushing.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
