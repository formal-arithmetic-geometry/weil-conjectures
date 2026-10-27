## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoheratorDistinguishedSquareTriangle`
states `AlgebraicGeometry.AlgebraicSpace.exists_coherator_distinguishedSquare_triangle`.
Its only declaration is a theorem with the whole proof `by sorry`. No definitions,
new nodes, dependency repairs, or statement corrections are needed. Only the item's
`lean` field changes.

Source checked: `literature/stacks-project/spaces-perfect.tex`,
`remark-explain-consequence` (Tag 0CR6), lines 4552–4567, together with the preceding
`lemma-pushforward-better-coherator` (0CR5). The source applies the exact coherator to
the unbounded Mayer–Vietoris triangle and commutes it past the three direct images.
The DAG's more explicit assumptions on the fourth vertex agree with this construction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fixed universes are the explicitly declared `u w`. `S : Scheme.{u}` is arbitrary;
  no condition on the base is imposed. Each of `W U V T : AlgebraicSpace S` uses
  the existing algebraic-space category, not a scheme presentation.
- `j : U ⟶ W`, `p : V ⟶ W`, `a : T ⟶ U`, `b : T ⟶ V` with
  `hsq : IsPullback a b j p` express the fourth vertex as the fibre product.
  Thus `a ≫ j` is the map denoted `j_T`; the other composite equals it by `hsq.w`.
- `hj` identifies the underlying presheaf of U with an existing `OpenSubspace W`,
  and identifies its inclusion with `j.hom.hom`. This is exactly the open-immersion
  condition used by `qcqs_etale_distinguishedSquare_induction`.
- `hp : IsEtale p.hom.hom` includes representability, by the recorded definition
  of `IsEtale`; it does not require V affine or p surjective.
- `Z : ClosedSubspace W`, `hZ : IsReduced ...`, and `hZsupport` state that Z is
  the reduced closed complement of U. `hcomplement` says that the actual sheaf
  fibre-product projection `pullback.snd p.hom Z.val.arrow.hom` is an isomorphism.
  These are the same reduced-complement conventions as the induction dependency.
- `hqcqs` applies exactly to A = W, U, V, T. Its first conjunct provides a scheme
  `B : Over S` with `CompactSpace B.left` and an étale surjective atlas q. Its
  second conjunct is the existing `IsAbsolutelyQuasiSeparated A`, whose affine-test
  definition is quasi-compactness of the absolute diagonal (also over a non-qsep S).
  The equality disjunction introduces no condition on any fifth algebraic space.
- Four `HasDerivedCategory.{w} A.SmallModules` instances select the prescribed
  localization sizes. `SmallModules` uses the original coefficient universe u on
  the equivalent small ringed model, without a coefficient lift or universe equality.
- `DQW`, `DQU`, `DQV`, `DQT` have codomain `A.DerivedQCoh`, the existing full
  subcategory of the ambient `A.DerivedModules` with quasi-coherent cohomology.
  `adjW`, `adjU`, `adjV`, `adjT` specify exactly that these are right adjoints of
  `A.derivedQCohProperty.ι`. These binders express the node's “let DQ be the right
  adjoints”; they do not assume extra geometric data or triangulatedness.
- Every DQ is followed by the actual full inclusion `A.derivedQCohProperty.ι`.
  The first vertex is therefore `(DQW ⋙ W.derivedQCohProperty.ι).obj E`.
- For j_U, j_V, j_T the composites
  `spaceDerivedPullback j_A ⋙ DQA ⋙ A.derivedQCohProperty.ι ⋙ derivedDirectImage j_A`
  are exactly `Rj_A,* DQ_A(E_A)` in the ambient category. The existing canonical
  `spaceDerivedPullback` is the total derived tensor pullback; these three maps
  are étale (open immersion, p, and their pullback/composite). Hence the recorded
  `spaceEtaleDerivedRestriction_existsUnique` identifies it canonically with exact
  étale restriction. No arbitrary replacement pullback is introduced.
- `derivedDirectImage` is the existing right derived functor of the chart-limit
  module direct image, conjugated through the existing small-module equivalences;
  its definition uses `rightDerivedFunctor` and K-injective resolutions.
- `αU`, `αV` are natural transformations with common source DQ_W followed by its
  inclusion and the two displayed summands as targets. `biprod.lift` gives the
  first triangle map. `βU`, `βV` are natural transformations from those summands
  to the third vertex; `biprod.desc` gives the second triangle map, with its signed
  components included in these transformations. The node asserts existence of
  the triangle and does not prescribe separate formulas for these components.
- `δ` is a natural transformation from the third functor to
  `DQW ⋙ W.derivedQCohProperty.ι ⋙ shiftFunctor W.DerivedModules (1 : ℤ)`,
  so its component has the required target `(DQ_W E)[1]`.
- The existential quantification over these five natural transformations precedes
  `∀ E : W.DerivedModules`. Thus the same arrows work naturally for every E;
  this is stronger than merely choosing triangles separately for each E and is
  precisely the stated naturality. `Triangle.mk ... ∈ distTriang W.DerivedModules`
  is distinguishedness in the ambient unbounded derived category. E has no
  boundedness, perfectness, or quasi-coherent-cohomology assumption.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `Modules`, its small étale site and its structure sheaf.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallModuleRestriction`, `smallModuleEquivalence` (the actual restriction).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and its inherited triangulation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh` and Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction`:
  `exists_derivedCoheratorAdjunction`, with its exact canonical adjoint shifts.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` is the resolving class used by direct image.
- `Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction`:
  `qcqs_etale_distinguishedSquare_induction`; its exact open/complement/pullback
  interface is reused. The induction theorem itself is not assumed as a hypothesis.
- `Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`:
  `spaceEtaleDerivedRestriction`, `spaceEtaleDerivedRestriction_existsUnique`,
  `space_derived_etale_chart_calculus`, `spaceDerivedChartDirectImageId`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback` and its unit.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `Pretriangulated`, `Pretriangulated.Triangle.mk`, `distinguishedTriangles`;
  `Triangulated.Triangulated` supplies `IsTriangulated`.
- Existing definitions visible through those public imports are
  `AlgebraicSpace.DerivedModules`, `derivedQCohProperty`, `DerivedQCoh`,
  `derivedDirectImage` in `AlgebraicSpaceDerivedModules`; `spaceDerivedPullback`
  in `SpaceDerivedPullback`; `OpenSubspace`, `ClosedSubspace`, `IsReduced`,
  `pointImage`, and `IsAbsolutelyQuasiSeparated` from the recorded induction
  dependencies. No private versions of these notions were introduced.
- Proof-only imports: `AlgebraicSpaceFiniteAffineSubatlas` for
  `compactSpace_points_of_scheme_atlas`, and Mathlib `Adjunction.Unique` for
  `Adjunction.rightAdjointUniq` and its counit equation.
- The proof dependencies `lem-sfb-space-qcqs-permanence`,
  `lem-sfb-space-relative-mv-exchange-triangles`, and
  `lem-sfb-space-derived-pushforward-coproducts` currently have no Lean record,
  Mathlib match or upstream audit declaration. Their imports are therefore omitted;
  their entire intended use remains in the theorem's step-by-step proof docstring.
  They are only proof dependencies: nothing in this statement needs a missing notion.

Edge cases checked against the source and signature: U empty (then the distinguished
condition makes V isomorphic over all W), U = W (empty complement), V or T empty,
W empty, E = 0, unbounded E with non-quasi-coherent cohomology, and a non-qsep base S.
None is excluded by a nonempty, affine, bounded, finite-type, or relative-separatedness
hypothesis. T may be any chosen pullback object, not only a particular limit encoding.
The four DQ choices are arbitrary adjoints, as the source permits by adjoint uniqueness.
All variables and universes are explicitly bound. No statement dispute found.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder "natural distinguished triangle for derived quasi
  coherator on elementary distinguished squares of algebraic spaces"`: eight hits,
  including `DerivedCategory.mem_distTriang_iff` and
  `DerivedCategory.triangleOfSES_distinguished`; none states the coherator result.
- `msearch.py ... leansearch "Derived coherator natural Mayer Vietoris triangle on
  algebraic spaces"`: eight hits, general `MayerVietorisSquare` and
  `Opens.mayerVietorisSquare`, not a derived coherator statement.
- `msearch.py ... loogle "CategoryTheory.Triangle.mk, CategoryTheory.NatTrans,
  CategoryTheory.Limits.biprod"`: no hits; unknown `CategoryTheory.Triangle.mk`.
  Reading the source resolved its correct namespace `Pretriangulated.Triangle.mk`.
- `msearch.py ... grep "coherator|Coherator|MayerVietoris" CategoryTheory`:
  ten ordinary site/sheaf-cohomology Mayer–Vietoris hits, no coherator statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for coherator/Coherator and
  distinguished-square triangles: scheme coherators and the space adjunction exist,
  but no space coherator distinguished-square triangle. `grep -rn` for the item id
  in `lean/WeilConjectures` gave no match.
- `rg` for `exists_coherator_distinguishedSquare_triangle` over both source roots,
  Mathlib, and `dag/lean_names_upstream.json`: no existing declaration.
- The latest blueprint was searched for coherator references; this is an inherited
  Stacks prerequisite, not the blueprint unit's own statement. The Stacks source is
  present locally and was read directly.

Validation: `scompile.py Q111 lem-sfb-space-coherator-distinguished-square-triangle
<module file>` compiled both `Sheaf.Stage2.Sandbox0` and the eventual library module
cleanly (2.5 seconds each), with no errors or warnings. Only the prescribed wrapper
was used, and no shared source or compiled library was written directly.

## Second reading by Q111

Author's second reading before the maintainer's independent review: reopened the node
and the complete Lean signature and checked every binder and vertex. In particular,
`hqcqs` uses the required compact scheme atlas, not just compact point spaces, and
absolute quasi-separatedness rather than separatedness relative to S. The complement
is reduced and its actual pullback projection is invertible. `hsq` ties the displayed
T to U times_W V. The four adjunction binders constrain the DQ functors to the full
quasi-coherent subcategories. All DQ values are included back into the ambient
categories before direct image. Exact étale restriction is the canonically equivalent
existing derived pullback, justified by the recorded chart calculus. The three natural
arrows are encoded by five natural transformations, including the boundary into the
shifted first functor. Distinguishedness is imposed for every E and no hypothesis on E
has appeared. No mismatch or statement change was found. This is a self-check, not a
claim of an independent second agent; the dispatcher explicitly forbids spawning agents.
