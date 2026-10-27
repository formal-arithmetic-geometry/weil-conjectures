## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectTensorTestsUpperBound` states
`AlgebraicGeometry.AlgebraicSpace.boundedAbove_of_perfect_tensor_tests` with a
single `sorry` proof. The source read is `literature/stacks-project/spaces-perfect.tex`,
Tag 0GFH, `proposition-detecting-bounded-above`, especially (7)(b), (1), and its
full distinguished-square proof (lines 7082–7214). No mathematical statement is
corrected and no new definition or dependency repair is needed.

Hypothesis and clause correspondence:

- The size convention is explicit `universe u w`. The scheme/coefficient universe
  is `u`, while `HasDerivedCategory.{w} X.SmallModules` leaves the derived Hom
  localization universe independent. The existing affine small model has both
  object and morphism universe `u`; the original etale site is not forced to
  have equal object and morphism universes.
- A commutative ring is `(A : Type u) [CommRing A]`, with no nontriviality,
  field, Noetherian or characteristic assumption. Its spectrum is `Spec (.of A)`.
- An algebraic space over that spectrum is
  `X : AlgebraicSpace (Spec (.of A))`. The recorded structure sheaf is the actual
  regular-functions sheaf restricted to `X.SmallEtaleModel`.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)`, meaning the finite
  subcover property for the existing algebraic-space point topology.
- Absolute quasi-separatedness is `hqs : X.IsAbsolutelyQuasiSeparated`.
  Read `AlgebraicSpaceAbsoluteQuasiSeparated.lean`: this is the affine-test
  criterion of Tag 0AHR, equivalent to quasi-compactness of the absolute diagonal.
- `K : X.DerivedQCoh` means the full subcategory of the unbounded derived module
  category with quasi-coherent cohomology, rather than the derived category of
  the abelian category QCoh. Its defining property transports each cohomology
  object back by `X.smallModuleEquivalence.inverse` and applies the dependency's
  Mathlib `SheafOfModules.IsQuasicoherent` predicate.
- Every perfect test is `∀ P : X.DerivedModules` followed by
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf P`. Tests range over the ambient derived category.
  Read the full predicate in `StrictPerfectCoefficientPackageOfUniverses.lean`:
  a representative is locally quasi-isomorphic to bounded complexes of
  degreewise retracts of finite free structure modules. Bounds and ranks may
  vary on the cover; no global strict-perfect representative is assumed.
- `X.derivedDualityModel.closed.tensor.obj (P, K.obj)` is precisely the recorded
  normalized K-flat derived tensor. Its model contains the K-flat total-tensor
  comparison, not an arbitrary operation or a new tensor definition.
- `IsZero ((ringedSiteZerothHypercohomologyOfUniverses ...).obj (T⟦i⟧))`
  renders `H^i(RΓ(X,T)) = 0`: H⁰ RΓ(T[i]) equals H^i RΓ(T) with Mathlib's
  cochain shift convention. The recorded zeroth hypercohomology functor is the
  K-injective right derived Hom(O,-) followed by zeroth cohomology, with values
  in `AddCommGrpCat`. This is `IsZero` of an abelian-group object, not `IsZero`
  of a bare carrier type.
- `∃ bP : ℤ, ∀ i : ℤ, bP < i → ...` occurs inside the quantifier over each
  perfect P. It is exactly the individual bound, without a uniform bound on tests.
- The conclusion `∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
  ((DerivedCategory.homologyFunctor X.SmallModules i).obj K.obj)` renders the
  required vanishing of cohomology sheaves above b. Exact equivalence of module
  categories reflects zero objects, so this is the same vanishing on X_et.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category
  of morphisms; spectrum is the standard `Spec` of the bundled commutative ring.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `structureSheaf`, `Modules` and their regular-functions definitions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the public abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; cohomology is the existing
  `DerivedCategory.homologyFunctor` (HomologySequence.lean).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`; the predicate is unchanged Mathlib
  `SheafOfModules.IsQuasicoherent` (Quasicoherent.lean, line 251).
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its local finite-free
  retract packages, from the recorded strict-perfect dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `DerivedModules`, `DerivedQCoh`, `derivedQCohProperty`, `derivedDualityModel`.
  Its `SmallModules` and actual regular-functions `smallStructureSheaf` come
  from `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`, whose precise
  restriction equivalence and definitions were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.

The two existing definition nodes `def-sfb-space-derived-module-calculus` and
`def-sfb-space-absolute-quasi-separated` are added to `stmt_deps` to name the
already landed interfaces used above, as permitted by brief-stage2 §5
(STMT_DEPS MAY GAIN LANDED NODES). They are not new nodes and their records are
unchanged. Every original statement dependency module is imported publicly.
The size-convention dependency is metatheoretic and has no module.

Already stated proof dependencies are imported privately:
`Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization`
(`Scheme.Modules.exists_affineEtaleDerivedModuleRealization`),
`Sheaf.Algebra.Homology.RingedSiteGlobalHomDirectImage`
(`RingedSiteGlobalHomDirectImage.globalHomDirectImage`),
`Sheaf.CategoryTheory.RingedSitePerfectDuality` (`ringedSitePerfectDuality`),
`Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus`
(`AlgebraicSpace.space_derived_etale_chart_calculus`), and
`Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction`
(`AlgebraicSpace.qcqs_etale_distinguishedSquare_induction`). The other eight
proof dependency nodes have no Lean records; none is needed to type the statement.
The docstring carries all six DAG proof steps, including their named dependencies,
the per-test Ext-window truncation argument, open-retract transfer, and final bound.

Edge cases checked before writing: the zero ring and empty algebraic space are
allowed and yield only zero sheaves; no nonempty or nontrivial instance is assumed.
For K=0, any integer bound works. The zero perfect test is included and places no
extra requirement. All integer shifts and negative thresholds are included.
K may have arbitrarily low nonzero cohomology. Perfect objects need only local
bounded finite-projective models. There is no uniformity assumption on bP and
no generator, chosen atlas, or common perfect-amplitude hypothesis is added.
No counterexample or statement dispute was found.

Searches actually run with `msearch.py Q03 lem-sfb-space-perfect-tensor-tests-upper-bound`:

- `leanfinder`: "On a quasi compact quasi separated algebraic space perfect derived
  tensor global sections detect bounded above quasi coherent complexes" returned
  eight ordinary scheme/quasi-separated/global-section results, no matching criterion.
- `loogle`: "DerivedCategory.IsLE, SheafOfModules" returned zero hits.
- `leansearch`: "Perfect tensor global section tests detect bounded above complexes
  on algebraic spaces" returned eight ordinary global-section, derived-support and
  small-Ext results; none states the algebraic-space tensor-test implication.
- `grep`: "perfect.*(test|bound)|tensor.*tests" in Mathlib/AlgebraicGeometry
  returned zero hits.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, for perfect/test/bound and tensor/tests found
  related scheme perfectness and scalar-test results, not this statement.
  Exact item-id and proposed declaration/module searches found no duplicate.
  The already landed small ringed model, derived modules and absolute
  quasi-separatedness definitions were found and reused instead of copied.

Validation: `scompile.py Q03 lem-sfb-space-perfect-tensor-tests-upper-bound
<module>` compiled both sandbox and library forms cleanly (6.8 s and 7.4 s),
with no errors or unexpected warnings. All declarations and universes are explicit;
`set_option autoImplicit false` enforces this. Every proof remains `sorry`.

## Second reading by Q03

A separate second pass was made by this same dispatcher-started worker; no other
agent was started, as explicitly required by the assignment. This is not a claim
of an independent agent review; the maintainer supplies that review.

Reread the node and source against the final signature. A is arbitrary commutative;
X is over Spec A; `CompactSpace` is on the point space; the quasi-separated
predicate is absolute; K is in the full cohomologically quasi-coherent category;
P ranges over all ambient derived objects with the exact local perfect predicate.
The tensor factors are P then K. H⁰ RΓ after shift by i has the correct positive
cohomological sign. The existential bP is after P, and the conclusion has only one
existential bound for the cohomology sheaves of K. The independent w is retained.
There are no added finite-presentation, separated, Noetherian or lower-bound
hypotheses. The equivalent small model retains the original coefficient universe.
The two additional stmt_deps record existing notions rather than alter the source.
No mismatch was found and no signature change was needed after compilation.
