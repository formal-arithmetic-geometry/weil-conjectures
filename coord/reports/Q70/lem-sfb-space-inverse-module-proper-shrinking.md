## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceInverseModuleProperShrinking` states
`AlgebraicGeometry.AlgebraicSpace.inverseModuleProperShrinking`, with proof `sorry`.
No definition, extra theorem, dependency repair, or statement correction is needed.
The six-step source proof is in its docstring, including the quasi-compact-neighbourhood
step and the point-set support comparison (not base change of annihilator ideals).

Clause-by-clause correspondence:

- Work over Spec Z and the size convention: `universe u`,
  `AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`. ULift places Z in the scheme universe;
  the canonical maps to it are `specULiftZIsTerminal.from (Spec R)`.
  No universe equality is added.
- Schemes and affine spectra: existing `Scheme`, `Spec`, `Spec.map`, as used in the
  inline spectrum construction. Algebraic spaces and module categories are the recorded
  `AlgebraicSpace` and `Modules`, using the existing small etale structure sheaf.
- The inverse sequence is `A : ℕ → CommRingCat.{u}`, with
  `r : ∀ n, A (n + 1) ⟶ A n`. Lean index n is paper level n+1.
  `hsurj` is surjectivity of every transition, and `hnil` says every element killed
  by a transition is nilpotent; there is no uniform nilpotence exponent assumption.
- The inverse-limit ring is `c.pt`, with `c : Cone (Functor.ofOpSequence r)` and
  `hc : IsLimit c`. This permits every limit model and specifies its projection maps.
- X over Spec A is `X` with `f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec c.pt)))`.
  `hsep : MapIsSeparated f` is the specified representable closed diagonal.
  `hfp : ProperQuotFinitePresentation f` is exactly locally finite presentation,
  quasi-compactness, and quasi-compactness of the diagonal.
- X_n is the actual sheaf fibre product `properQuotFibre f T_n`, where T_n denotes the inline costructured arrow below;
  its two maps are `properQuotFst` and `properQuotSnd`.
- X_0, the node's common underlying subset, is used as
  `pointImage (properQuotFst f T_0).hom.hom`.
  The equal underlying subsets of all levels follow from the nil kernels; they are
  explanatory notation, not an additional hypothesis or conclusion of this lemma.
- The open W in X is `W`, `j`, and `hopen`, requiring representability by scheme
  open immersions on all scheme tests. An open immersion identifies W with an open
  subspace of X, so this is the same notion without choosing a second subfunctor model.
  `hcontains` is exactly X_0 contained in the point image of j.
- F is `F : W.Modules`, `hqc : F.IsQuasicoherent`, and
  `hfin : F.IsFinitePresentation`, using Mathlib's local finite-free presentation.
  The node explains base-flatness but does not assume F flat; no flatness binder is added.
- `hsupp` expands proper support with a closed immersion i, `MapIsProper` for its
  composite to Spec A_1, and a finite type quasi-coherent G whose canonical direct
  image is isomorphic to the special-fibre tensor pullback of F.
  That tensor pullback is along `properQuotFst (j ≫ f) T_0`.
  Its domain W times_A Spec A_1 is canonically X_1, since j is an open immersion
  whose image contains X_1. Thus no arbitrary factorization or arbitrary map replaces
  the canonical restriction to X_1.
- The existential W' and k give an open subspace of W, by the same scheme-test
  `IsRepresentableWith ... IsOpenImmersion` condition. Its composite k then j
  has point image containing X_0, exactly the second conjunct.
- The final existential Z, i, G is the same closed-carrier proper-support condition
  over A: `MapIsProper (i ≫ k ≫ j ≫ f)`, G quasi-coherent and finite type, and
  `(moduleDirectImage i).obj G ≅ (moduleTensorPullback k).obj F`.
  This is F restricted to W', without any extra finiteness requirement on W'.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `Modules`, `EtaleSite`, `structureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, through `properQuotFibre`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice sheafification instances; underlying predicates are Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleDirectImage`, their specified adjunction.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, read for the convention but not asserted here.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`:
  `ProperQuotFinitePresentation`, `properQuotFibre`, `properQuotFst`, `properQuotSnd`;
  its `ProperQuotient.properSupport` supplies exactly the expanded carrier criterion.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsSeparated`, `MapIsProper` and its component definitions.
- `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal`, giving the unique
  spectrum-to-Spec-Z maps and their equality used by `Over.homMk`.
  `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`.
  The formula T_n used in this report is only an expository abbreviation for
  `CostructuredArrow.mk (yoneda.map (Over.homMk (Spec.map (c.π.app (op n)))
  (specULiftZIsTerminal.hom_ext _ _) :
  Over.mk (specULiftZIsTerminal.from (Spec (A n))) ⟶
  Over.mk (specULiftZIsTerminal.from (Spec c.pt))))`.
  Every actual occurrence T_0 is written in full in the Lean source. There is no
  new definition, arbitrary test scheme, or theorem-node statement dependency.
- `pointImage` is the existing field-representative point-image definition from
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, publicly exposed by dependencies.
  Open immersions use Mathlib's existing `IsOpenImmersion` through scheme tests.

All already-recorded proof dependency modules are imported privately: the quasi-compact
affine tests, etale open image, etale chart support, finite-type composition, and
point/open calculus modules. The other six proof dependencies have no Lean record at
this reading; they are not needed to type this statement and no module is fabricated
for them. The docstring names every proof dependency at its relevant step.

Edge cases checked before writing: empty X and empty special fibre permit empty W';
zero F permits the empty carrier. Constant towers and identity transitions satisfy the
nil-kernel condition, with paper level one still correctly index zero. The zero ring
is allowed. Arbitrary elementwise nil kernels, not just nilpotent ideals or adic
towers, are retained. W need not be quasi-compact. F need not be flat. Finite presentation
of the morphism does not silently become finite type only. Arbitrary ring universes
are supported by the ULift Z convention already used by the sibling modules.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "Shrink an open neighborhood of the special fibre over
  an inverse limit of rings with nil kernels so a finitely presented module has proper
  support". Eight hits: finite-presentation localization, free locus and module support;
  no matching shrinking result.
- `msearch.py ... leansearch`: "A finitely presented sheaf whose special fibre has
  proper support admits a smaller open neighborhood with proper support over an inverse
  limit of nilpotent ring thickenings". Eight hits on finite-presentation predicates
  and constructors; no matching theorem.
- `msearch.py ... loogle '"Henselian", "Proper"'`: zero hits.
- `msearch.py ... grep 'proper.*[Ss]upport|[Ss]upport.*[Ss]hrink'`: eight unrelated
  support hits; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf/AlgebraicGeometry` for proper support,
  support shrinking and inverse-module names: existing module/support infrastructure
  and the canonical inverse-ring spectrum/test helpers, but no theorem of this statement.
  `grep -rn` of this node id in `lean/WeilConjectures` returned no match.
- Read Stacks `spaces-flat.tex` at lemma-proper-support (0CXA) and
  `more-algebra.tex` at lemma-limit-henselian (0CT7), and the node's full proof.

Validation after H2 repair: `scompile.py Q70
lem-sfb-space-inverse-module-proper-shrinking <file>` compiled sandbox and library modes
cleanly (8.8s and 2.4s). No STATEMENT-DISPUTED flag or node fault remains.

## Repair H2

Returned head: 2773624eb19b. The maintainer accepted the mathematics and returned the
added statement dependency on the theorem node
`lem-sfb-space-inverse-module-derived-limit`, which had been used only for its plain
helper definitions. Implemented the explicitly authorized inline alternative:
removed that stmt_dep and the public import of its theorem module; inlined
`Over.mk (specULiftZIsTerminal.from (Spec c.pt))` and the canonical test scheme
constructed by `CostructuredArrow.mk`, `yoneda.map`, `Over.homMk`, and `Spec.map` at
every occurrence; imported the two owning Mathlib modules directly. Updated the
node's verbatim Lean signature and note. Current main has no Lean record for the
item, and its original stmt_deps are exactly those now retained in this delivery.
All other node fields and every mathematical hypothesis and conclusion are preserved.
The delivery wrapper prepares the new commit against current main.

## Second reading by Q70

This is a separate self-review pass with the original JSON and final Lean source open;
the dispatch brief prohibits starting another worker. The maintainer supplies the
independent delivery review. I checked every binder and conjunct against the mapping
above. The subtle points are that paper A_1 is Lean A 0, the special-fibre tensor
pullback lives on W times_A Spec A_1 (canonically X_1 by hcontains), and both proper
support occurrences use a finite type quasi-coherent carrier module with the existing
canonical direct image. Neither an arbitrary fibre map nor a flatness assumption was
introduced. The conclusion requires W' to contain the same special subset in X, not
just its support. All variables and the sole universe are explicitly bound. No
mathematical mismatch or correction was found in this rereading. The H2 repair removes the added theorem dependency entirely. I compared every
expanded test-scheme occurrence with the previous helper bodies at
SpaceInverseModuleDerivedLimit.lean:50,58,63: each uses the same Spec map and the same
terminal-object equality. The expansion is definitionally the previous expression,
so both special-fibre containment clauses and the support pullback retain their meaning.
Checked the original node against the sandbox node: only lean changes; stmt_deps
is exactly the original list. No new node or duplicate definition is introduced.
