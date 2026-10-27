## Worker report

The module `Sheaf.Paper.ConstructibleProjectiveChartRefinement` states
`WeilConjectures.constructible_projective_chart_refinement`, with one `sorry` and no
new definitions. Its statement is the node's common-chart assertion. The seven-step
natural-language proof in the declaration follows the seven DAG proof steps, including
the ordinary restriction/completion comparison, the residue Tor bound, and preservation
of the displayed retractions on intersections. No theorem is proved in this delivery.

The source read is `literature/stacks-project/proetale.tex`,
`lemma-local-structure-constructible-complex` (Tag 09C3), including the statement that
maps between the completed projective terms are arbitrary sheaf-module maps. The
finite open–closed tree and the two separate projective model statements were read
in their recorded modules; neither states this simultaneous conclusion.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)` with
  `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The imported coefficient
  constructions supply the valuation ring, its chosen uniformizer and quotients.
  Index `0` of `scalarReductionDerivedExtension` means exponent one, so all occurrences
  of `Padic.coefficientExtensionRing l E 1` are the residue coefficient ring.
- The scheme is `W : Scheme.{u}`. Quasi-compactness and quasi-separatedness are
  `[CompactSpace W] [QuasiSeparatedSpace W]`. The prime's invertibility is
  `_hl : IsUnit (l : Γ(W, ⊤))`. A global section is a unit iff it is a unit in every
  stalk, so this expresses invertibility on the whole scheme.
- `scalarReductionSource l E W` is exactly the category of module sheaves over
  `completedIntegralCoefficientSheafUnrestricted l E W`, the inverse limit of the
  positive finite quotient sheaves, not the discrete constant valuation ring.
  `M N : DerivedCategory ...` are unbounded ambient derived objects, with
  `_hM` and `_hN : sfIntegralConstructible ...` imposing precisely the given
  integral constructible category: completeness, all constructible reductions,
  and one uniform finite reduction interval. No bounded representative is assumed.
- The finite list of finite partitions is `m`, `n : Fin m → ℕ`, the schemes
  `S a j` and arrows `s a j`. `_hs` states locally closed immersion, `_hc` states
  constructibility of each image, `_hcover` states exhaustive union and
  `_hdisjoint` states pairwise disjointness. `_hlisse` states local constancy of
  each residue-cohomology sheaf after its actual constant-module pullback along
  every `s a j`. Quantification over `K` with `K = M ∨ K = N` is exactly the two
  assertions, and allows `M = N`. No finite partition is assumed to be nonempty.
- The finite tree is indexed by `Fin d`, with `root`, `parent`, `left`, `right`,
  the schemes `T v`, structure maps `toW v`, and actual child edge maps.
  `T root ≅ W` identifies the root with its structure map. The root is its own
  parent; every other vertex has a smaller parent index and is one of that parent's
  two children. Thus all vertices reach the root and there are no cycles or extra
  components. `leaf` is equivalent to having no nonroot child. Internal vertices
  have two distinct larger children with the stated parent and commuting maps.
- Every `T v` is qcqs and `toW v` is an immersion. Internal left edges are
  quasi-compact open immersions; right edges are closed immersions; their images
  are disjoint and have union the whole parent. This is exactly an open split and
  its closed complement. The tree's finite recursive splits also imply that its
  leaf images partition `W`; no extra geometric tree premise is needed.
- Each nonempty leaf has, for every partition `a`, a `j` and an actual scheme map
  `f : T v ⟶ S a j` with `f ≫ s a j = toW v`. These are scheme-theoretic
  factorizations, rather than image containment alone.
- Both leaf restrictions use the existing `ordinaryIntegralDerivedPull l E (toW v)`.
  In particular they are not made complete by defining restriction to be a completed
  pullback. `IntegralOnSlice.IsComplete ... none` is the recorded global quotient-tower
  Roos completeness predicate, applied to those ordinary restrictions.
- For each of the two restrictions, `∃ a b : ℤ, a ≤ b` and the outside-interval
  `IsZero` condition express finitely many nonzero residue cohomology sheaves.
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses` with
  `Module.Finite (ULift ... (Padic.coefficientExtensionRing l E 1))` gives finite
  module local models over the residue field, equivalently finite-dimensional
  vector-space local models. This uses the recorded general-universe local-constancy
  definition directly. It does not impose constancy on an entire leaf.
- `V : (T v).ProEt` is the single weakly etale covering object. `IsAffine V.left`
  supplies affineness. The explicitly quantified `Epi f → Function.Surjective ...`
  condition is evaluation on the final object of `V.left`'s own small pro-etale
  site, as in the node. `Presieve.singleton ... ∈ ProEt.precoverage ...` states
  that the canonical arrow `V → T v` is a pro-etale covering.
- A single `c : ℕ` and `U : Fin c → V.left.Opens` give the common chart partition.
  Their supremum is top and they are pairwise disjoint. Every `U i` is explicitly
  qcqs. The composite maps `(U i).ι ≫ V.hom` cover `T v`: the range condition
  states joint surjectivity. These arrows are automatically weakly etale. Together
  with qcqs domains and the quasi-separated target, this is equivalent to the
  pro-etale covering condition: each arrow is quasi-compact, and over any affine
  target open one takes finite affine covers of the inverse images. Thus the
  displayed geometric covering clause retains the node's full covering property.
- For each chart and each of `M,N`, `∃ P : CochainComplex ... ℤ` gives a
  representative over exactly `B_(U i)`. `P.IsStrictlyGE a` and `P.IsStrictlyLE b`
  say its actual terms vanish outside a finite interval. For each degree `q`, the
  displayed `ι` and `ρ` split `P.X q` off the finite product of unit modules, with
  `ι ≫ ρ = 𝟙 _`. In this additive module-sheaf category finite products are also
  finite direct sums, including the zero-rank case. The concluding derived
  isomorphism identifies `Q.obj P` with the ordinary restriction along the full
  composite `(U i).ι ≫ V.hom ≫ toW v`. The cover is shared by the two complexes;
  their representatives and bounds can differ.
- No hypothesis says Noetherian, noetherian dimension, finite-type scheme, constant
  differential, or constant matrix. The arbitrary cochain differential is an actual
  completed-coefficient module-sheaf morphism. The guard `leaf v → Nonempty (T v) →`
  imposes no chart conditions on empty leaves, including the empty root.

Dependency declarations used (recorded declarations and their imported constructions):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing` and their quotient transitions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and the
  scheme equivalence with `QuasiSeparatedSpace`; the statement uses the latter.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`,
  `ProEt.topology` and `ProEt.precoverage` on the small weakly etale site.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, importing the existing
  `completedIntegralCoefficientSheafUnrestricted` and the finite coefficient tower.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the Mathlib `SheafOfModules` category used by `scalarReductionSource`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; `...HomologySequence`: `DerivedCategory.homologyFunctor`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`, whose `none`
  case is `IsDerivedCompleteUnrestricted` on the global small site.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, with `scalarReductionSource` and its instances.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`:
  `IsLocallyConstantProEtaleModuleSheafOfUniverses` and the recorded
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses` specialization.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `intrinsicFiniteTorsionConstructible`, used by the imported integral predicate.
- `def-sf-ordinary-integral-derived-pullback` records the existing
  `WeilConjectures.ordinaryIntegralDerivedPull` and its named existence instance
  `WeilConjectures.ordinaryIntegralPull_hasLeftDerived`, in
  `Sheaf.Paper.OrdinaryCompletedIntegralPullback`. This definition node replaces the
  theorem-node dependency from the returned packet. Its underlying module functors
  belong to `def-sf-ordinary-integral-pullback-construction`.
- `def-weil-proetale-inverse-image` owns
  `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback`, used in `_hlisse`.
  Its module `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` is now imported publicly.
  The homology theorem module remains a non-public proof import, matching proof step 3.

Every stated proof dependency's module is imported. The only proof dependency with
no recorded Lean module is `lem-fix-qcqs-completion-unit-locality`; its mathematical
use is retained explicitly in the proof docstring, and no placeholder copy or extra
postponed theorem is introduced. The affine-qcqs proof dependency is Mathlib's existing
`Scheme.compactSpace_of_isAffine` and `quasiSeparatedSpace_of_isAffine`, available
through the scheme imports. All declaration signatures and local-constancy docstrings
were read in the project sources, including the full ordinary-pullback construction.

Edge cases checked before finalizing: empty `W` (one empty root leaf, all chart guards
vacuous); empty initial partition list (`m = 0`); an empty partition of nonempty `W`
(the partition cover hypothesis correctly rules it out); empty strata and empty tree
children; coincident complexes `M = N`; zero complexes and empty residue support
(`a = b = 0` allowed); zero-rank projective terms (`r = 0`); empty chart index sets
on an empty cover; arbitrary negative or positive cohomological bounds; arbitrary
non-Noetherian qcqs schemes. `Fin d` with a root correctly forces a nonempty tree.
The common universe `u` contains both schemes and the finite coefficient extension;
no equality of the small site's object universe `u+1` and morphism universe `u` is
imposed. Module coefficients and module objects live in `u+1`.

Searches for an existing exact theorem:

- `msearch.py leanfinder`: “Two integral constructible complexes admit common finite
  projective sheaf charts on a weakly contractible proetale cover after open closed
  stratification”. Eight hits, all affine-transition-limit open-cover refinements,
  none about integral derived complexes or the asserted common projective charts.
- `msearch.py loogle`: `IsWeaklyContractible, CochainComplex, IsStrictlyGE`.
  No hits; Loogle reports the project-defined first identifier is unknown.
- `msearch.py grep`: `projective.*chart|chart.*refinement|finite_open_closed`, under
  Mathlib `AlgebraicGeometry`. No hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf`: common/projective chart patterns
  and `finite_open_closed_refinement`. Located the single-complex projective-model
  module and the finite refinement theorem, but no simultaneous theorem.
- `rg` for the item id in `lean/WeilConjectures`: no match. Search for the proposed
  declaration name in Mathlib, upstream and project Lean: no existing declaration.

No mathematical statement correction is needed. No STATEMENT-DISPUTED issue remains.
The node file changes only in `lean` and the addition of the two definition dependencies
listed above to `stmt_deps`. The original theorem signature and proof plan are unchanged.

Validation: the required `scompile.py Q10 ... ConstructibleProjectiveChartRefinement.lean`
passed, both as a sandbox file and as its named library module, with no diagnostics.
The first compile found use of the ordinary `Over.homMk` rather than the small site's
`MorphismProperty.Over.homMk`; the final statement uses the latter and the explicit
category right-identity witness. No diagnostic declarations remain in the module.

## Repair of return H2

Compared the saved packet with the current base: only `lean` and `stmt_deps` differed.
The saved delivery log identifies the returned head as `31e2f8a3749`; the resumed
initial dry run passed at `972ea93b046`, but still contained the returned dependency
fault. This repair removes `lem-tw-ordinary-completed-integral-pullback` from the
item's statement dependencies and adds `def-sf-ordinary-integral-derived-pullback`
and `def-weil-proetale-inverse-image`. The Lean theorem signature is unchanged.
The latter's existing constant-module pullback is now available through its owning
module's public import; the homology theorem remains a proof-only import.

## New nodes

`def-sf-ordinary-integral-derived-pullback` defines the ordinary unbounded total
left derived pullback for the canonical completed coefficient ring map, before
completion. Its `existing: true` record owns exactly the existing
`ordinaryIntegralPull_hasLeftDerived` and `ordinaryIntegralDerivedPull` in
`Sheaf.Paper.OrdinaryCompletedIntegralPullback`, without creating any Lean declarations.
The prime, extension, arbitrary scheme map, completed rings and additive pullback
are the parameters of the existing module; `mapHomotopyCategory` followed by `Qh`
is F, and `totalLeftDerived Qh (HomotopyCategory.quasiIso ...)` supplies the specified
universal functor. The named instance is precisely its existence prerequisite.
Stacks `sites-cohomology.tex`, Section 06YV and Lemma 06YY construct the same unbounded
ringed-topos pullback by flat-term K-flat resolutions. The node asserts no constructibility
preservation or invertibility of the completion comparison.

Searches through `msearch.py`: LeanSearch “total left derived pullback of sheaves of
modules on ringed sites” gave eight hits, including `Functor.totalLeftDerived` and
`SheafOfModules.pullback`, which are the general constructions used by the published
specialization. LeanFinder “unbounded total left derived ordinary pullback of completed
integral coefficient module sheaves on the small proetale site” gave eight unrelated
or ordinary module-pullback hits. Mathlib grep
`ordinaryIntegralDerivedPull|ordinaryIntegralPull_hasLeftDerived` gave no hits.
Project grep found the exact declarations at lines 227 and 235 of the existing module.
DAG grep found ownership only in the theorem record, while the ordinary module-pullback
construction definition node explicitly omits these two. `blueprint_refs.py search
ordinaryIntegralDerivedPull` gave zero matches; `ancestor` returned
`lem-fix-weil-operations`. These results justify a new definition-node binding to the
existing declarations. Empty schemes, identity maps and zero complexes remain allowed;
there are no qcqs, Noetherian, completeness or constructibility hypotheses in this
ordinary derived functor construction.

Repair validation: `scompile.py` compiled the changed theorem module both as a sandbox
file and under its library name without Lean diagnostics. The repaired packet's
`deliver2.py --no-push` passed preflight and compilation at `8dfb38f26ae`, including
the generated checks of both declarations in the new existing-definition record.
The self-check confirmed verbatim equality of `lean.statement` with the theorem
signature, one expected `sorry`, no lines over 100 characters, and the required JSON
format. Only import visibility and definition ownership changed in this repair.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
