## Worker report

The module `lean/Sheaf/AlgebraicGeometry/QuasiCoherentMayerVietorisOpenCover.lean`
states `AlgebraicGeometry.Scheme.quasiCoherent_mayerVietoris_openCover`, with its sole
proof `sorry`. It defines no new notion. The node is unchanged apart from `lean` and
adding the landed definition node `def-sc-open-module-cohomology` to `stmt_deps`.
There is no statement correction, disputed statement, or dependency module.

Hypothesis and clause correspondence:

- The ambient scheme is `(X : Scheme.{u})`, and the open subscheme on which the
  module lives is `(W : X.Opens)`, with scheme `W.toScheme`. The ringed space used
  to compute its module cohomology is `W.toScheme.toRingedSpace`.
- The opens of the cover are `(U V : Opens W.toScheme)`. They represent the
  original opens inside W by their inverse images along the open immersion W → X.
  Their union and intersection are `U ⊔ V` and `U ⊓ V`. The statement treats all
  pairs simultaneously, just as the recorded ringed-space theorem does; the
  requested cover of W is obtained by taking `U ⊔ V = ⊤`. This does not require
  that F extend to X: F is always defined on W itself. For pairs with smaller
  union, the sequence is that of the quasi-coherent restriction to that union,
  another case of the node with a smaller base open.
- An arbitrary quasi-coherent module on W is
  `(F : SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  [F.IsQuasicoherent]`. This is the recorded Mathlib quasi-coherence notion of
  `pqf-def-coherent`, not coherence or finite presentation. The coefficient
  category and all cohomology groups use universe u, as do the existing definitions.
- `H^p(A,F|A)` is `(openModuleCohomology W.toScheme.toRingedSpace p A).obj F`.
  It derives sections on O_W-modules, not Ext-cohomology in abelian sheaves.
  The established open-cohomology definition identifies this computation with
  cohomology of the restriction: an injective module resolution stays injective
  on every open. Thus the last conjunct computes the target sequence with F|T
  using the same resolution restricted to T, rather than introducing different
  cohomology objects or a second definition of restriction.
- The existential δ supplies additive connecting morphisms
  `H^p(U ⊓ V,F) ⟶ H^(p+1)(U ⊔ V,F)` for every F, U, V and p.
- The map from union cohomology to the finite direct sum is the displayed
  pair of `openModuleCohomologyRestriction ... (homOfLE le_sup_left/right)`
  components. A product of two abelian groups is their finite direct sum.
- The map to intersection cohomology is the displayed subtraction of the
  `inf_le_left` and `inf_le_right` restriction components. The order of the
  signs is U minus V, as in the node and Stacks 01EB.
- The first conjunct is `Function.Injective` for this pair in degree zero,
  rendering the initial zero and the convention H^(-1)=0.
- For every `(p : ℕ)`, the second conjunct contains three `Function.Exact`
  assertions: pair then difference; difference then δ; δ then the pair in
  degree p+1. Hence exactness holds at every position, including p=0, with
  no boundedness or cohomological vanishing hypothesis.
- The third conjunct quantifies a second quasi-coherent G and an arbitrary
  morphism `(f : F ⟶ G)`. Its equality
  `δ F U V p ≫ H^(p+1).map f = H^p.map f ≫ δ G U V p`
  is commutativity at the connecting map. The other squares are already
  naturality squares of the established restriction natural transformations,
  and of their pairs and differences. Thus it gives a morphism of the entire
  sequence, not just a family of exact sequences without naturality.
- The fourth conjunct quantifies an arbitrary smaller open T of W. Restricting
  to `U ⊓ T` and `V ⊓ T` gives their union `(U ⊓ T) ⊔ (V ⊓ T)` and intersection
  `(U ⊓ T) ⊓ (V ⊓ T)`. When U ∪ V = W, this union is T. The last equality is
  the connecting-map square, using `sup_le_sup inf_le_left inf_le_left` and
  `inf_le_inf inf_le_left inf_le_left` for its two restriction maps. The other
  squares follow from composition of the canonical cohomology restriction maps.
  Under the existing definition of open cohomology these are exactly the
  maps to H^p(A ∩ T,F|T) requested by the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  `Hom`, read with their full structure signatures and docstrings; scheme
  opens and their `toScheme` encode the open subscheme.
- `Sheaf.AlgebraicGeometry.Coherent` (pqf-def-coherent): its module docstring
  explicitly specifies that quasi-coherent means Mathlib
  `SheafOfModules.IsQuasicoherent`; the node's primary declaration
  `RingedSpace.IsCoherent` concerns the coherent clause and is not imposed here.
  The full Mathlib signatures/docstrings of `IsQuasicoherent` and
  `isQuasicoherent` were read in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Sheaf.Paper.PQFCohomology` (pqf-def-cohomology): the full statement and
  docstring of `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` were
  read. Its degree functors are the existing
  `Sheaf.Topology.RingedSpaceModuleCohomology` declarations
  `RingedSpace.globalSectionsFunctor` and `RingedSpace.moduleCohomology`;
  their signatures and definitions were also read. The current statement uses
  their recorded open version, rather than importing an unused higher-direct-image
  theorem.
- `Sheaf.Topology.OpenModuleCohomology` (added landed statement dependency):
  `AlgebraicGeometry.RingedSpace.openModuleCohomology` and
  `AlgebraicGeometry.RingedSpace.openModuleCohomologyRestriction`, read in full.
- Proof dependency `Sheaf.Topology.ModuleMayerVietoris`:
  `AlgebraicGeometry.RingedSpace.module_mayerVietoris`, signature and full
  docstring read. It supplies precisely the scheme specialization proof route;
  it is not imported just to give a sorry statement an unused proof import.
- Mathlib `Function.Exact` renders image = kernel at all consecutive positions.

Edge cases checked before writing: empty X or W, U or V empty, both empty, U=V,
zero F, degree p=0, and arbitrary degree p. There is no nonempty or finiteness
assumption. For an empty component, restriction is zero and the sequence reduces
correctly to that of the remaining component. For U=V the pair is diagonal and
the next map is subtraction. The two-group product includes the zero cases.
For T empty the fourth conjunct still compares well-typed canonical restrictions.
There is no characteristic, separatedness, noetherian, or quasi-compactness
assumption; none is needed by Stacks 01EB or its ringed-space specialization.

Searches for existing statements/notions (2026-10-11):

- `msearch.py ... leanfinder "Mayer Vietoris cohomology of modules on scheme
  open cover natural connecting maps"`: eight hits, all generic site
  MayerVietorisSquare/sheaf-condition/short-complex declarations; none is the
  O_X-module derived-functor theorem with this naturality.
- `msearch.py ... loogle "MayerVietorisSquare, sequence_exact"`: zero hits;
  service says unknown identifier MayerVietorisSquare.
- `msearch.py ... grep "MayerVietoris|mayer.vietoris" AlgebraicGeometry`:
  zero Mathlib hits. Direct reading of
  `Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean` confirms
  its `sequence_exact` is site-level abelian-sheaf Ext cohomology, not this notion.
- `rg -n 'mayerVietoris|mayer_vietoris|lem-sc-mayer-vietoris-open-cover'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- `rg` on `lean/Sheaf` found the recorded ringed-space theorem and open-module
  cohomology definitions, but no matching scheme/quasi-coherent specialization.
- `rg` on `dag/lean_names_upstream.json` found no existing declaration with
  the chosen name or a Mayer–Vietoris spelling.
- `rg` for quasi-coherence in the source found many uses of the Mathlib
  `IsQuasicoherent` class; reading the recorded Coherent module confirms this
  is exactly the dependency's quasi-coherence notion. No replacement definition
  or new node is needed.

Source: [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB),
opened because the local literature file is absent. The displayed sequence,
functoriality in F, and the injective-resolution short exact sequence in the proof
match the formalization and its recorded proof route. The restriction clause
is the restriction of this resolution construction, as the source field specifies.

Validation: initial server compile was clean (3.9 seconds); final delivery dry run
will compile the finalized file and check its record and report. The independent
second reader, not this worker, will add the second-reading section and deliver.

## Second reading by G1

The node introduces a scheme X, an open subscheme W of X, opens U and V of W
covering W, a quasi-coherent O_W-module F, and the Mayer--Vietoris long exact
sequence, with pair and difference restriction maps, naturality in F, and
compatibility with restriction to every T ⊆ W. The Lean renders X and W as
`(X : Scheme.{u})` and `W : X.Opens`, U and V as `Opens W.toScheme`, and
quasi-coherence as `[F.IsQuasicoherent]`; open cohomology is
`openModuleCohomology W.toScheme.toRingedSpace`. The existential δ supplies the
connecting maps. The initial injectivity and three `Function.Exact` clauses render
the long exact sequence (including p = 0). The naturality clause is the displayed
commuting square for every module morphism. The final clause is the square after
restricting U,V to T. Every cohomology restriction map and sign agrees with the
node.

The first reading omitted the essential cover condition. The theorem originally
quantified arbitrary U,V and therefore stated a sequence for pairs that need not
cover W. I corrected the item statement to say U ∪ V = W and changed each
exactness, naturality, and restriction clause in Lean to carry the hypothesis
`U ⊔ V = ⊤ →`. The connecting-map family remains defined for all pairs, while
all asserted properties are restricted to covers. The three citers continue to
hold: `def-sc-open-module-cohomology` is unchanged; the Mayer--Vietoris diagram
and finite-support arguments apply only to covers and supply the new hypothesis.

Edge cases checked are empty X or W, empty U or V, both empty (when W is empty),
U = V = W, the zero module, p = 0, and arbitrary p. No characteristic,
Noetherian, separatedness, finiteness, or nonemptiness assumption was added.
Searches in Mathlib, WeilConjectures, and lean/Sheaf found no existing
scheme O_X-module Mayer--Vietoris declaration; only generic site-level
Mayer--Vietoris primitives occur.

## Statement corrected

The old statement omitted the requirement that U and V cover W. Following
Stacks Project Lemma 01EB, the corrected statement adds U ∪ V = W, rendered in
Lean as `U ⊔ V = ⊤`, to every asserted clause. Citers
`def-sc-open-module-cohomology`, `lem-sc-invert-s-cohomology-mayer-vietoris-diagram`,
and `lem-pc-finite-support-hi` still hold for their stated cover applications.
