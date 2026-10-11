## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePresentationHomDirectedColimit` states
`AlgebraicGeometry.Scheme.Modules.hom_directedColimit_of_isFinitePresentation`.
Its only theorem has proof `sorry`; no definitions or proofs were added.
The node copy changes only `lean`.

### Matching the statement

- Scheme X: `(X : Scheme.{u})`, using Mathlib's `AlgebraicGeometry.Scheme`.
- Quasi-compact X: `[CompactSpace X]`.
- Quasi-separated X: `[QuasiSeparatedSpace X]`, the compact-open-intersection
  characterization for schemes (Stacks 01KO). The conventions dependency has
  no declaration of its own and explicitly delegates these notions to Mathlib.
- Directed set I: `(I : Type w) [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Stacks 00D3 explicitly requires nonemptiness;
  no antisymmetry is imposed.
- System of O_X-modules: `(D : I ⥤ X.Modules)`. Here Mathlib's
  `Scheme.Modules` is exactly `SheafOfModules.{u} X.ringCatSheaf`.
  Functor identity/composition encode the system identities, and
  `D.map (homOfLE hik)` is the transition from i to k.
- Specified colimit `(F,(c_i))`: `(c : Cocone D) (hc : IsColimit c)`.
  `c.pt` is F and `c.ι.app i` is c_i. Naturality imposes compatibility;
  `IsColimit` is precisely the universal property, not a chosen replacement
  colimit with different maps. This also works for index universes larger than u,
  whenever the supplied colimit exists.
- Finitely presented G: `(G : X.Modules)
  [SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) G]`.
  The definition inspected in Quasicoherent.lean says locally a cokernel of
  a map of finite coproducts of the ring sheaf, precisely the finite local
  presentation in the node and Stacks 01BN. No extra quasi-coherence hypothesis
  is imposed; it follows from the finite local presentation.
- Surjectivity/factorization: the first conjunct says for every
  `h : G ⟶ c.pt`, there are i and `g : G ⟶ D.obj i` with
  `g ≫ c.ι.app i = h`.
- Injectivity/eventual equality: the second conjunct quantifies both i,j and
  both maps g,g'; equality after composition with the supplied cocone maps
  implies a k and inequalities `hik : i ≤ k`, `hjk : j ≤ k` with
  `g ≫ D.map (homOfLE hik) = g' ≫ D.map (homOfLE hjk)`.
- Canonical-map bijectivity: expressed exactly by those two explicit clauses
  in the node, rather than by constructing a separate quotient carrier.
  The colimit of the Hom sets is the disjoint union modulo eventual equality;
  cocone naturality makes postcomposition descend. The first clause is its
  surjectivity, and the second is its injectivity. Conversely bijectivity gives
  both clauses. Thus no clause or strength is lost.

### Dependencies inspected and used

`def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, declarations
`AlgebraicGeometry.Scheme` and `Scheme.Hom` (scheme category).
`def-weil-pbc-scheme-conventions`: convention-only record; CompactSpace and
QuasiSeparatedSpace render its qcqs specialization. Read the convention record
and the definition/docstring in Mathlib.Topology.QuasiSeparated.
`def-weil-sheaf-of-modules-category`: Mathlib.Algebra.Category.ModuleCat.Sheaf,
`SheafOfModules` and its Hom/category, via
Mathlib.AlgebraicGeometry.Modules.Sheaf's `Scheme.Modules` and category.
`def-weil-pbc-category-colimit`: Mathlib.CategoryTheory.Limits.HasLimits,
`CategoryTheory.Limits.colimit`; its additionally recorded `Cocone` and
`IsColimit` are used directly (their full signatures/docstrings were inspected
in Limits.Cones and Limits.IsLimit). A chosen colimit is unnecessary because
this node supplies a colimit cocone. All original statement dependencies remain.

The declaration docstring carries all five proof steps of the node and the
supporting node ids; those are future stage-3 inputs, not additional hypotheses.

### Source and edge cases

The local literature checkout does not include stacks-project/modules.tex.
Read the primary source at https://stacks.math.columbia.edu/tag/01BS,
https://stacks.math.columbia.edu/tag/01BN, and
https://stacks.math.columbia.edu/tag/00D3 instead. They confirm the statement,
finite local presentation definition, and nonempty directed preorder convention.

Checked: empty schemes are allowed (no point/nonempty assumption on X);
zero G and zero diagram terms are allowed; finite presentations with zero
relations or zero generators are allowed. Empty I is excluded by the source's
definition of directed set, not by an added assumption. Without nonemptiness,
the first clause would fail even for zero G and the empty diagram's zero
colimit. Non-antisymmetric preorders are allowed. Universes u,w are explicitly
bound and independent; no finiteness/countability constraint is imposed on I.
There is no characteristic restriction. No statement correction or dispute.

### Searches

- msearch.py leanfinder: `Hom from a finitely presented sheaf of modules commutes
  with directed colimits on a qcqs scheme`: eight hits, including
  Scheme.Modules.instHasColimits and finite-presentation definitions/presentation
  maps, but no theorem with this statement.
- msearch.py loogle: `SheafOfModules.IsFinitePresentation,
  CategoryTheory.Limits.IsColimit`: zero hits.
- msearch.py grep: `IsFinitePresentation.*[Cc]olimit|[Cc]olimit.*IsFinitePresentation`:
  zero hits.
- msearch.py leansearch: `Hom from finitely presented sheaves of modules commutes
  with directed colimits on quasi compact quasi separated schemes`:
  unavailable (Internal Server Error). No mathematical verdict inferred.
- rg in WeilConjectures and lean/Sheaf:
  `IsFinitePresentation|hom.*colimit|finitePresentation.*colimit`:
  finite-presentation/descent results, abstract localization Hom colimits,
  and cohomology colimits, none this O_X-module Hom theorem.
- grep of this item id in WeilConjectures: no occurrences.
- rg of `hom_directedColimit|hom_directed_colimit|hom.*finitePresentation` in
  dag/lean_names_upstream.json: no declaration-name collision.
- Inspected Mathlib's IsFinitePresentation source and module category source
  rather than introducing a duplicate finite-presentation notion.

### Verification

Server scompile.py: clean compilation (2.0 seconds); no warning.
The first attempt needed the explicit ring and universe in the finite-presentation
binder, which was corrected. Final delivery preflight is run after this report.

## Second reading by G1

Independently opened the sandbox node and module, all four statement-dependency
nodes, and the Mathlib declarations they designate. Read the actual Stacks
`modules.tex` source fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/modules.tex at
`lemma-finite-presentation-quasi-compact-colimit` and
`definition-finite-presentation`; the local literature directory lacks this file.
Also checked https://stacks.math.columbia.edu/tag/00D3 for the indexing convention.
The source assumes a ringed space, a directed preorder, finite presentation,
and cofinal finite covers with quasi-compact intersections; its scheme
specialization in this node supplies the last hypothesis by qcqs. There is
no implicit Noetherian, separated, field, or characteristic hypothesis.

Object/hypothesis/conclusion checklist, in the order of the node:

- Scheme X: `(X : Scheme.{u})`, the Mathlib scheme and scheme category of
  `def-pc-scheme`. PASS.
- X quasi-compact: `[CompactSpace X]`, compactness without a Hausdorff assumption.
  X quasi-separated: `[QuasiSeparatedSpace X]`, whose definition requires
  compactness of intersections of compact opens; for schemes this agrees with
  quasi-separatedness (01KO). The convention node introduces no private
  declaration. PASS for both hypotheses.
- Finite local presentations: the node's finite m,n exact sequence is rendered
  by `[SheafOfModules.IsFinitePresentation.{u} (R := X.ringCatSheaf) G]`.
  Opened `Presentation`, `Presentation.IsFinite`, `QuasicoherentData`, and
  `IsFinitePresentation` in Mathlib's Quasicoherent module: a covering family,
  finite generating sections of G, and finite generating sections of the
  kernel of the corresponding free-module surjection. On the open site these
  are exactly the local presentations in 01BN. No independent quasi-coherence
  assumption occurs. PASS.
- Directed set I: `(I : Type w) [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Source 00D3 requires nonemptiness and common upper
  bounds but not antisymmetry; Mathlib IsDirected supplies the upper bounds.
  PASS.
- System of O_X-modules: `(D : I ⥤ X.Modules)`. Opened Scheme.Modules and
  its category: it is `SheafOfModules.{u} X.ringCatSheaf`, with sectionwise
  linear, restriction-compatible morphisms from SheafOfModules.Hom. Functor
  laws give the system laws, and `D.map (homOfLE hik)` is the i-to-k transition.
  This uses the recorded category notion, not constant-coefficient or etale
  sheaves. PASS.
- Specified colimit F and maps c_i: `(c : Cocone D) (hc : IsColimit c)`.
  Opened Cocone and IsColimit: c.pt is F, c.ι.app i is c_i, naturality is
  compatibility, and desc/fac/uniq are the universal property. Both notions
  are explicitly recorded by `def-weil-pbc-category-colimit`; choosing another
  colimit object is unnecessary. PASS.
- Finitely presented G: `(G : X.Modules)` and the finite-presentation binder
  above refer to the same G in both conclusions. PASS.
- Canonical Hom-colimit map bijective: the two conjuncts unpack exactly the
  quotient of pairs (i,g) by eventual equality; cocone naturality makes
  postcomposition descend. Surjectivity is the first conjunct and injectivity
  is the second, so omitting a separate quotient construction loses no clause.
  PASS.
- Every h factors: `∀ h : G ⟶ c.pt, ∃ (i : I) (g : G ⟶ D.obj i),
  g ≫ c.ι.app i = h`. Lean composition has precisely the order c_i after g.
  PASS.
- Equality becomes eventual equality: universal i,j,g,g' followed by the
  equality of their composites, then `∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)`
  and equality after `D.map (homOfLE hik)` and `D.map (homOfLE hjk)`.
  The common stage depends on these representatives as in the node. PASS.

Edge cases: empty I is excluded by the source itself, not an added hypothesis;
otherwise even the zero-source factorization clause would fail for an empty
system. Empty X is allowed: no Nonempty X instance is requested, and the local
presentation can use an empty cover. Zero G and zero diagram terms are allowed;
finite generators/relations can have cardinality zero. There is no restriction
on characteristic or countability. Universes u,w are explicitly bound and
independent. The scheme and its module values use the standard common ambient
universe; larger values are accommodated by enlarging that ambient universe.
A diagram in any universe w is allowed with its supplied colimit, without a
HasColimitsOfSize assumption. No unbound variables occur.

Independent searches (different wording from the first reader):

- msearch LeanFinder: `locally finitely presented module sheaf on a compact
  quasi separated scheme is a finitely presentable object`: eight hits, all
  finite-presentation definitions or their finite-type/quasi-coherent
  consequences; no Hom-colimit theorem.
- msearch Loogle: `SheafOfModules.IsFinitePresentation,
  CategoryTheory.IsFinitelyPresentable`: zero hits.
- msearch LeanSearch: `finite presentation sheaf modules compact quasi
  separated Hom directed colimit`: unavailable, Internal Server Error;
  no mathematical verdict assigned to that service failure.
- Independent rg across Mathlib, WeilConjectures, and repository lean/Sheaf:
  `isfinitepresentation.*(colimit|presentable)|
  (colimit|presentable).*isfinitepresentation|finitely.?present.*sheaf|
  hom_directedColimit_of_isFinitePresentation` (case insensitive).
  Only the source's Etale.isFinitelyPresentable_of_isConstructibleSheaf is
  relevant-looking. Opened its signature: it concerns constructible sheaves
  of modules over a Noetherian constant ring on the small etale site, not
  locally finitely presented O_X-modules. It cannot serve this node. The
  project's finite locally free pushforward mention is also unrelated.
  No duplicate theorem was found; existing Mathlib definitions are used.

No new definition nodes, dependency modules, or statement correction are in
this delivery, and none are needed. Checked the module and theorem docstrings:
source and blueprint markers are present, and all five proof steps and their
supporting nodes are carried over. There are no definitions with sorry data;
the single theorem is left sorry, as stage 2 requires. Imports serve the
scheme module category, finite presentation, preorder category, directedness,
and quasi-separatedness. The recorded lean.statement equals the signature
verbatim. No mismatch was found, so no correct Lean or node text was rewritten;
only this independent reading and its search evidence were added.

Verification: scompile.py compiled the delivered module cleanly in 2.0 seconds,
exit code 0, without warnings. Delivery dry run and push follow this reading.
