## Worker report

Stated `AlgebraicGeometry.AlgebraicSpace.relative_ampleness_iff_fpqc_scheme_cover` in
`Sheaf.AlgebraicGeometry.SpaceRelativeAmplenessFpqcDescent`. Its only proof is `sorry`.
Repair H2 adds def-sfb-scheme-space-zariski-restriction and its small construction module.
No mathematical statement is corrected and no dependency record is repaired.
The source was read at spaces-descent.tex, lemma-descending-property-ample (0D3C),
and spaces-divisors.tex, definition-relatively-ample (0D31) and
lemma-relatively-ample-sanity-check (0D32).

Hypotheses and clauses, matched individually:

- The scheme base is `T.left : Scheme.{u}`. The auxiliary `S : Scheme.{u}` is the
  ambient scheme of the dependency's algebraic-space category. `T : Over S` and
  `X : AlgebraicSpace S` use that category without restricting the mathematical case:
  any space over the node's T can be taken over S = T with its structural map.
- The given map is `f : X ⟶ schemeSpace T`, with its actual map of presheaves
  `f.hom.hom`. `schemeSpace` is the representable fppf sheaf, not a different space.
- `L : X.Modules` is a module on the existing small étale ringed site;
  `hL : X.IsLineModule L` is exactly local isomorphism to the structure sheaf.
- `I : Type v`, `Tᵢ : I → Over S` and `g : ∀ i, Tᵢ i ⟶ T` are the covering
  schemes and maps. `hg` is membership of the underlying family of scheme maps in
  `Scheme.fpqcPrecoverage T.left`. It requires neither a finite index set nor a
  quasi-compact individual cover map.
- The left side exhibits `Z : Over S`, its map `a : schemeSpace Z ⟶ X`, and
  `p : Z ⟶ T`. `IsIso a` says precisely that X is represented by this scheme.
  `a.hom.hom ≫ f.hom.hom = yoneda.map p` identifies its structural map with f.
- For each affine open `V : T.left.Opens`, the predicate `IsAffineOpen V` selects
  exactly the node's affine opens. `p.left ⁻¹ᵁ V` is their inverse image in Z.
  `Scheme.Modules.tensorPullback (p.left ⁻¹ᵁ V).ι` restricts the line module to it.
- The ordinary module on Z is, literally,
  `(schemeSpaceZariskiRestriction Z).obj ((moduleTensorPullback a).obj L)`.
  The first operation is canonical tensor pullback along the representing map to X;
  the second is the existing chart restriction evaluated at the identity chart of Z,
  hence direct restriction from its representable-space small étale site to Zariski opens.
  The ring comparisons are pullback of regular functions. No arbitrary isomorphic replacement module is assumed.
- `∃ h : (...).IsInvertible, @Scheme.Modules.IsAmple ... h` states absolute
  ampleness on that inverse-image scheme, including quasi-compactness as required
  by the recorded definition. The existential is only its proof argument, not an
  extra geometric hypothesis or arbitrary choice of module.
- The equivalence is `↔`, and its right side begins `∀ i : I`. For each member it
  exhibits `Z`, `a : schemeSpace Z ⟶ X`, and `p : Z ⟶ Tᵢ i` with
  `IsPullback a.hom.hom (yoneda.map p) f.hom.hom (yoneda.map (g i))`.
  This is exactly the presheaf fibre-product universal property, so Z represents
  X_i = X ×_T T_i. The module used is the tensor pullback along its actual composite
  a to X; functoriality identifies it with L_i on X_i. The remaining affine-open
  formula is identical, now over `(Tᵢ i).left`, and states local relative ampleness.
- Consequently schematicity is a conclusion on the left, not a hypothesis on X.
  Local schematicity is part of each local relative-ampleness condition, as in the
  node. There is no properness, Noetherian, quasi-separatedness, or quasi-compactness
  hypothesis on f, X, T, or the covering schemes.

Dependency declarations used (source declarations and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Scheme.Opens`, and affine opens.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`, `IsLineModule`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: imports the existing enlarged
  ringed-site construction, including `schemeSpace` from `EnlargedEtaleRingedSite`.
  Its current commutative-ring structural-map extension is retained unchanged.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `ZariskiEtaleModuleContext.restriction`, and
  `scheme_zariski_etale_quasiCoherent_equivalence` (including its line-module clauses).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple` (quasi-compact
  scheme, positive tensor power, affine nonvanishing neighbourhood at every point).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fpqcPrecoverage` and its base-change
  and composition axioms; the family is `Presieve.ofArrows`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleTensorPullback`,
  normalized by `moduleTensorAdjunction` to the actual chart-section direct image.
- `Sheaf.AlgebraicGeometry.SchemeSpaceZariskiRestriction`:
  `schemeSpaceIdentityEtale` and `schemeSpaceZariskiRestriction`. This definition node
  owns the main statement's Zariski restriction. It directly specializes the existing
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction.schemeRestriction` to the
  representing scheme's identity étale chart.
- `Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison` remains a private
  proof import for the graded evaluation comparison in the natural-language proof;
  none of its conclusion or ancillary definitions is used by the repaired signature.
- The direct statement dependencies gained def-trf-space-etale-module-functors and
  def-sfb-scheme-space-zariski-restriction. The latter's public imports expose its
  two construction dependencies: the existing scheme-chart restriction and the
  representable étale scheme-test theorem that proves the identity chart is étale.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.

All already-recorded proof-dependency modules are imported with ordinary `import`;
statement dependencies have `public import`. The section-algebra-construction node and
fpqc-open-immersion-descent node currently have neither a lean record nor an upstream
closed audit; they occur in the proof docstring but have no module to import yet. They
are proof prerequisites only, not missing notions required to state this item.

Edge cases checked before writing and again against the final signature:

- Empty I: allowed. Its fpqc hypothesis forces empty T; a space over empty T is empty,
  hence a scheme, and the empty scheme satisfies the absolute ampleness condition.
- Empty X or empty affine open V: allowed, with the ordinary invertible module on the
  empty scheme and vacuous point condition in IsAmple; its underlying space is compact.
- Singleton identity cover: the two representations express the same scheme and the
  same module up to its canonical tensor identity isomorphism.
- General flat field extension, including inseparable extensions: allowed; no étale
  hypothesis appears on g, and tensor pullback is used for a, rather than étale-only
  restriction along a.
- Non-quasi-compact base or source: no absolute compactness is assumed. Only the
  inverse image of each affine base open is required to be compact by IsAmple.
- Infinite covers and independent index universe v: permitted. All schemes and chart
  modules stay in their existing universe u, with no forced equality of site object
  and morphism universes or coefficient enlargement.
- A trivial module on an arbitrary non-quasi-affine scheme is not made ample: the
  actual nonvanishing affine-neighbourhood condition remains in IsAmple.

Searches (all msearch calls used Q10 and this item's id):

- leanfinder: "Relative ampleness of a line module on an algebraic space descends
  along fpqc coverings including representability by schemes". Eight hits, on scheme
  morphism-property descent and related local-property results; no matching theorem.
- loogle: "IsAmple, AlgebraicSpace". Zero hits; unknown identifier IsAmple in service.
- msearch grep: "RelativeAmple|relative.*ample|fpqc.*[Aa]mple", AlgebraicGeometry.
  Zero Mathlib hits.
- leansearch: "Relative ampleness of invertible modules on algebraic spaces is fpqc
  local on the base". Eight results on generic scheme descent, affine locality and
  base-change properties; no matching algebraic-space ampleness theorem.
- rg in lean/WeilConjectures and lean/Sheaf for
  "RelativeAmple|[Rr]elative.*[Aa]mple|relativelyAmple|isRelativelyAmple" found scheme
  relative-ampleness results and the étale-only
  `AlgebraicSpace.representable_and_ample_of_etale_cover`. That theorem requires an
  étale cover and is one implication over a general space base, so it does not state
  this fpqc equivalence. Its source was read and its underlying site APIs reused.
- rg of this node id in lean/WeilConjectures: no hit. Searches of the proposed full
  declaration name in Mathlib, WeilConjectures and Sheaf found no existing declaration.

Original validation compiled the returned single-module presentation cleanly.
Repair validation compiles both construction and consumer separately through scompile.py;
the wrapper reports clean results for both files, with no errors or warnings. No theorem proofs were supplied.
No STATEMENT-DISPUTED flag or known mathematical node fault remains.

## Second reading by Q10

A separate in-thread rereading was made with the node and final Lean signature open;
this dispatcher explicitly forbids spawning another agent, so this is not claimed as
an independent worker review. Checked each binder and both sides against the mapping
above. The substantive check is that each local representing scheme has the full
IsPullback universal property, not just a commuting square, and that global schematicity
is expressed by IsIso a. Both sides use the same normalized tensor pullback of L and
absolute IsAmple on every affine inverse image. The index type is unrestricted, and
no properness or Noetherian assumption is introduced. The original semantic mapping was confirmed; return H2 required the construction-ownership
repair detailed below.
The maintainer's independent delivery review remains to be performed.

## Repair of return H2

Compared the retained packet with the returned module text and the current shared main
node. The original main theorem had no other semantic mismatch according to the independent
review. Rebased the node metadata on the current main copy, preserving every field other
than the authorized lean and stmt_deps delta. No direct Git operation was used.

H2 is repaired by a substantive module and node addition:
`def-sfb-scheme-space-zariski-restriction` now owns
`Sheaf.AlgebraicGeometry.SchemeSpaceZariskiRestriction`. The main theorem directly uses
its `schemeSpaceZariskiRestriction`, instead of reaching into the graded-evaluation
theorem module for its ancillary `evaluationZariskiRestriction` definition. Its imports
now publicly expose the definition module and privately import the graded-evaluation
module for the unchanged proof plan. The theorem node was removed from stmt_deps and
remains in proof_deps.

The repair uses the reviewer's permitted "state them anew" route, specialized through
the already-owned chart restriction. `schemeSpaceIdentityEtale T` is the actual identity
Yoneda chart, with its étaleness proof supplied by the existing scheme-test theorem.
`schemeSpaceZariskiRestriction T` is literally
`(schemeSpace T).schemeRestriction (schemeSpaceIdentityEtale T)`. Thus no chart-site
continuity theorem, new equivalence, context or underlying restriction functor is copied.
Unlike the old route through ordinary small étale modules, this directly restricts to
Zariski opens; both evaluate M on the same open subscheme, with the same regular-function
scalar comparison. No equality between these two presentations is assumed as a hypothesis.
The function has real data, no sorry, and works for every module, including non-quasi-coherent
modules and the empty scheme.

## New nodes

`def-sfb-scheme-space-zariski-restriction` defines the identity étale chart of a
representable space and canonical Zariski restriction of its module sheaves. Its source
is Stacks 03DX/03FH. Its Lean signature introduces S and T explicitly. The identity
chart binder has the actual representing scheme T; its scheme-test proof asserts
étaleness of the identity, not a hypothesis. The functor's domain is exactly
`(schemeSpace T).Modules` and its target is `T.left.Modules`. Its body specializes
`schemeRestriction`, so sections, restriction maps and scalar action have exactly the
node's formula. There are no extra assumptions or postponed theorems. Search results
are recorded verbatim from searches.jsonl for LeanSearch, LeanFinder and Mathlib grep;
DAG and project searches are also recorded. The ordinary-site construction node does
not supply this representable-space domain, and the generic chart-restriction node
requires a supplied chart; both are reused, not redefined. The graded-evaluation module
contains the old composite presentation but no definition node owns it, precisely the
ownership gap identified in the return. Blueprint ancestor search returned null, matching
the item's existing blueprint.from.node; the ancestry place and full via are preserved.

Additional reading of the repair: the identity chart has `yoneda.map (𝟙 T)` and the
same T.left as its underlying scheme. Its chart restriction evaluates the original M
at every open U composed with identity; map composition and ring maps are inherited
from the existing construction. Both occurrences in the main theorem use this functor,
so neither direction has changed its module. The left IsIso and right IsPullback, affine
quantifiers, existential invertibility proof and all fpqc hypotheses are preserved.
This is a more detailed in-thread second reading; the dispatcher still forbids other
agents, and no independent worker reading is claimed.

Repair compilation completed successfully through scompile.py for both delivered files,
including separate module-mode sandbox checks and named-module checks. The new definition
module has no postponed theorem, while the main theorem retains its sole sorry proof.

Repair dry run: deliver2.py --no-push passed compilation and server preflight, with
all five intended files staged and no unrelated files in the packet.
