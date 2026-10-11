## Worker report

The module `Sheaf.AlgebraicGeometry.EventuallyAffine` states `AlgebraicGeometry.eventually_affine`, the relative eventual-affineness lemma of Stacks Tag 09ZM. The base scheme `T` is represented by `CompactSpace T` and `QuasiSeparatedSpace T`; each stage has the corresponding instances. The inverse system is `D : Iᵒᵖ ⥤ Scheme`, with directed nonempty `I`. The affine-transition hypothesis is the instance `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]`. A limit cone `(c,hc)` supplies `Z` and its projections. The maps `h_i` are the structure maps to `T`; `h_i_compat` gives compatibility with every transition, and `h_induced` identifies their composites with the induced map `h : c.pt ⟶ T`, assumed affine by `[IsAffineHom h]`. The conclusion is an index `i₀` after which every `h_i` is affine.

The Lean binders render each hypothesis clause directly: directed/nonempty index, qcqs base and stages, affine transitions, limit cone, compatible structure maps, induced affine limit map. The conclusion `∃ i₀, ∀ i, i₀ ≤ i → IsAffineHom (h_i i)` renders “for every `i ≥ i₀`, `h_i` is affine.” `hc` is the limit witness required by the node's phrase “let Z be its limit”; it is not used to weaken the conclusion.

Dependencies used: `def-weil-pbc-scheme-conventions` (its scheme/morphism conventions are rendered by Mathlib's `Scheme`, `CompactSpace`, `QuasiSeparatedSpace`, and `IsAffineHom`); `pqf-def-affine-morphism` (`AlgebraicGeometry.IsAffineHom`); `lem-weil-pbc-limit-affine-transition` (`Sheaf.AlgebraicGeometry.LimitAffineTransition`, declaration `AlgebraicGeometry.exists_limit_affine_transition`, for the limit cone notion). The module imports the latter and the Mathlib morphism/topology modules.

Edge cases checked: `I` is explicitly nonempty; finite affine covers may be empty when `T` is empty, and the theorem's hypotheses allow an empty base; no stage or scheme is assumed nonempty; arbitrary universes are tied to the scheme universe `u`; `i₀` may be any index and the directed order is unchanged.

Searches made before writing: `msearch.py H1 lem-weil-pbc-eventually-affine leanfinder` for relative eventual affineness (no exact project declaration); `msearch.py ... loogle "AlgebraicGeometry.IsAffineHom, CategoryTheory.Limits.IsLimit"` (only absolute affine-limit lemmas); `msearch.py ... grep "IsAffineHom.*exists|09ZM"` over Mathlib (no relative Tag 09ZM theorem); `rg -n "eventually_affine|IsAffineHom"` over `WeilConjectures` and existing `lean/Sheaf` (no exact declaration). The dependency declarations and their full signatures were read from their node records and source modules.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the Stacks 09ZM source. The Lean theorem includes the nonempty directed index, qcqs hypotheses on `T` and every `Z_i`, affine transition maps, the specified limit cone and projections, compatible structure maps `h_i`, the induced affine limit map, and exactly the eventual-affineness conclusion. The dependency declarations were checked against their node records: `IsAffineHom` is the affine-morphism notion, and `exists_limit_affine_transition` supplies the limit cone and affine projections. No hypothesis or conclusion was added beyond making the node's “structure maps” and “induced map” explicit. Empty `T`, arbitrary stages, and arbitrary universe `u` remain permitted.

## Second reading by H1

Read the repository node, sandbox node and Lean module independently. The local
repository has no Stacks checkout; read the available source checkout at
`/home/ubuntu/c1-stacks-review/limits.tex`, lines 890–911, and its tag table
(09ZM = limits-lemma-eventually-affine), as well as Categories Definition 00D3.
The source assumes schemes, a nonempty directed preorder, affine transitions,
qcqs base and stages, and an affine induced limit morphism. No field,
Noetherianity, finite presentation, or characteristic hypothesis is assumed.
The parenthesis about a finite morphism in the source proof is an unnecessary
stronger example; the statement and argument only require affineness.

Object/hypothesis/conclusion inventory, with the Lean rendering and verdict:

- Base scheme T: `{T : Scheme.{u}}`; qcqs:
  `[CompactSpace T] [QuasiSeparatedSpace T]`. Exact. CompactSpace expresses
  quasi-compactness without a Hausdorff assumption; QuasiSeparatedSpace is
  compactness of intersections of compact opens, the scheme qcqs notion.
- Nonempty directed set I: `{I : Type w} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Exact, including the Stacks 00D3
  preorder convention. Changed its universe from u to independent w so the
  statement does not restrict the size of the indexing set to the scheme universe.
- Inverse system Z_i and its transitions: `(D : Iᵒᵖ ⥤ Scheme.{u})`, with
  Z_i = `D.obj (op i)`; an arrow `op i' ⟶ op i` means i ≤ i'. Functor laws
  give identity and composition laws. Exact; no alternate scheme notion.
- Every Z_i qcqs: `[∀ i : I, CompactSpace (D.obj (op i))]` and the analogous
  `QuasiSeparatedSpace` binder. Exact, with no nonempty-stage assumption.
- Affine transition maps: `[∀ {i j : Iᵒᵖ} (f : i ⟶ j),
  IsAffineHom (D.map f)]`. Exact. Opened pqf-def-affine-morphism and
  Mathlib.AlgebraicGeometry.Morphisms.Affine:47–48: its field requires the
  inverse image of every affine open to be affine, precisely the node definition.
- Limit scheme Z, projections p_i: `(c : Cone D) (hc : IsLimit c)`, with
  `Z = c.pt` and `p_i = c.π.app (op i)`. Exact actual limit cone; its naturality
  is projection compatibility. Opened the recorded dependency
  `AlgebraicGeometry.exists_limit_affine_transition` and its entire signature
  in `Sheaf.AlgebraicGeometry.LimitAffineTransition`: it uses these same
  Mathlib Cone/IsLimit notions, affine projections, opensCone and opensDiagram,
  and a spectrum-of-colimit description in the affine-stage case. This theorem
  supplies existence; the present statement correctly takes an arbitrary
  specified limiting cone and does not replace it by unrelated objects.
- Structure maps h_i: `(h_i : ∀ i : I, D.obj (op i) ⟶ T)`;
  `h_i_compat : ∀ {i i' : I} (f : op i' ⟶ op i),
  D.map f ≫ h_i i = h_i i'`. Exact inverse system over T.
- Induced map h: `(h : c.pt ⟶ T)` and
  `h_induced : ∀ i : I, c.π.app (op i) ≫ h_i i = h`. Exact equations,
  in categorical composition order; not an unconstrained map.
- Affine h: `[IsAffineHom h]`. Exact same notion as the transitions; it is
  a substantive property, not a hypothesis true of all scheme morphisms.
- Conclusion: `∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsAffineHom (h_i i)`.
  Exact order of quantifiers and every sufficiently late structure map;
  neither only one stage nor affineness of Z_i absolutely.

Opened def-weil-pbc-scheme-conventions and its convention-only lean record:
this node introduces no new definition, and its leaves give the Mathlib
scheme/morphism notions used here. No new definition nodes or dependency
modules are necessary. There is no statement_change in this delivery, and
no correction to the natural-language node statement.

Edge cases: empty I is excluded by the source and Lean alike. Empty T, empty
Z_i and empty limit are allowed; no Nonempty instance on a scheme is required.
For an empty T the affine cover has n = 0 and any index supplies the common
bound. The zero ring and its empty spectrum, all characteristics, and arbitrary
scheme universe u remain covered. Independent universe w now permits indexing
sets both smaller and larger than u; the specified limit witness is retained,
so no large-limit existence assumption is introduced. No test-algebra universe
or vacuous quantification occurs. There is no numerical n binder to constrain.

Independent searches (different phrasing from the worker):
- `msearch.py ... leanfinder "affine morphism from inverse limit to fixed scheme
  descends to affine structural morphism at sufficiently large indices"`:
  eight hits, including isAffineHom_π_app, exists_isAffine_of_isLimit and
  exists_isAffineOpen_preimage_eq. Opened exists_isAffine_of_isLimit:1040:
  it concludes an affine stage scheme assuming an affine limit scheme, the
  absolute 01Z6 case, not this relative statement. Projection affineness is
  also a different conclusion.
- `msearch.py ... loogle '"IsAffineHom", "IsLimit"'`: zero hits.
- `msearch.py ... leansearch "inverse system over a fixed base scheme affine
  limit morphism eventually affine stage structure maps"`: service unavailable
  (Internal Server Error); recorded as unavailable, not as a negative match.
- Direct rg for `IsAffineHom`, `affine.*limit`, `limit.*affine`,
  `eventually_affine`, `09ZM`, and existential/eventual IsAffineHom signatures
  across Mathlib algebraic geometry, WeilConjectures and repository lean/Sheaf;
  also checked dag/lean_names_upstream.json. No existing exact relative lemma.
  The project LimitAffineTransition is existence/projections/restriction,
  FiniteSurjectiveAffineTarget has additional finite/surjectivity hypotheses,
  and the source library hits concern different limits or affineness descent.

Repairs: independent index universe; added the conventional copyright header;
expanded the theorem docstring to the node's five proof steps, including the
qcqs preimages, restricted limit cone, propagation to every later stage and
empty-cover case, with all supporting node names. Removed the unused project
existence-theorem import and redundant direct Mathlib imports; a single
Mathlib.AlgebraicGeometry.AffineTransitionLimit import supplies the actual
notions and the absolute lemma referenced in the docstring. No private
notions, data definitions, auxiliary proved statements, or extra axioms were
added. The only proof remains `by sorry`. Updated lean.statement verbatim
from the repaired signature; all universes and variables are explicitly bound.
