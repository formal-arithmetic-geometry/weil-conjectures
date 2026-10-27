## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiAffineChartLimitTopology` states
`AlgebraicGeometry.Scheme.quasiAffineChartLimitTopology`, with its one proof `sorry`.
The helper `quasiAffineChartSectionDiagram` is a real composition of Mathlib
functors, not chosen data or an assumption on arbitrary maps. It belongs to the
same chart-limit construction and is listed in `lean.declarations`. No node
statement, dependency list, or proof plan was changed.

Source read: `literature/stacks-project/more-groupoids.tex`, Tag 0API,
`lemma-sits-in-functions`, especially the middle paragraph beginning with the
rings A_i and the final paragraph of cartesian squares. The six proof steps of
the node are reproduced in the theorem docstring, including the common-upper-bound
argument and the absence of any quasi-compactness requirement on W.

Hypotheses and objects, clause by clause:

- `Y : Scheme.{u}` is the scheme Y. `I : Type u`, `[PartialOrder I]`,
  `[Nonempty I]` and `hdir : Directed (· ≤ ·) (id : I → I)` express the small,
  nonempty directed partially ordered index set. The common index/ring universe
  follows the project's size convention for ring colimits.
- `U : I → Y.Opens` gives the actual ambient opens; their open subschemes are
  `(U i).toScheme`. `hU : Antitone U` says precisely U_k is contained in U_i
  when i ≤ k.
- `[hqa : ∀ i : I, (U i).toScheme.IsQuasiAffine]` is the quasi-affineness
  hypothesis. Mathlib's class includes compactness and the canonical immersion;
  its canonical map is an open immersion. This is equivalent to being a
  quasi-compact open subscheme of an affine scheme.
- The subtype `{x : Y // ∀ i : I, x ∈ U i}` is exactly E, with the inherited
  subspace topology, not the interior of an intersection of opens.
- `quasiAffineChartSectionDiagram Y U hU` has objects
  `Γ((U i).toScheme, ⊤)`. On i ≤ k its map is pullback of global sections along
  `Y.homOfLE (hU ...) : (U k).toScheme ⟶ (U i).toScheme`.
  The functor is constructed by taking the opposite of the inclusion of opens,
  then `Y.restrictFunctor.op`, `(Over.forget Y).op`, and `Scheme.Γ`.
  This uses global sections of the actual subschemes, not unrelated rings with
  extra isomorphisms.
- `c : Cocone ...` and `hc : IsColimit c` allow any specified colimit C with its
  coprojections: C is `c.pt`, r_i is `c.ι.app i`, and p_i is `Spec.map (c.ι.app i)`.
- The canonical j_i is `(U i).toScheme.toSpecΓ`, the unit of the affine adjunction
  corresponding to the identity on sections. Q_i is `Set.range` of this map.

Conclusions, clause by clause:

- `∃ t : C(E, Spec c.pt)` supplies the continuous map.
- The first conjunct gives p_i(t(x)) = j_i(x) for every index and every x in E.
- The next conjunct quantifies over every other continuous map t' with these
  same coordinates and concludes t' = t. Thus uniqueness concerns the specified
  continuous map, not just maps also satisfying the remaining conclusions.
- `Topology.IsEmbedding t` together with `Set.range t = ⋂ i, p_i ⁻¹' Q_i`
  states exactly a homeomorphism onto F with its subspace topology.
- For each i, `IsOpen (p_i ⁻¹' Q_i) ∧ IsCompact (p_i ⁻¹' Q_i)` states that
  each inverse image is a quasi-compact open in Spec C.
- For every `W : Y.Opens` with `(W : Set Y) ⊆ ⋂ i, (U i : Set Y)`, the image
  `t '' {x | x.val ∈ W}` is equated, for every i, to the inverse image under p_i
  of `j_i '' {x : (U i).toScheme | x.val ∈ W}`. These sets are precisely W viewed
  inside E and inside U_i. The same conjunct explicitly asserts openness of t(W).
  There is no compactness binder for W.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `AlgebraicGeometry.Spec`, `Spec.map`, and `Scheme.Γ`.
- `Mathlib.CategoryTheory.Limits.HasLimits` (and its imported Cones/IsLimit):
  `CategoryTheory.Limits.Cocone` and `IsColimit`. The node allows an arbitrary
  colimit cocone, so no choice of `colimit` is forced.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` and the scheme version
  of its unit, `AlgebraicGeometry.Scheme.toSpecΓ`. Read the adjunction's full
  definition and the unit's definition; no specialized replacement is needed.
- `Mathlib.AlgebraicGeometry.QuasiAffine`:
  `Scheme.IsQuasiAffine`, its compactness parent, separatedness instance, and
  `Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`. The open-immersion notion
  is the recorded `AlgebraicGeometry.IsOpenImmersion`, available transitively.
- `Mathlib.AlgebraicGeometry.Restrict`:
  `Scheme.Opens.toScheme`, `Scheme.restrictFunctor`, `Scheme.homOfLE` and
  their restriction/global-section descriptions supply the helper's real data.
- Proof import `Sheaf.Topology.FilteredSpectrumTopologicalLimit`:
  `AlgebraicGeometry.filteredSpectrumTopologicalLimit`, read with its full
  compatible-family homeomorphism and compact-inverse-image clauses.
- Proof import `Sheaf.AlgebraicGeometry.QuasiAffineOpenAffinizationSquare`:
  `AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isOpenImmersion`, read with
  both quasi-affine hypotheses and its identity-left-arrow pullback square.
  Both recorded proof dependency modules are imported privately as required.

Edge cases checked mathematically before writing:

- A singleton/constant system reduces to the canonical open embedding of its
  quasi-affine chart; F is its image and the image formula is the ordinary one.
- Empty ambient Y or an empty chart: E and F are empty; the ring colimit is the
  zero ring once the system reaches the empty chart. The unique empty-domain
  map and all empty image/open/compact clauses remain meaningful.
- An empty intersection E with no empty stage is allowed: no nonemptiness of E
  is assumed. Nonemptiness is imposed only on the specified index set.
- Quasi-affine opens such as affine 2-space minus the origin are permitted;
  neither the charts nor their inclusions are assumed affine.
- W may be empty or non-quasi-compact. Its point set is rendered as an ambient
  open restricted to the relevant subtype, with no compactness assumption.
- Nonseparated Y is allowed; only its charts are quasi-affine. No condition on
  the field, characteristic, reducedness, or a chosen base scheme is introduced.

Searches for an existing statement (2026-10-23):

- `msearch.py ... leanfinder` with query
  "A directed intersection of quasi affine open subschemes is homeomorphic to
  the intersection of chart images in the spectrum of the colimit of section rings"
  returned eight hits, including directed affine covers, affine transition
  limits, and affine-Zariski section colimits. None states this directed
  intersection topology together with arbitrary ambient-open images.
- `msearch.py ... loogle '"IsQuasiAffine", "toSpecΓ"'` returned the canonical
  open-immersion instance, which is used as a dependency, not duplicated.
- `msearch.py ... grep
  'isPullback_toSpecΓ|instIsOpenImmersionToSpecΓ|chartLimit|chart_limit'
  AlgebraicGeometry` found only Mathlib's affine-morphism pullback result and
  its use. That result requires affine transition maps, absent in this node.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, chartLimit/chart_limit, and
  quasi-affine limit/intersection terminology found only the parent
  `IntersectionCanonicalAffineEmbedding` discussion. Its statement is about
  a ringed-subspace embedding into the spectrum of its own section ring and
  does not give this arbitrary specified colimit/coordinate/image formula.
- Exact-name searches for `quasiAffineChartSectionDiagram` and
  `quasiAffineChartLimitTopology` in Mathlib, upstream, Sheaf and the upstream
  declaration index found no existing declarations.

Validation: `scompile.py Q140 lem-a1-quasi-affine-chart-limit-topology <module>`
compiled both the sandbox and library module variants cleanly. All variables and
universes are explicit; `autoImplicit` is disabled. The only postponed proof is
`quasiAffineChartLimitTopology`; the diagram definition has real data. No
STATEMENT-DISPUTED flag or statement correction is needed.

## Second reading by Q140

Fresh local rereading with the node and final Lean file open confirmed all
hypotheses and clauses listed above. In particular the intersection is a subtype
with its subspace topology; the colimit cocone is arbitrary; the restriction
arrows are constructed; the embedding and range equality together give the
homeomorphism onto exactly F; uniqueness quantifies over every continuous map
with the coordinate equations; and the W-image equality holds for every i
without any compactness condition on W. No mismatch or statement change was
found. This is a local self-check, not a claimed independent-agent review:
the dispatch brief prohibits starting other agents and assigns the independent
reading to the maintainer after delivery.
