## Worker report

The module `Sheaf.AlgebraicGeometry.NagataQCOpenDescent` defines
`AlgebraicGeometry.nagataQCOpenDescent`, the chosen finite-stage model. Its data is a
computation, with no `sorry`: the result includes the selected stage, its inequality above
the base stage, and the union of transported basic opens. The choices preceding that
computation are explicit inputs, rather than an opaque selection of a compact open from
Mathlib's general existence theorem. No node statement or dependency list was changed.

Hypotheses and clauses, in the order of the node:

- A directed index set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Scheme and index universes are the same, as required by the
  project convention. The opposite preorder category encodes the inverse system.
- The inverse system and specified limit are `D : Iᵒᵖ ⥤ Scheme`, `c : Cone D`, and
  `_hc : IsLimit c`. The transition-affineness hypothesis is the instance quantifying
  over every morphism `t` of `Iᵒᵖ`.
- The base stage is `i₀`, the base-stage scheme is `Y₀`, and its structural map is `p`.
  The recorded `baseChangeDiagram D p` and `baseChangeCone D c p` give exactly the
  schemes and maps of the base-changed system. A stage `j ≥ i₀` is
  `Over.mk (homOfLE hj).op`; its object is `pullback p (D.map (homOfLE hj).op)`.
- Quasi-compactness and quasi-separatedness of `Y₀` are `[CompactSpace Y₀]` and
  `[QuasiSeparatedSpace Y₀]`. The parenthetical sufficient conditions on the original
  base are examples, not additional hypotheses.
- The quasi-compact open is `W : (baseChangeCone D c p).pt.Opens`, with `_hW` stating
  compactness of its underlying set. Being open is built into `Opens`.
- A chosen finite affine cover is `m : ℕ`, `U : Fin m → Y₀.Opens`, `_hU` asserting
  `IsAffineOpen (U a)`, and `_hcover : iSup U = ⊤`.
- The inverse-image chart at infinity is
  `pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ U a`. At a finite stage it is
  `pullback.fst p (D.map (homOfLE hj).op) ⁻¹ᵁ U a`. These are genuine inverse images
  under the base-change projections; neither a new notion nor an arbitrary map is used.
- `r : Fin m → ℕ` and `f` give the finite families of sections on the infinite charts.
  `_hpresentation` is exactly `W ⊓ Uinf = ⨆ k, Y.basicOpen (f a k)` for each chart.
  Mathlib's `Scheme.basicOpen` accepts a section over any open and returns its basic
  open in the ambient scheme, so no image or extension of sections is hidden here.
- The chosen finite-data stages are `stage : Fin m → I`, with `ha : ∀ a, i₀ ≤ stage a`.
  `lift` has the exact section ring of the finite inverse-image chart as its codomain.
  `_hlift` states that the limit projection pulls each lift back to `f a k`, using
  `Scheme.Hom.appLE` and the named limit-chart compatibility lemma.
- The section-colimit and finite-data assertions justify obtaining this chosen family:
  `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` applies to the affine chart limits,
  and `CommRingCat.exists_finite_data_stage` applies with zero equations on the upper
  tail of the directed set. These assertions are not extra data of the definition and
  are not reproved here. Chartwise compactness follows from the affine limit projection
  and quasi-separatedness, as in the node, and justifies the finite presentations.
- The chosen upper-bound operation has inputs `boundBase`, `d`, `hd`, and `order`,
  exactly the independent base point, selected pair bounds, their inequalities, and
  auxiliary linear order of `def-nagata-directed-finite-upper-bound`.
  In the body, `F = insert i₀ (Finset.univ.image stage)` and
  `w = directedFiniteUpperBound boundBase d order F`. Thus the returned index is the
  prescribed `u({λ₀} ∪ {λa})`, including an arbitrary selected base point for `u`.
- `le_directedFiniteUpperBound` supplies `hw` and `hwa`. Each transition `t a` is the
  actual morphism of `Over (op i₀)` from the selected stage to `stage a`; the equality
  in `Over.homMk` uses uniqueness of morphisms in the preorder category.
- The transported section is `((baseChangeDiagram D p).map (t a)).appLE ... (lift a k)`.
  The returned open is the double supremum of its `Scheme.basicOpen`, the stated
  union over `a,k`. The `PSigma` output permits retaining the stage inequality, whose
  type is `Prop`, alongside the open. No extra property is asserted as an output.
- Dependence on all choices is preserved by the explicit arguments. Eventual agreement
  is supplied by `pqf-lem-limit-qc-open-descends`, not baked into the definition as a
  new theorem: its recorded `exists_map_preimage_eq_map_preimage` gives eventual equality
  after moving two witnesses to a common stage. Its same-stage signature was read.

Dependency declarations inspected:

- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `AlgebraicGeometry.baseChangeDiagram`, `baseChangeCone`, their projection compatibility
  lemmas, with full definitions and docstrings. This module is imported and its
  constructions are used throughout.
- `Sheaf.Order.DirectedFiniteUpperBound`: `directedFiniteUpperBound` and
  `le_directedFiniteUpperBound`, full declarations and docstrings; imported and used.
- `Sheaf.RingTheory.FilteredColimitFiniteData`: `CommRingCat.exists_finite_data_stage`,
  full signature and proof docstring. Its role is the existence of the chosen inputs,
  so no otherwise-unused import was added to the definition module.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`, full signature and proof docstring.
  The definition accepts the prescribed limiting cone; this theorem supplies the
  affine-projection/chart-limit facts used to obtain the choices.
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `nonempty_isColimit_Γ_mapCocone`, `exists_preimage_eq`,
  `exists_map_preimage_eq_map_preimage`, `isLimitOpensCone`, full signatures/docstrings.
  These are available through the used upstream affine-transition module and provide
  the stated existence and independence facts.

Two auxiliary named theorems, both with `sorry`, provide the chart inclusions needed by
`appLE`: `nagataQCOpenDescent_chart_le` and
`nagataQCOpenDescent_limit_chart_le`. Their docstrings give complete elementary proofs:
compose the appropriate base-change projection with the chart projection, use the
recorded projection-compatibility equality, and take inverse images. They postpone only
these well-definedness proofs. All theorem proofs are `sorry`, including these two;
no mathematical theorem is proved in this stage.

Edge cases checked: if `m = 0`, the cover hypothesis forces `Y₀` to be empty, the finite
set of stages still contains `i₀`, and the returned open is the empty supremum. If a
chart has `r a = 0`, its presentation says the intersection is empty and it contributes
nothing. The empty `W` is allowed. Repeated chosen stages are removed by the Finset
image, without requiring commutativity or associativity of `d`. The auxiliary linear
order is passed as data and does not replace the directed preorder instance. No bound
on characteristic, cardinality of schemes, or a nonempty affine cover was added.

Searches made:

- LeanFinder through `msearch.py`: “chosen finite-stage model of a quasi-compact open in
  a base-changed inverse system of schemes”: 8 hits, including `exists_preimage_eq`,
  morphism descent and preimage-inclusion results. None defines this selected-cover,
  selected-lift, selected-upper-bound construction.
- Loogle through `msearch.py`: `AlgebraicGeometry.exists_preimage_eq,
  AlgebraicGeometry.baseChangeDiagram`: 0 hits; unknown identifier for the upstream
  `baseChangeDiagram` (subsequently inspected directly in its recorded source).
- Mathlib grep through `msearch.py`: `qcOpenDescent|qc_open_descent|finite.*stage.*open`,
  subdirectory `AlgebraicGeometry`: 0 hits.
- LeanSearch through `msearch.py`: “chosen finite stage witness of a quasi compact open
  subscheme in an inverse limit”: service unavailable, Internal Server Error.
- Direct `rg` for `nagataQCOpenDescent|qcOpenDescent|qc_open_descent` across Mathlib,
  `WeilConjectures`, and project `lean/Sheaf`: no preexisting declaration.
- `grep -rn def-nagata-qc-open-descent` in `WeilConjectures`: no hit.
  `tools/lean_names_upstream.py show def-nagata-qc-open-descent`: no attached declaration.

No statement dispute, new definition node, or unusable dependency was found. The blueprint
file recorded in `source.document` is not materialized in this read-only checkout; the
node's complete repaired construction and source metadata were read, together with all
recorded dependency source modules. The source's existing general descent theorem does
not prescribe these choices and therefore is not an exact existing-definition match.

Validation: server single-file compile passed with no errors or warnings. The retained
proof hypotheses are prefixed `_` because the formula uses their chosen data rather
than inspecting the certificates. The required delivery dry run printed `OK (dry run)`: clean server compile and preflight
pass except for the independent second reading, which the second reader supplies. Nothing
was pushed. The first preflight identified the signature-record prefix `noncomputable`;
the record now starts at the `def` keyword, exactly as the signature reader requires.

## Second reading by P1

The node introduces a directed index type `I` with `[Preorder I]`, `[Nonempty I]`,
and `[IsDirected I (· ≤ ·)]`, an inverse system `D : Iᵒᵖ ⥤ Scheme` with a specified
limit cone `c`, affine transition maps, a base stage `i₀`, a scheme `Y₀` and map `p`,
quasi-compact and quasi-separated hypotheses on `Y₀`, a quasi-compact open `W` in
the base-changed limit, a finite affine cover `U : Fin m → Y₀.Opens`, finite basic-open
presentations and lifts at stages `stage a ≥ i₀`, and a selected common upper bound.
The Lean signature renders these as the binders of `nagataQCOpenDescent`; the output
is `Σ' w, Σ' hw : i₀ ≤ w, ...Opens`, namely the selected stage, its base-stage
inequality, and the union of transported basic opens. The transition and limit chart
compatibility inputs are rendered by `nagataQCOpenDescent_chart_le` and
`nagataQCOpenDescent_limit_chart_le`. The choice-dependence clause is documented
for the recorded eventual-equality dependency and is not asserted as an extra field
of this definition.

One mismatch was found. The original Lean signature introduced an independent
`boundBase : I`, so its selected upper bound could use a base point different from the
node's prescribed `i₀`. The source construction explicitly sets
`u({i₀} ∪ {stage a})`; I removed `boundBase` and changed all three calls to
`directedFiniteUpperBound`/`le_directedFiniteUpperBound` to use `i₀`. The node's
recorded signature was updated verbatim to match.

Edge cases were checked: `m = 0` is permitted (the cover then forces an empty base
scheme), `r a = 0` contributes an empty supremum, `W = ⊥` is allowed, repeated stages
are removed by `Finset.image`, and no characteristic, finiteness, or nonempty-cover
assumption is added. Universes use the same `u` for `I` and schemes, as required for
the inverse-system and limit declarations.

Searches were reviewed: LeanFinder/Loogle/grep/LeanSearch searches and direct `rg`
find no existing declaration for this selected construction. The dependency declarations
in the worker report were opened; their signatures match the notions used here, and no
new node or dependency module is needed.
