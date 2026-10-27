## Worker report

The item is stated by `AlgebraicGeometry.FormalOpen.adicFormal_open_gluing` in
`Sheaf.AlgebraicGeometry.AdicFormalOpenGluing`. Its only proof is `sorry`.
The original node statement, proof and proof dependencies are unchanged.
The statement dependencies gain the new definition node described below.

Hypothesis and clause correspondence (names below are in `AlgebraicGeometry.FormalOpen`):

- A locally topologically ringed space is an existing `RingedSpace` with a
  `SectionTopology`, `IsTopologicalSheaf`, and local stalk rings. The topological
  sheaf axiom includes the initial topology for restrictions to every open cover;
  together with the underlying sheaf axiom this is the subspace topology on
  matching tuples. It does not merely assume continuity of restrictions.
- `IsAdic` requires actual open charts from the recorded `adicFormalSpec R K`,
  complete for K, using the recorded `adicFormalSectionTopology R K`. Thus the
  quotient-limit section topology is retained, not replaced by discrete rings.
- `IsNoetherian` includes the recorded `IsNoetherianAdicFormalScheme` finite atlas
  convention, together with compatibility of the supplied topology with local
  complete Noetherian formal-spectrum charts. K is finitely generated and
  `IsAdicComplete K R` includes completeness and separatedness.
- Formal morphisms are `IsMorphism`: local homomorphisms on every stalk and
  continuous homomorphisms on every section ring. No specified ideal of
  definition has to be preserved, and no algebraization is imposed.
- The finite family, including the empty family, is `D.data.U` with `D.finite`.
  Every piece satisfies `D.noetherian`. Its index is `Type u`, with no
  `Nonempty` or positive-cardinality requirement.
- Overlaps are the objects `D.data.V (i,j)` and the open immersions
  `D.data.f i j`. This is the coordinate-free presentation of an open subset;
  no affine or separatedness assumption is added. `D.openMap` supplies the
  topological open-isomorphism condition. `D.transition` requires continuous
  local transition maps. Mathlib's `GlueData.t_inv` identifies the reverse
  transition as its inverse, so both directions are continuous.
- `SheafedSpace.GlueData.toGlueData` supplies the standard diagonal identity,
  inverse identities, identification of triple overlaps, and cocycle condition.
  Its diagonal overlap is canonically isomorphic to the full piece, rather than
  syntactically equal to it. This is the usual equivalent gluing-data convention.
- The glued ringed space is the actual `D.data.toGlueData.glued`, not an
  arbitrary chosen object. The conclusion supplies its section topology τ.
  `Realizes` gives `IsNoetherian`, covering formal open immersions, the transition
  equality, and `IsPullback` for each overlap square. The last two conditions
  identify precisely the indicated overlaps, including their sheaf maps.
- `CoverDescent` first quantifies over every adic formal target, without assuming
  it Noetherian or finitely covered. `CompatibleMaps` is equality on overlaps;
  testing all common maps is equivalent to testing the overlap pullback. The
  `∃! g` is unique gluing as a continuous local morphism with all restrictions
  prescribed. The next conjunct explicitly states locality of morphism equality.
- `IdealSheaf` is actual section ideals with restriction stability and local
  membership. It is not an abstract ideal object up to isomorphism and is not
  an arbitrary family of stalk ideals. Its `stalk` is the directed supremum
  of neighborhood ideal images.
- `IdealSheaf.IsCoherent` means locally finite sections generate every stalk
  ideal. On a Noetherian formal affine, the resulting subsheaf is exactly the
  completed-localization sheaf of the finitely generated ideal. It does not
  require sections on every nonaffine open to have one set of global generators.
- `CompatibleIdeals` and `SamePullback` impose equality of the restricted stalk
  ideals; equality of ideal subsheaves is detected on stalks. `PullsBack` uses
  extension along the actual stalk homomorphism of each open immersion.
- The ideal part of `CoverDescent` concludes `∃! J : IdealSheaf X`, with coherence
  and the prescribed restrictions. This is equality uniqueness of actual ideal
  subsheaves. The same J is an ideal of definition whenever all local ideals
  are, and is open whenever they all are.
- `IdealSheaf.IsOpen` is locally openness of the section ideal on formal affine
  charts. `IsDefinition` requires locally an open ideal whose powers generate
  exactly the given topology (`τ U = (I.ideal U).adicTopology`). No exponent
  uniform over a non-quasi-compact open is required. In this Noetherian setting
  ideals of definition are coherent; this condition is included in the predicate.
- `StableDescent` quantifies over every formal open subspace W of the gluing,
  states W remains Noetherian adic, and states `CoverDescent` for every cover
  of W. This includes restricted covers and all their refinements. Their glued
  maps and ideal subsheaves are the unique ones with the same restrictions;
  applying uniqueness on a common refinement gives the canonical comparison
  and its compatibility for further refinement. No independently chosen map
  or comparison is substituted for those determined by restrictions.
- The final `∀ X σ v` compares every other `Realizes` datum with the actual
  gluing by `∃! e`, with continuous local hom and inv and the equation on every
  chart. Thus uniqueness is up to unique isomorphism respecting gluing maps.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.AdicFormalGeometry`: `adicFormalSpec`,
  `IsAdicFormalAffineOpen`, `IsNoetherianAdicFormalScheme` (record of
  def-per-adic-formal-geometry). The ringed-space construction is reused intact.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and
  `isNoetherianRing_iff_ideal_fg` (def-weil-pbc-noetherian-ring).
- `Sheaf.AlgebraicGeometry.AdicPrincipalChartData`: `adicFormalSectionTopology`
  (def-per-adic-principal-chart-data, a dependency of the new definition node).
- `Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing`:
  `SheafedSpace.GlueData` and the actual categorical glued ringed space.
- Proof-only imports: `Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement`
  and `Mathlib.RingTheory.AdicCompletion.Completeness`. The existing proof node
  lem-per-topological-ring-sheaf-open-descent has no Lean record, so there is
  no module to import yet. The full intended argument remains in the theorem
  docstring, including that dependency; it is not assumed as a new hypothesis.

Edge cases checked before drafting: empty index type and empty pieces; empty
open cover of the empty open; the one-element section ring on the empty space;
zero and unit ideals, including empty formal spectra; singleton covers; identical
pieces and diagonal overlaps; nonaffine overlaps; arbitrary open restriction;
refinement by an arbitrary open cover; non-Noetherian adic targets. There is no
`Nonempty`, nonzero-ring, positive-atlas-size, affine-overlap or preserved-ideal
binder. All universes and variables are explicitly bound, with both automatic
implicit options disabled.

Searches performed using msearch.py and source reads:

- LeanFinder: "Open gluing of Noetherian adic formal schemes with coherent ideals
  and continuous local morphisms" returned ordinary scheme gluing declarations,
  including `Scheme.GlueData.gluedScheme`, not formal topological descent.
- Loogle: `"GlueData"` returned `CategoryTheory.GlueData` and its variants.
- LeanSearch: "Sheaves of topological rings and continuous local morphisms glue
  on open covers" returned section-gluing lemmas for existing sheaves and
  `TopCat.GlueData.ofOpenSubsets`, not this theorem.
- Mathlib grep: `TopologicalRingSheaf|TopologicallyRinged|FormalScheme|\bSpf\b`
  returned no hits. A second grep for
  `SectionTopology|IsTopologicalSheaf|FormalOpen|TopologicallyRinged` returned none.
- LeanFinder for topological enhancements of adic formal ringed spaces returned
  ring adic topology, `RingedSpace`, and `LocallyRingedSpace`, not the enhancement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the item-id search in
  `lean/WeilConjectures`, found no existing declaration of the item. Source reads
  found the formal section topology in AdicPrincipalChartData and reuse it.
  RigRegularFormalGeometry's `FormalIdeal` is a family of stalk ideals without
  subsheaf locality or section topologies; it is not a duplicate of `IdealSheaf`.
- DAG searches and `blueprint_refs.py search` found no existing topological
  enhancement node; the formal geometry and principal section data are reused.
  The ancestor is lem-per-artin-gabber-affine-curve, whose current blueprint
  statement and proof were read under literature/blueprint/latest.

Validation: both delivered modules compile separately in dependency order through
scompile.py, with no errors or warnings. No theorem was proved, no data contains
sorry, and no live source or launcher script was edited. There is no known
statement fault or STATEMENT-DISPUTED issue.

## New nodes

`def-per-topological-formal-open-data`, module
`Sheaf.AlgebraicGeometry.TopologicalFormalOpenData`, supplies the missing
section-topology enhancement of the recorded ringed-space geometry, its
continuous local maps, actual ideal subsheaves, and the cover/gluing predicates
used to state all clauses compactly. Its main declaration is
`AlgebraicGeometry.FormalOpen.GlueData`; all 20 declarations are listed in
lean.declarations. Every definition has real data, no theorem and no sorry.
It reuses the formal spectrum and section topology; it neither constructs a
second formal spectrum nor redefines Mathlib gluing. Sources are Stacks 0AHY,
01JA and 00AL and the item's explicit local ideal convention. The recorded
LeanSearch, Loogle/LeanFinder, Mathlib grep, project grep and DAG searches found
no existing node or declaration for this enhancement. This is §1(A), not a
replacement of the usable ringed-space dependency. The new node has empty
import_flags because the former target thm-weil-final reaches the item.

## Second reading by Q85

Clause-by-clause reading of `adicFormal_open_gluing` and the new node module
`TopologicalFormalOpenData` against the node, Stacks 0AHY/01JA/00AL. (The worker's own
reread had strengthened `IsNoetherian` to topology-compatible Noetherian charts and removed
a redundant `IsTopologicalSheaf` premise in `StableDescent`; both changes are kept.)

1. Locally topologically ringed space: `RingedSpace` + `SectionTopology` with
   `IsTopologicalSheaf` (topological rings, continuous restrictions, initial topology for
   every cover) + local stalks in `IsAdic`. Correct (0AHY equalizer condition).
2. Noetherian adic formal scheme, finite Spf cover: `IsNoetherian` = `IsAdic` ∧ recorded
   `IsNoetherianAdicFormalScheme` (finite `Fin n` atlas, n = 0 allowed) ∧ local charts
   `adicFormalSpec R K` with recorded `adicFormalSectionTopology`, R Noetherian, K FG,
   `IsAdicComplete` (complete + separated). Correct; the topology on Noetherian formal affines
   is intrinsic, so the two atlases are compatible.
3. Morphisms continuous and local: `IsMorphism` (IsLocalHom on stalk maps, continuity of
   every `c.app`). Correct; no preserved ideal of definition.
4. Finite family incl. empty: `D.data.J : Type u`, `D.finite`, no Nonempty. Overlaps open:
   `f i j` open immersions (`D.openMap` fixes `overlapTopology` from the piece topology, so no
   free data). φ_ij iso, φ_ii = 1, φ_ji = φ_ij⁻¹, triple overlaps and cocycle: Mathlib
   `SheafedSpace.GlueData` fields (f_id, t_id, t_inv, t', cocycle); `D.transition` gives
   continuity both ways. T_ii = T_i up to canonical iso (`f_id` IsIso) — standard convention.
5. Existence: the actual `D.data.toGlueData.glued`; ∃ τ with `Realizes` (Noetherian, covering
   formal open immersions, transition equality, cartesian overlap squares = precisely the
   indicated overlaps). τ is not an arbitrary choice: the uniqueness clause applied to
   (glued, τ′, ι) forces 𝟙 continuous both ways, so τ = τ′.
6. Unique up to unique iso respecting gluing maps: final `∀ X σ v, Realizes → ∃! e`,
   continuous local hom/inv, `ι i ≫ e.hom = v i`. Correct.
7. Morphisms glue uniquely to any adic formal target: `CoverDescent` clause 1, target only
   `IsAdic` (broader than node: stronger, still true). Compatibility through all cones is
   equivalent to equality on the overlap pullback. Equality local on any formal open cover:
   clause 2 for the gluing cover, and `StableDescent` with W = glued, w = 𝟙 for every cover.
8. Coherent ideals glue uniquely as ideal subsheaves: `IdealSheaf` = actual section ideals with
   restriction and locality; `∃! J` coherent with `PullsBack` on each piece. Ideal subsheaves are
   determined by stalks (germ argument + locality) and open-immersion stalk maps are isos, so the
   uniqueness is equality of subsheaves; any J′ with these pullbacks is automatically coherent,
   so restricting ∃! to coherent J loses nothing. `IsCoherent` (local finite generation of
   stalk ideals) = completed-localization sheaf of an FG ideal on Noetherian formal affines.
9. Ideals of definition / open ideals glue: the two implications inside the ∃!. `IsDefinition`
   = coherent ∧ locally on formal affines open with `τ U = adicTopology`; `IsOpen` = locally
   open section ideal. Local predicates as in the node's Step 6; no uniform exponent.
10. Commute with restriction and refinement: `StableDescent` (every formal open W is Noetherian
   adic and descent holds for every cover of W); comparisons follow from the stated
   uniqueness clauses and from the theorem itself applied to the restricted datum. Acceptable
   rendering of the node's sentence. Overlaps not affine: no affine/separated hypothesis.

Edge cases: empty J (glued = ∅, n = 0 atlas, one-element ring on ⊥, indiscrete = any topology);
empty covers of ⊥; arbitrary non-affine overlaps; non-Noetherian targets; universes all `u`
(J, spaces, CommRingCat.{u}, cover indices) — same convention as Mathlib gluing, no extra
restriction. Searches: no `SectionTopology`/topological-sheaf/ideal-subsheaf notion in
lean/Sheaf or lean/WeilConjectures besides the reused `adicFormalSectionTopology`;
`FormalCompletionGeometry.HasInvertibleIdealOfDefinition` is a different notion; Mathlib has
only ordinary (locally) ringed-space gluing. New node: all 20 declarations real data, Stacks
docstrings and blueprint tags, no sorry. Theorem: proof `sorry`, docstring carries Steps 1–8.
`lean.statement` verbatim equal to the file signature. stmt_deps: only the new node added.

Mismatches found: none in the Lean or the node records. Changed: this section only.
