## Worker report

The module `Sheaf.DeligneLaumon.AffineGeometricComponentsFiniteExtension` states
`AlgebraicGeometry.exists_affine_geometric_components_finite_extension` with `sorry`.
The auxiliary structure `AlgebraicGeometry.AffineGeometricComponentDecomposition` packages
precisely its witnesses, using real scheme/morphism data and existing Mathlib predicates.
It belongs to this node's notion and is listed in `lean.declarations`; it is not an
independent new notion needing a definition node. No dependency or statement is changed.

Hypothesis and conclusion correspondence:

- The fixed prime power, finite base field and chosen algebraic closure are
  `D : WeilConjectures.FiniteFieldDatum.{u}`. This is the recorded dependency, including
  `D.q`, the characteristic/exponent data, cardinality, and `IsAlgClosure D.k₀ D.k`.
- `X₀ = Spec B` is expressed invariantly by `{X₀ : Scheme.{u}} [IsAffine X₀]` and its
  structure morphism `f₀`. There is no distinguished coordinate ring B in the node's
  conclusion. Mathlib's `IsAffine` gives the canonical spectrum presentation by global
  sections, so this includes precisely all affine schemes, including Spec of the zero ring.
- Finite type over the base is `[LocallyOfFiniteType f₀] [QuasiCompact f₀]`.
- The geometric scheme X is exactly
  `pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))`.
- `∃ (e : ℕ) (he : 1 ≤ e)` renders the positive extension degree. The finite subfield
  is the recorded `D.extensionSubfield e he`, and its map from the base is the recorded
  `D.extensionEmbedding e he`. Its inclusion into the closure is the subfield's `subtype`.
  No new algebra instance or unrelated field embedding is postulated.
- `H.I : Type u` and `H.finite_I : Finite H.I` render the finite set I. This may be empty.
- `H.component`, `H.componentMap`, `H.inclusion`, and `H.inclusion_over` give the component
  schemes over the finite subfield and their inclusions over that base.
- `H.affine`, `H.nonempty` and `H.open_closed` state that each component is affine,
  nonempty, and both an open and a closed subscheme. The last field uses
  `IsOpenImmersion` and `IsClosedImmersion` on the same inclusion.
- `H.cover` and `H.pairwise_disjoint` render the coproduct decomposition: a disjoint open
  cover by open immersions is exactly a scheme coproduct presentation. The induced maps
  from the inclusions and their inverses on the opens glue to the coproduct isomorphism.
  Thus a separate arbitrary isomorphism is not used in place of the given inclusions.
- `H.geometrically_connected : ∀ i, GeometricallyConnected (H.componentMap i)` gives
  geometric connectedness over the finite field, in the Mathlib notion of the dependency.
- `H.baseComponent` has the actual component pullback to D.k as domain and X as codomain.
  `H.baseComponent_fst` and `H.baseComponent_snd` prescribe both of its projections,
  uniquely characterizing the canonical base-changed inclusion by the pullback property.
  In particular these maps are not arbitrary maps with a component as their image.
- `H.componentPoint` chooses a point in each base-changed component. This is legitimate
  witness data for a nonempty component, never a definition chosen from an unproved
  nonunique existence theorem. `H.component_range` identifies the image with the
  `connectedComponent` of its chosen point; `H.components_bijective` makes the induced
  map to `ConnectedComponents X` bijective. Together they say that the base changes
  are exactly all the connected components, each once.
- The final `∀ (d : ℕ), SmoothOfRelativeDimension d f₀ → ∀ i, ...` is conditional
  preservation of every nonnegative smooth relative dimension on this same decomposition.
- Empty X₀ is permitted. The empty family gives `H.cover`, and all component conditions
  are vacuous; conversely nonempty components mapping into the empty base change force
  the index type empty. In the proof plan this case takes e = 1.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.extensionSubfield`, `FiniteFieldDatum.extensionEmbedding`, and its
  `geometricFiber` convention, which is the same explicit pullback used here.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- Base-change dependency: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`
  under the recorded conventions. `baseChange_iterated` and
  `baseChange_morphism_projections` were read both in the local side module and via
  `scompile.py --source WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
  `FiniteFieldFiber` currently imports the side `Sheaf.AlgebraicGeometry.BaseChangeConventions`,
  supplying these identical declarations. No simultaneous import of its duplicate upstream
  module is added, in accordance with the launcher's duplicate-declaration repair rule.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral` is the recorded umbrella module for
  `def-pc-geometrically-irreducible`; geometric connectedness itself uses
  `AlgebraicGeometry.GeometricallyConnected` from `...Geometrically.Connected`.
- `ConnectedSpace` in `Mathlib.Topology.Connected.Basic` includes nonemptiness. Connected
  components use `connectedComponent` and `ConnectedComponents` from `...Connected.Clopen`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension` and `Smooth`.

The proof dependencies already having declarations are imported nonpublicly, directly or
through the statement imports: affine finite-type algebra, Noetherian connected components,
quasi-compact-open descent, surjectivity after ring base change, testing geometric
connectedness over an algebraically closed field, finite intermediate-field generation,
and smooth/etale permanence. The theorem docstring carries all nine DAG proof steps and
names the nodes used. The current server declaration of `descend_qc_open_fg_subalgebra`
was read via `scompile.py --source`; its signature gives exactly the open descent used.

Source checked: varieties.tex, `lemma-galois-action-connected-components-continuous` (038E)
and its proof, `lemma-descend-open` (0388), and
`lemma-characterize-geometrically-connected` (0387). These give the simultaneous descent
and geometric connectedness; clopen affineness and the optional smoothness follow the
explicit node proof. Edge cases checked also include d = 0, nilpotents/nonreduced affine
schemes, and fields with a non-prime prime-power cardinality: none is excluded by a binder.
The sole postponed proof is the named theorem of this node; the structure contains no sorry.

Searches for an exact existing statement:

- `msearch.py leanfinder "finite extension decomposition connected components affine scheme"`
  returned eight hits about finite maps, affine coproducts and pre-Galois categories;
  none gives simultaneous descent of geometric connected components.
- `msearch.py leansearch "Geometric connected components of an affine finite type scheme over
  a finite field descend to a finite extension"` returned eight hits, including
  `finite_irreducibleComponents_of_isNoetherian` and finite-field extension finiteness;
  none states this theorem.
- The first Loogle query `ConnectedComponents, IsAffine, SmoothOfRelativeDimension` reported
  unknown unqualified identifier `IsAffine`. The corrected query
  `AlgebraicGeometry.GeometricallyConnected, AlgebraicGeometry.Scheme` returned twelve
  definitions and base-change facts, but no descent theorem.
- `msearch.py grep "connectedComponent|ConnectedComponents|geometric.*component"
  AlgebraicGeometry` found nine hits about constant sheaves and geometric connectedness;
  none is the target theorem.
- `rg` over Mathlib's connected topology declarations, upstream `WeilConjectures/`, and
  project `lean/Sheaf` found no exact statement or prior `AffineGeometricComponentDecomposition`.
  The project `GenericComponentsSplit` concerns irreducible components, allows an arbitrary
  field extension and does not give this connected affine clopen partition or dimension clause.
  The upstream node-id/name search also found no target declaration.

No `STATEMENT-DISPUTED` flag, statement correction, new DAG node or dependency repair.

## Second reading by Q143

Independent maintainer second reading, 2026-10-18, of immutable delivery
4400b211c0b85b0d249ed978af4a6c9a2af45b6e. This section is supplied by the
independent maintainer reviewer, not attributed to a second Q143 worker.
The original placeholder section was insufficient (delivery-errors H11).
The Lean module and node need no correction.

Clause-by-clause reading with the snapshot node and Lean module open:

1. Fixed prime power and algebraic closure: `D : FiniteFieldDatum.{u}` has
   prime `p`, positive exponent `a`, `q = p ^ a`, a finite field `k₀` of
   cardinality `q`, and `IsAlgClosure k₀ k`. I read the actual dependency
   structure, `extensionSubfield`, `extensionEmbedding`, and the unique-subfield
   theorem used to define them. The finite extension is the specified subfield
   of this closure, with the specified base inclusion. Correct.
2. Affine finite-type scheme: `X₀ : Scheme.{u}`, `[IsAffine X₀]`, and the
   explicit structure morphism `f₀` with `[LocallyOfFiniteType f₀]` and
   `[QuasiCompact f₀]`. `IsAffine` is the canonical spectrum presentation
   (`Scheme.isoSpec`); no coordinate ring B is needed as separate witness data.
   Both finite-type conjuncts match the dependency. Correct.
3. The geometric scheme and finite scalar extension are actual `pullback`s,
   along `algebraMap D.k₀ D.k` and `D.extensionEmbedding e he`, respectively.
   This follows the recorded base-change conventions. Correct.
4. Positive degree and finite set: `∃ e : ℕ, ∃ he : 1 ≤ e` and the structure
   fields `I : Type u`, `finite_I : Finite I`. There is no nonempty-index
   assumption, and every finite set has a representation in this universe.
   Correct.
5. Component schemes over the finite field: `component`, `componentMap`,
   `inclusion`, `inclusion_over` specify the schemes and their inclusions over
   the finite base. `affine`, `nonempty`, `open_closed` give exactly affine,
   nonempty open and closed subschemes. Correct.
6. Coproduct decomposition: `cover` and `pairwise_disjoint` give a jointly
   surjective disjoint family of open immersions. These identify the target
   scheme with the coproduct: the local inverse maps on the disjoint open
   images glue, including the empty cover. No separate arbitrary isomorphism
   or arbitrary morphism substitutes for the inclusions. Correct.
7. Geometric connectedness: `geometrically_connected` uses Mathlib's actual
   `GeometricallyConnected (componentMap i)`, i.e. connectedness of all field
   base changes. I read this class and `geometrically_iff_of_commRing`, and
   checked `ConnectedSpace` includes nonemptiness. Correct.
8. Base changes are exactly the connected components: `baseComponent` has
   the actual pullback of each component as domain. `baseComponent_fst` and
   `baseComponent_snd` uniquely prescribe its map to the geometric scheme;
   together with `inclusion_over` and the composite of `extensionEmbedding`
   with subfield inclusion, these are the canonical iterated base-change
   inclusions. Pullback pasting makes these open immersions, so the range
   characterization also identifies the scheme structures. `componentPoint`
   chooses a point in each actual base change; `component_range` identifies
   its image with that point's connected component; `components_bijective`
   gives every component exactly once. This is witness data in an existential
   theorem, not a hollow definition or a choice of an arbitrary map. Correct.
9. Smooth relative dimension: after the same decomposition is chosen,
   `∀ d : ℕ, SmoothOfRelativeDimension d f₀ → ∀ i, ...` preserves every
   nonnegative relative dimension, with no smoothness assumption on the main
   existence assertion. The conclusion uses that component's actual structure
   morphism. Correct.

Dependencies and sources checked:

- All nine snapshot statement dependencies, their complete statements, and
  their Lean/match records were read. The actual signatures and docstrings of
  `FiniteFieldDatum`, its finite-extension constructions, `Spec`, `Spec.map`,
  `IsAffine`, `LocallyOfFiniteType`, `QuasiCompact`, the base-change projections
  and iterated comparison, `GeometricallyConnected`, `ConnectedSpace`,
  `connectedComponent`, `ConnectedComponents.mk`, `IsOpenImmersion`,
  `IsClosedImmersion`, and `SmoothOfRelativeDimension` were inspected.
- Stacks `varieties.tex:792-842` (0387 and 0388) and `1284-1328` (038E),
  `fields.tex:693` (09GH), `morphisms.tex:5582` (02NK), `5594` (02NL),
  and `7119` (01VB) support all hypotheses and the descent/smoothness plan.
  The blueprint ancestor `lem-zl-affine-curve-hc2-purity.md`, second proof
  paragraph, explicitly requests simultaneous finite-field component descent.
  Finite fields are perfect, so its algebraic closure supplies the separable
  closure in 038E. No additional separatedness, reducedness, or smoothness
  hypothesis is introduced.
- The current upstream `descend_qc_open_fg_subalgebra` source was retrieved
  through `scompile.py --source WeilConjectures.AlgebraicGeometry.DescendQCOpenFGSubalgebra`.
  Its exact signature descends a quasi-compact open along the canonical map to
  a finitely generated subalgebra. It supplies precisely step 3, with no extra
  quasi-separatedness or finite-type assumption.
- Independent `rg` searches of Mathlib algebraic geometry, upstream
  `WeilConjectures`, and project `lean/Sheaf` used the declaration names and
  alternative phrases `connected.*finite.*extension`,
  `finite.*extension.*connected`, and `geometric.*component`. No exact prior
  theorem or duplicate decomposition structure was found. I opened
  `GenericComponentsSplit.lean`: it concerns geometrically irreducible
  components over an unspecified finite separable extension, not this affine
  connected-component partition over the designated finite subfield. The
  original worker's semantic/Loogle/grep search records are retained above.

Edge cases and gates:

- Empty X₀ / Spec of the zero ring: the empty type may be I, all component
  conditions are vacuous, and the empty cover identifies the empty target;
  e = 1 is allowed. Conversely no nonempty component can map to an empty target.
- Dimension zero is included by `d : ℕ`; nonreduced affine schemes and all
  prime powers are included. Smoothness is only a conditional conclusion.
- The universe `u` is explicitly bound throughout. The datum and schemes use
  the dependency's common universe; no new equality of unrelated universes,
  small test universe, or finiteness assumption is imposed. Geometric
  connectedness reuses the standard Mathlib field-test notion.
- Both declaration names are recorded in `lean.declarations`. The structure
  has actual data and properties and contains no `sorry`; the only theorem
  body is exactly `by sorry`. Module and declaration docstrings contain the
  source place and blueprint id; the theorem docstring carries all nine proof
  steps. No line exceeds 100 characters, no auto-implicit variable remains,
  and the node's `lean.statement` equals the file signature verbatim.
- Only `lean` changed in the node relative to the delivery parent. No new
  nodes, dependency modules, statement correction, or citer audit is required.
  Missing-helper and universe-repair rules were considered; no missing
  interface or universe defect was found.
- The current `origin/newtargets-dag:coord/route-pivot-dropped.txt` has empty
  intersection with this item's statement and proof dependencies. No repair
  note exists for this item at that ref. No dropped enhancement, infinity,
  model-category or pro-etale machinery occurs in the delivered module.

Compiler reproduction, 2026-10-18:

Command, run with the immutable snapshot as working directory:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q143 lem-zl-affine-geometric-components-finite-extension lean/Sheaf/DeligneLaumon/AffineGeometricComponentsFiniteExtension.lean
```

Exit code: 0. Complete result text:

```text
sandbox Sheaf/Stage2/Sandbox0.lean

(with the modules compiled into /dev/shm/nt-tmp/nt-local-compile-4z9pnlza/.lbuild) [6.7 s]
library Sheaf/DeligneLaumon/AffineGeometricComponentsFiniteExtension.lean

[152.8 s]
```

No errors or warnings were printed. The installed wrapper identifies itself as
server-side persistent-overlay compilation (2026-10-17) and prints the above
private overlay and library checks; I used that prescribed wrapper without
modifying it or invoking SSH directly. The original report supplied no explicit
per-file compile transcript, so this independent reproduction supplies the
missing evidence. The earlier invocation from the review directory failed only
because the relative `lean/` path is under `snapshot/`; rerunning from the correct
working directory produced the successful result above.

No lake/global build, live Lean write, clone edit, delivery, merge, or Git mutation
was performed. Only this complete replacement report and the independent
`review.md` were written in the authorized review directory.
