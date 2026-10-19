## Worker report

The module `Sheaf.AlgebraicTopology.MarkedEndpointPrismGeneration` states
`SSet.Marked.marked_endpoint_prism_generation`. Its only postponed theorem is
that declaration, with proof `by sorry`. Its docstring contains all eight proof
steps of the node, including both existing combinatorial inputs and the marking
checks. All definitions have actual data. No statement correction, new node, or
dependency-record repair is needed. The item's node copy changes only `lean`.

The previous worker's BLOCKED message referred to a stage-1 unchanged-node
refusal. There was no preserved Lean file, node copy, or report in this sandbox.
This delivery supplies a new stage-2 Lean record and module.

Source read: Lurie, Higher Topos Theory,
<https://www.math.ias.edu/~lurie/papers/HTT.pdf>, Definition the project server,
Definition the project server (1), and Proposition the project server with its proof, PDF pages
163--166 (printed pages 146--149). The source presents the factors in the
opposite order; the node and this module put the interval first. The Cartesian
coordinate switch identifies the two versions and preserves exactly the
coordinatewise markings. The source compares the same classes with the inner
horns retained. No source hypothesis is omitted.

All names below are in `SSet.Marked` unless explicitly qualified.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial sets, standard simplices, horns | `A B : SSet.{u}`, Mathlib `Δ[n]`, `horn n i`, and their actual subcomplex inclusions. The existing enhanced-diagrams dependency uses these same Mathlib primitives. |
| Universe convention | Explicit `universe u`; simplices and Hom sets are in `u`, marked objects in `u + 1`. Every occurrence of the saturation in the theorem explicitly uses `.{u}`. The transfinite closure is also indexed in `u`; no larger indexing universe or equality between universe levels is imposed. |
| Marked objects and marking-preserving maps | Existing `SSet.Marked` with fields `underlying`, `marking`, `degenerate`, and existing `Hom` and `markedCategory`. |
| Products mark an edge exactly when both coordinates are marked | Existing `product` and `productMap`, whose underlying simplicial set is the degreewise product and whose marking is the conjunction of the two coordinate predicates. |
| Minimal and full marking | Existing `flat`, `sharp`, `flatMap`, and `sharpMap`; the respective edge sets are the range of `σ 0` and `Set.univ`. |
| Closure contains the given family and all isomorphisms | `markedWeakSaturation S` is the intersection, expressed by universal quantification, of all `W` with `S ≤ W` and `MorphismProperty.isomorphisms Marked ≤ W`. This is the least class, rather than an unspecified class satisfying the axioms. |
| Closure under pushouts | The same definition requires `W.IsStableUnderCobaseChange`, using the actual categorical pushout universal property. |
| Small continuous transfinite composites | It requires `W.IsStableUnderTransfiniteComposition.{u}`. Its Mathlib structure uses a well-ordered `u`-small indexing type, a well-order-continuous diagram, and a colimit cocone identifying the target. Thus limit stages really are colimits. Isomorphisms cover the zero-length case. |
| Retracts in the arrow category | It requires `W.IsStableUnderRetracts`, whose defining field takes `RetractArrow f g`, not merely a retract on domains or codomains. |
| `I`, all flat inner horn inclusions with `0 < i < n` | `innerMarkedHorns` uses `MorphismProperty.ofHoms` indexed by `Σ n : ℕ, {i : Fin (n + 1) // 0 < i.val ∧ i.val < n}`, with map `flatMap (horn n i).ι`. |
| `F`, all positive-dimensional final marked horns | `finalMarkedHorns` is `ofHoms finalMarkedHorn`. Parameter `n : ℕ` means dimension `n + 1`, so it includes every positive dimension and no dimension zero. |
| Final edge and all degeneracies, no other markings | `finalMarkedSimplex n` marks `Set.range (Δ[n + 1].σ 0)` together with edges whose endpoints are `n` and `n + 1`. A simplex of `Δ[n + 1]` in degree one is a monotone map from `[1]`, determined by these endpoints, so this names exactly the final edge. |
| Induced marking on the final horn | `restrictMarking` pulls back the target marking along the actual subcomplex inclusion; `restrictMarkingι` is that inclusion as a marked map. `finalMarkedHorn` uses `horn (n + 1) (Fin.last (n + 1))`. |
| Endpoint `{1}♯` | `sharpTerminalEndpoint` uses the sharp zero-simplex and `SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)`. This is the terminal vertex, not the initial vertex. |
| Actual pushout source of `P(h)` | `markedPushout` constructs the underlying simplicial pushout, marking the images of the two input markings and the degenerate edges. `endpointPrism h` uses the legs `productMap sharpTerminalEndpoint (𝟙 (flat A))` and `productMap (𝟙 (sharp Δ[0])) (flatMap h)`. The inputs are exactly `Δ[1]♯ × A♭` and `{1}♯ × B♭` glued along `{1}♯ × A♭`. |
| Canonical outgoing map to `Δ[1]♯ × B♭` | `markedPushoutDesc` is the actual `pushout.desc` of the underlying two specified product maps, with their equality on the overlap checked in every degree. It is marking-preserving by naturality on degeneracies and the two `pushout.inl_desc`/`inr_desc` identities on image markings. No arbitrary comparison map or existence choice replaces the canonical arrow. |
| Boundary, including `∂Δ⁰ = ∅` | Mathlib `boundary n` is the subcomplex of nonsurjective monotone maps. `boundary_eq_iSup` identifies it with the union of all codimension-one faces and `boundary_zero` identifies the zero-dimensional boundary with bottom. No replacement boundary is defined. |
| `P_boundary` for all `m ≥ 0` | `boundaryEndpointPrisms` is `ofHoms (fun n : ℕ ↦ endpointPrism (boundary n).ι)`. |
| `P_mono` for every small simplicial monomorphism | `monoEndpointPrisms` is indexed by `Σ A : SSet.{u}, Σ B : SSet.{u}, {h : A ⟶ B // Mono h}`. This includes all small simplicial sets and all their monomorphisms, not just simplex inclusions or finite simplicial sets. |
| First equality of saturated classes | The first conjunct is `markedWeakSaturation.{u} (innerMarkedHorns ⊔ finalMarkedHorns) = markedWeakSaturation.{u} (innerMarkedHorns ⊔ boundaryEndpointPrisms)`. Supremum of morphism properties is union. |
| Second equality | The second conjunct equates the latter with `markedWeakSaturation.{u} (innerMarkedHorns ⊔ monoEndpointPrisms)`. |
| In particular every monomorphism prism belongs to the first class | The last conjunct quantifies over `{A B : SSet.{u}} (h : A ⟶ B)` with exactly `Mono h` and concludes membership for the actual `endpointPrism h`. |

The explicit marked pushout has the required universal property, not just a
compatible underlying map. For any marked span, simplicial pushout maps are
jointly surjective in each degree. Thus every vertex of the pushout is the image
of a vertex from one of the two inputs. Its degeneracy is the image of that
input's degenerate edge, which is marked. Consequently the explicitly adjoined
`Set.range (σ 0)` adds no extra marking beyond the two input images. A map from
the underlying pushout preserves these markings precisely when both restrictions
preserve markings. This proves mathematically that the implemented source is
the displayed marked pushout. No universal-property theorem is assumed or left
as a postponed extra lemma.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones` records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.coneCategory`; I read its signature and docstring and the
  module's explicit convention that standard simplices, horns, simplicial
  products and quasicategories are Mathlib's. Only the underlying simplicial
  conventions are needed for this item; no cone hypothesis is introduced.
- `def-weil-size-convention` is recorded as a metatheoretic convention, without
  a Lean declaration. The universe annotations above implement it.
- `def-weil-pbc-category-colimit` is a Mathlib leaf, recorded as
  `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, with `Cocone`, `IsColimit`, `colimit.desc`,
  `CategoryTheory.IsFiltered`. I read the full cocone and IsColimit signatures,
  the chosen-colimit definition and docstrings, and the filtered-category
  signature. The present construction uses the corresponding actual pushout
  instance, `pushout` and `pushout.desc`; filteredness is not a hypothesis here.
- Existing marked infrastructure is imported from the landed
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, `Hom`,
  `markedCategory`, `flat`, `sharp`, `flatMap`, `sharpMap`, `product`,
  `productMap`. I read their complete definitions. These are unconditional
  concrete definitions, and this delivery neither redeclares them nor uses
  `marked_point_cartesian_model` or chooses any structure from its theorem.
  No dependency on that downstream theorem is added to the DAG; its primitive
  definitions merely already live in the imported module.
- Proof-only input `lem-coef-infinity-monomorphism-boundary-cells` is the
  Mathlib leaf `SSet.relativeCellComplexOfMono` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`. Its full signature
  constructs the boundary relative-cell complex for every simplicial mono.
  It is imported without `public`.
- Proof-only input `lem-coef-infinity-right-prism-boundary` records
  `SSet.exists_right_prism_boundary_filtration` in
  `Sheaf.CategoryTheory.RightPrismBoundary`. I read its full signature and
  proof docstring, including the initial union, final top stage, vertex
  formula, horn index, pushout square and restriction identities. It is
  imported without `public`.

Edge cases checked before finalizing:

- Inner-horn index types are empty in dimensions zero and one; no spurious
  outer horn is a generator of `I`.
- In dimension one, `finalMarkedHorn 0` has horn `Λ[1,1]`, the terminal vertex,
  and its codomain has the unique nondegenerate edge marked. Thus this is the
  same arrow up to canonical pushout isomorphism as `P(∅ → Δ[0])`.
- In dimension two, the final edge already belongs to the final horn, and the
  pullback marking includes it. In dimension one it does not belong to the
  horn, so no designated nondegenerate edge is incorrectly added to the source.
- `boundary 0 = ⊥` includes the initial empty simplicial set. The dimension-zero
  boundary prism is not omitted; it supplies the required new vertical marking.
- For an identity monomorphism, the prism map is the canonical pushout
  isomorphism and belongs to every class in the saturation intersection.
- For an empty source or an empty target the same constructions make sense;
  the only map to an empty target has empty source. No nonemptiness or finite
  dimension hypothesis has been added.
- The mono family includes infinite simplicial sets and arbitrary small
  indexing well-orders. All closure operations are taken in the simplex
  universe; no accidental restriction to countable simplicial sets occurs.

Searches for existing declarations were actually run through `msearch.py`:

1. LeanFinder: `Marked simplicial sets, marked horn inclusions and endpoint
   prisms have the same weakly saturated closure` returned eight hits, including
   `SSet.modelCategoryQuillen.horn_ι_mem_J`, `SSet.horn.multicoequalizerDiagram`,
   `SSet.modelCategoryQuillen.J`, and `SSet.Quasicategory.hornFilling`.
   These concern unmarked horns and their colimits, not this equality of marked
   saturated classes.
2. Loogle: `"marked", "SSet"` returned zero hits.
3. Mathlib grep: `MarkedSSet|MarkedSimplicial|marked.{0,30}prism|WeaklySaturated`
   returned zero hits.
4. LeanSearch: `The weak saturation of final marked horns and inner horns
   equals the weak saturation of endpoint boundary prisms and inner horns`
   returned eight hits including `SSet.horn`, `SSet.quasicategory_of_filler`,
   `SSet.KanComplex.hornFilling`, and horn face inclusions. I read the horn
   definition and the relevant horn-filling signatures; these do not state the
   marked comparison. The existing unmarked generator signatures and
   `SSet.boundary`/`boundary_eq_iSup`/`boundary_zero` were also inspected.
5. Direct `rg` in the upstream `WeilConjectures` source for marked objects and
   endpoint prisms, and for this node id, found no declaration of this statement.
   Searching the new full declaration names in Mathlib, the upstream source,
   `dag/lean_names_upstream.json`, and `lean/Sheaf` found no collision.
6. Direct `rg` in `lean/Sheaf` found the marked infrastructure above and
   `SSet.Enhanced.WeaklySaturated` in
   `Sheaf.AlgebraicTopology.PushoutJoinSaturation`. I read its full definition:
   it is specialized to unmarked `SSet` and supplies no closure operator on
   marked maps. The new `markedWeakSaturation` is exactly the closure notation
   introduced by the present node, assembled from Mathlib's existing closure
   properties. The generator maps, restricted marking, marked pushout and
   endpoint prism are likewise the concrete constructions introduced in the
   item's own statement, listed in `lean.declarations`, not independent
   postponed results.
7. DAG title/statement searches and `tools/blueprint_refs.py search
   'marked simplicial'` found no duplicate of this comparison (the blueprint
   search returned zero). `blueprint_refs.py ancestor` returned
   `prop-coef-integral-exceptional-adjoint`, agreeing with the item's ancestry.

No `STATEMENT-DISPUTED` issue was found. The existing source-error caution at
`n = 1` is handled by separating that case in the node and the theorem's proof
docstring. No node statement, proof, source, or status was changed.

Validation: `scompile.py Q87 lem-coef-marked-endpoint-prism-generation` compiled
both the sandbox module and its library-path form cleanly, approximately 1.4
and 1.5 seconds respectively. Only the requested theorem is postponed.

## Second reading by Q87

I reread the node statement, HTT Proposition the project server (classes (1), (2),
(2-prime), and (2-double-prime)), and every declaration used by the module.
The item-by-item verdict is:

- The objects are `SSet.{u}`, `SSet.Marked`, `flat`, `sharp`, `product`, and
  marking-preserving maps; the module uses the existing `SSet.Marked` fields,
  `flatMap`, `sharpMap`, `productMap`, and `markedCategory`. Verdict: exact.
- The closure is `markedWeakSaturation`, universally intersecting classes
  containing the generators and isomorphisms and stable under cobase change,
  `IsStableUnderTransfiniteComposition.{u}`, and arrow-category retracts.
  Verdict: exact, including colimit continuity and the arrow retract.
- `I` is `innerMarkedHorns`, indexed by `0 < i < n`; `F` is
  `finalMarkedHorns`, with all positive dimensions (the parameter `n` gives
  dimension `n + 1`). Verdict: exact.
- The endpoint map is `endpointPrism h`, whose source is the marked pushout of
  `(Delta[1])♯ × A♭` and `{1}♯ × B♭` over `{1}♯ × A♭`, and whose target is
  `(Delta[1])♯ × B♭`. `markedPushoutDesc` is the canonical pushout map.
  Verdict: exact; no arbitrary comparison map is used.
- `boundaryEndpointPrisms` contains `m = 0` through Mathlib `boundary 0 = ⊥`,
  and `monoEndpointPrisms` ranges over every small simplicial monomorphism.
  Verdict: exact.
- The conclusion is the two stated equalities followed by membership of every
  monomorphism prism in the first saturation, with the same quantifier order.
  Verdict: exact; the theorem signature is byte-for-byte the node's
  `lean.statement` after normalization by `stage2_delivery signature`.

I checked empty simplicial sets and targets, identity and empty-source
monomorphisms, `m = 0`, dimensions `n = 1` and `n = 2`, the empty inner-horn
index cases, and arbitrary infinite small simplicial sets. No nonemptiness,
finite-dimensionality, characteristic, or universe equality is imposed.

The independent searches were rerun with `msearch.py` (LeanFinder, Loogle,
LeanSearch, and Mathlib grep) and direct `rg` over `lean/Sheaf` and the source.
They found only unmarked horn/boundary declarations and the existing marked
infrastructure; no statement of this comparison occurs in Mathlib, the source,
or another DAG node.

The marked-anodyne sibling module visible in the shared working tree is still
only split, so it is not available on this delivery's base. I therefore kept
the concrete `restrictMarking`, `restrictMarkingι`, `finalMarkedSimplex`, and
`finalMarkedHorn` helpers in this item, as the node's statement needs them and
the delivery cannot import an unlanded declaration. Their source meanings and
edge markings were checked directly. Recompilation with `scompile.py` is clean;
the sole remaining `sorry` is the requested theorem.

## Maintainer review fix

Since the delivery's base, `SSet.Marked.restrictMarking` landed in
`Sheaf.AlgebraicTopology.MarkedTriangleCancellation` and `SSet.Marked.finalMarkedSimplex`,
`SSet.Marked.finalMarkedHorn` in `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`. The
delivered copies had the same full names (H4/H9), and a module importing this one together with
those failed (`environment already contains 'SSet.Marked.restrictMarking._proof_1'`). The fix
deletes the four helpers `restrictMarking`, `restrictMarkingι`, `finalMarkedSimplex`,
`finalMarkedHorn` and defines `finalMarkedHorns` as `ofHoms finalMarkedHornInclusion` from
`MarkedTriangleCancellation`, whose marking (degeneracies plus the edge `[n, n+1]` of
`Δ[n+1]`, restricted along the final-horn inclusion) is the same as the delivered one.
`MarkedAnodyneLiftingCalculus` cannot be imported, because its node cites this one as a proof
dependency. For the same reason `markedWeakSaturation` stays local. The theorem signature is unchanged.
