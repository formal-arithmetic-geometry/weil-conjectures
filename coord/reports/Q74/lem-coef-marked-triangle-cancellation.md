# Stage-2 statement: lem-coef-marked-triangle-cancellation

## Worker report

The module `Sheaf.AlgebraicTopology.MarkedTriangleCancellation` states
`SSet.Marked.marked_triangle_cancellation`, with `sorry` as its entire proof.
Its docstring contains the complete six-step proof in the current reviewed DAG.
All other declarations are explicit constructions or predicates, contain real data,
and are listed in `lean.declarations`. They specify the notions introduced inline
in this item's statement, rather than assert extra theorems. There are no new nodes,
no dependency-record repairs, and no statement correction or disputed statement.
The earlier worker's stage-1 unchanged-node refusal was a stage mismatch: Q18
already supplied the split, but the base item still has no Lean record. This
stage-2 delivery leaves that split and all other node fields unchanged and adds `lean`.

Clause-by-clause correspondence:

- Small simplicial sets and all their standard simplices, horns and Kan complexes
  use Mathlib `SSet.{u}`, `Δ[n]`, `horn n i` and `KanComplex`. The explicit universe
  `u` implements `def-weil-size-convention`. There is no universe equality or bound
  on the shapes beyond the node's smallness convention, and `autoImplicit` is false.
- A simplicial set with a set of edges containing all degeneracies is the already
  defined `SSet.Marked`; its `marking` and `degenerate` fields give precisely those
  conditions. Its morphisms are the marking-preserving maps `Marked.Hom`, with
  the existing `markedCategory` instance. These are reused, never copied.
- The minimal and maximal markings are the existing `Marked.flat` and
  `Marked.sharp`; `flatMap` is the existing functorial map on minimal markings.
  `withEdges` adds the range of the degeneracy map to the given set of extra edges.
- The class W is `markedAnodyne`. Its formula quantifies over all morphism classes
  P containing all isomorphisms and all generators, closed under the three stated
  operations, and requires P to contain the given map. This is the intersection
  of exactly those classes, hence the smallest one in the node. In particular it
  does not replace weak saturation by a model-structure or lifting-property claim.
- Isomorphisms are `MorphismProperty.isomorphisms Marked ≤ P`. Pushouts are
  `P.IsStableUnderCobaseChange`, applying to every pushout square, without making
  a noncanonical choice of colimit. Small continuous transfinite composites are
  `P.IsStableUnderTransfiniteComposition.{u}`; Mathlib's shape interface includes
  the colimit condition at limit stages. Arrow retracts are
  `P.IsStableUnderRetracts`, defined using `RetractArrow`. Empty composites are
  covered by the separately required isomorphisms.
- Family (i) is the first conjunct of `ContainsMarkedAnodyneGenerators`:
  every `n : ℕ` and `i : Fin (n+1)` with `0 < i` and `i < Fin.last n` contributes
  `flatMap (horn n i).ι`. These are exactly the inner flat horn inclusions.
- Family (ii) is the second conjunct: `finalMarkedHornInclusion n` for all `n : ℕ`.
  Its dimension is `n+1`, an exact reindexing of the positive dimensions in the
  statement. `finalEdgeMarkedSimplex n` marks the degenerate edges and the edge
  with endpoints `(Fin.last n).castSucc` and `Fin.last (n+1)`, namely `[n,n+1]`.
  `restrictMarking` takes the inverse image of this marking along the final horn
  inclusion. The map is that actual inclusion, not an arbitrary marked map.
- Family (iii) is the third conjunct:
  `fullMarkingMap (hornMarkedSimplex 2 1)`. The underlying pushout of the identity
  on the minimal horn along its simplex inclusion is the simplex itself. Colimit
  markings are the union of the images of the input markings; `hornMarkedSimplex`
  implements exactly that formula, namely degeneracies plus the image of the
  edges of the horn. For horn index one these are `[0,1]` and `[1,2]`. Thus the
  explicit source represents precisely the specified marked pushout.
- Family (iv) is the fourth conjunct: every `K : SSet.{u}` with `KanComplex K`
  contributes `fullMarkingMap (flat K)`, the identity-underlying map from the
  minimal to the maximal marking. No countability or inhabitedness restriction
  is imposed; countable generators occur only in the proof docstring.
- The conclusion is `markedAnodyne (fullMarkingMap (hornMarkedSimplex 2 2))`.
  Horn index two consists of the faces omitting zero and one: its nondegenerate
  edges are `[1,2]` and `[0,2]`. Therefore its image-edge marking, union the
  degeneracies, is exactly the displayed source of the node. `fullMarkingMap`
  has underlying map `𝟙 (Δ[2])` and target `sharp (Δ[2])`, as required. The
  theorem has no extra hypothesis.

Dependency declarations and source inspection:

- `def-cbc-enhanced-diagrams-cones`: imported its recorded module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, read its module documentation and
  recorded `SSet.Enhanced.coneCategory` signature/docstring. That node explicitly
  uses Mathlib's simplicial primitives, which this item uses directly. The comma
  cone construction is not part of this item's mathematical statement.
- `def-weil-size-convention`: read its convention-only Lean record; it deliberately
  has no declaration. This module declares `universe u` explicitly and uses `u`
  for simplices and small transfinite shapes.
- The existing `Sheaf.AlgebraicTopology.MarkedPointCartesianModel` supplies
  `SSet.Marked`, `Marked.Hom`, `Marked.markedCategory`, `Marked.flat`, `Marked.sharp`
  and `Marked.flatMap`. Read their complete definitions and docstrings. Only these
  definitions are used: the model-structure theorem is not an assumption of W or
  of the conclusion. No statement-dependency edge to that downstream model theorem
  is added; its proof ultimately uses this item. The shared definitions currently
  live in that module, so the import is necessary to obey one-definition-per-notion.
  A later proof import from that module back to this item must be omitted under
  the standing import-cycle rule.
- Already stated proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.InfinityFibrations` and
  `Sheaf.CategoryTheory.EquivalenceOuterHornFilling`. The other three proof nodes
  currently have no Lean records and are not being stated here: they are needed
  only to prove this item, not to type its statement.
- Mathlib's `MorphismProperty.IsStableUnderCobaseChange`,
  `IsStableUnderTransfiniteComposition` and `IsStableUnderRetracts` are used
  directly. Read their definitions, including `RetractArrow` and the universe
  parameter of the transfinite-shape interface.

Edge cases checked before writing: no inner generator exists in dimensions zero
or one; family (ii) includes dimension one via `n=0`, with source the terminal
vertex and only degenerate edges marked. It excludes dimension zero exactly as
in the source. The empty Kan complex is allowed and its flat-to-sharp extension
is an identity; a point has only degenerate edges. In dimension two, horn one
marks exactly 01/12 and horn two exactly 02/12, so the target theorem adds 01,
not 02 or 12. All degenerate edges are included even for general horn shapes
by `withEdges`. All maps are canonical inclusions or underlying identities.
No property of quasicategories or a model category has been added as a theorem
hypothesis.

Source: opened the IAS HTT PDF, Definition the project server, Remark the project server,
Proposition the project server and Corollary the project server. The corollary's horn index is two.
Its source is `(Λ²₂)♯ ⨿[(Λ²₂)♭] (Δ²)♭`, precisely the image-marking model used
here. The proof follows the reviewed DAG's more explicit small-object/retract
argument and the opposite form of Proposition the project server.

Searches made:

- `msearch.py` LeanFinder query: "The identity of a marked two simplex with edges
  02 and 12 marked to the fully marked simplex is marked anodyne". Eight hits:
  `SSet.Edge.CompStruct.exists_of_simplex` and unmarked horn face/inclusion maps,
  including `horn₂₂.ι₀₂` and `horn₂₂.ι₁₂`. None asserts a marked marking extension.
- `msearch.py` Loogle query: `"marked", "anodyne"`; zero hits.
- `msearch.py` grep query: `MarkedAnodyne|marked.?anodyne|WeaklySaturated`, under
  Mathlib `CategoryTheory`; zero hits.
- `msearch.py` LeanSearch query: "The marked triangle with the final and long edges
  marked is marked anodyne". Eight hits, comprising the unmarked
  `SSet.horn.primitiveTriangle` and unrelated triangulated-category triangle facts.
- Read Mathlib `SimplicialSet/AnodyneExtensions/Basic.lean`: its `anodyneExtensions`
  concerns unmarked Quillen horns and is not this marked class.
- `rg` over `WeilConjectures/` for `marked.?anodyne|MarkedAnodyne|marked.{0,30}triangle`
  and the exact item id returned no declaration. `rg` over `lean/Sheaf` found the
  marked data API in `MarkedPointCartesianModel`, which is reused; no existing
  marked-anodyne membership theorem or generator closure definition was found.
  The existing `SSet.Enhanced.WeaklySaturated` in `PushoutJoinSaturation` is
  specialized to unmarked `SSet`, so the present definition uses the same Mathlib
  closure predicates on `Marked` directly.

Validation: `scompile.py Q74 lem-coef-marked-triangle-cancellation` compiled the
single delivered module successfully in both wrapper checks, with no errors or
unexpected warnings. The dry-run preflight is run after this report is written.

## Second reading by Q74

I independently opened the sandbox node and module, the two statement-dependency
records and their declarations, the existing marked-set API, and the Mathlib
closure predicates. I read HTT Definition the project server, Definition the project server,
Remark the project server, Proposition the project server and Corollary the project server at
https://www.math.ias.edu/~lurie/papers/HTT.pdf (printed pages 146--150).
This source is HTT, not a Stacks result. The section imposes no extra
quasicategory, nonemptiness, finiteness or model-category hypothesis on the
marked simplicial sets in the statement.

Independent object/hypothesis/conclusion checklist (each verdict is PASS):

1. Small simplicial sets, standard simplices, horns and Kan complexes:
   `SSet.{u}`, `Δ[n]`, `horn n i`, `KanComplex K`. The enhanced-diagrams
   dependency explicitly reuses these Mathlib notions. I read `coneCategory`
   and its comma construction: that is not a replacement definition of a
   simplex or a horn. Mathlib's horn is the union of the faces other than i;
   its Kan predicate fills precisely positive-dimensional horns.
2. A marked object and its maps: the imported `SSet.Marked` has exactly
   `underlying`, `marking` and `degenerate`; `Marked.Hom` is the subtype of
   simplicial maps preserving markings. Its category instance adds no
   assumption. The node's inline notion is therefore the existing one.
3. Minimal and full markings: imported `flat` uses `Set.range (K.σ 0)`;
   imported `sharp` uses `Set.univ`. Imported `flatMap` sends degeneracies
   to degeneracies by simplicial naturality. These are the node's flat and
   sharp, with no second definition of either.
4. The class W contains every isomorphism: the first premise in the
   universal formula for `markedAnodyne` is
   `MorphismProperty.isomorphisms Marked.{u} ≤ P`.
5. Pushout closure: `P.IsStableUnderCobaseChange` quantifies over every
   `IsPushout` square and applies to the opposite parallel arrow. It needs
   no supplied choice of pushouts or extra colimit hypothesis.
6. Small transfinite closure: `P.IsStableUnderTransfiniteComposition.{u}`
   quantifies over every well-ordered shape `J : Type u`. I read its
   `TransfiniteCompositionOfShape` interface: the diagram is well-order
   continuous, the source is its bottom object up to isomorphism, the target
   is its colimit, and each proper successor map satisfies P. Thus the
   limit-stage requirement and the size convention are both retained.
7. Arrow retract closure: `P.IsStableUnderRetracts` uses `RetractArrow`,
   exactly the arrow-category retract specified by the node.
8. Generator (i): the first conjunct of `ContainsMarkedAnodyneGenerators`
   quantifies over every n and i with `0 < i` and `i < Fin.last n`, and
   applies P to `flatMap (horn n i).ι`. These are exactly the inner horns.
9. Generator (ii): its second conjunct includes `finalMarkedHornInclusion n`
   for every n. Dimension `n+1` ranges over exactly all positive dimensions.
   `finalEdgeMarkedSimplex n` adds the edge with vertices n and n+1 to the
   degenerate marking. `restrictMarking` takes its inverse image along the
   last horn; `restrictMarkingInclusion` has underlying map that horn's ι.
   Thus the intersection marking and the canonical map are both exact.
10. Generator (iii): its third conjunct is
    `P (fullMarkingMap (hornMarkedSimplex 2 1))`. The underlying pushout
    along the identity of the minimal horn is Δ[2]. Its marking is the union
    of degeneracies and the image of the horn's edges, exactly the formula
    in `hornMarkedSimplex`. For index one those edges are 01 and 12.
    This concrete pushout model states the same generator up to its
    canonical marked isomorphism; pushout/retract closure respects that
    isomorphism. It adds no assumption about a separately chosen pushout.
11. Generator (iv): its fourth conjunct quantifies over every
    `K : SSet.{u}` and every proof `KanComplex K`, and uses
    `fullMarkingMap (flat K)`. Its underlying map is the identity. The Lean
    statement does not restrict K to the countable generators used in the
    proof plan.
12. Smallest such class: `markedAnodyne` quantifies over every property P
    satisfying precisely checklist items 4--11. This is their intersection,
    with no extra stability condition, lifting characterization or model
    structure assumed.
13. Conclusion: `marked_triangle_cancellation` asserts
    `markedAnodyne (fullMarkingMap (hornMarkedSimplex.{u} 2 2))`.
    The second horn has exactly edges 02 and 12, including their vertices;
    `withEdges` also includes all degenerate edges. `fullMarkingMap` is
    `⟨𝟙 _, ...⟩` into `sharp Δ[2]`, so it adds exactly edge 01.
    There are no theorem hypotheses or hidden instance binders.

Edge cases: the strict inner inequalities exclude dimensions zero and one;
family (ii) includes dimension one at helper argument zero and excludes
only dimension zero as the source does. At dimension one the last horn is
the target vertex, and the final edge is nondegenerate. Empty Kan complexes
are included: `KanComplex` imposes no dimension-zero inhabitance condition.
The point and all degenerate edges are included. The empty transfinite
composite is an identity, already included; finite and limit composites
are covered by the Mathlib interface. The explicit universe u is shared by
the simplicial values and small ordinal shapes and is otherwise arbitrary;
no extra universe equality, countability or size hypothesis is imposed.
Rings, characteristic, schemes and zero objects are not parameters here.

Independent searches, using different wording from the worker:

- `msearch.py ... leanfinder "Weakly saturated marked horn generators imply
  marking cancellation for a cartesian triangle"`: eight unmarked horn
  colimit results, including `horn₂₁.sq`, `horn₂₂.sq` and `horn₃₂.exists_desc`.
  I checked the horn source: these identify faces or supply unmarked maps,
  and do not assert a marked-anodyne marking extension.
- `msearch.py ... loogle '"marking"'`: zero hits.
- `msearch.py ... grep 'Marked|marking' AlgebraicTopology/SimplicialSet`:
  zero hits.
- `msearch.py ... leansearch "Simplicial marking extension generated by
  inner horns final horns and Kan complexes"`: eight results about
  `Quasicategory`, `KanComplex`, their horn-filling lemmas, and unmarked
  Quillen fibrations; no marked morphism class or cancellation theorem.
- Independent `rg` in upstream WeilConjectures, Mathlib AlgebraicTopology,
  and this project's AlgebraicTopology/CategoryTheory, for
  `marked.?anodyne`, marking extensions/horns/saturation, the helper names,
  and `WeaklySaturated`: the marked category/flat/sharp API is already in
  `MarkedPointCartesianModel` and is correctly reused. The only project
  weak-saturation predicate found is `SSet.Enhanced.WeaklySaturated`, whose
  argument is `MorphismProperty SSet`, not a property on `Marked`.
  There is no existing declaration matching this item's theorem or the
  newly explicit marked-generator class.

No new nodes, dependency modules or statement corrections are in this
delivery, so the corresponding extra audits and citer audit do not apply.
I also checked the current proof-dependency records: InfinityFibrations and
EquivalenceOuterHornFilling are the two stated imports; the small-object,
cocartesian-composition and core-Kan nodes have no Lean records yet and are
not needed to type this statement. Importing the existing marked API does
not use or assume its downstream model-structure theorem. The reverse
proof import must remain omitted to avoid an import cycle.

H5/H6/H8/H9: every helper has explicit data or is a predicate; the only
postponed declaration is the final theorem, with `sorry` as its complete
proof. Every declaration names its source and blueprint. The theorem's
proof docstring follows all six node steps: countable generators,
small-object factorization, opposite cartesian cancellation, comparison
in a fiber, core-Kan marking, and the explicit arrow retract. All binders
and the universe are declared with autoImplicit disabled, and the node's
`lean.statement` is verbatim the file's theorem signature.

Mismatches found: none. I preserved the Lean and node, and added this
independent reading to the report. The prescribed scompile.py invocation
with the absolute sandbox module path passed both the sandbox and library
checks (1.2 s and 1.3 s), with no errors or warnings. An initial invocation
from the read-only repository used a relative sandbox path and failed to
locate the file; rerunning with its absolute path resolved it.

## Reviewer fix (maintainer second reader, 2026-10-17)

Both readings missed that the delivery's base already contains the landed
`Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus` (node
lem-coef-marked-anodyne-lifting-calculus, Q39). It defines `SSet.Marked.markedAnodyne`,
the same full name as this delivery's class. That node lists this item as a proof
dependency. Under stages/2-statements.md §3 rule 7 its module therefore gets
`import Sheaf.AlgebraicTopology.MarkedTriangleCancellation`. Any module importing both fails
with "environment already contains 'SSet.Marked.markedAnodyne'" (reproduced with nt_compile.py).
The item cannot cite or import that module, because it is a citer and doing so closes a
cycle. The reviewer therefore renamed the class to `SSet.Marked.markedAnodyneClass`.
Its docstring records the coincidence with the downstream `markedAnodyne`; stage 3 bridges
the two. The statement, `lean.statement`, `lean.declarations` and `lean.note` are updated to
match. The theorem docstring now names the DAG node each proof step uses. Nothing else
changed. The fixed module compiles clean. A test module importing both it and
MarkedAnodyneLiftingCalculus also compiles.
