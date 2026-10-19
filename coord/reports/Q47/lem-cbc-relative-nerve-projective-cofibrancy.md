## Worker report

Q47, stage 2, 2026-10-17. The module
`Sheaf.AlgebraicTopology.RelativeNerveProjectiveCofibrancy` states
`SSet.RelativeNerveProjective.relative_nerve_projective_cofibrancy`.
The node copy adds its `lean` record and the already-landed statement dependency
`lem-coef-marked-anodyne-lifting-calculus`, solely to reuse its canonical marking
inclusion. Its mathematical statement and proof are unchanged. There are no new
nodes or dependency repairs. This addition uses brief-stage2 §5, STMT_DEPS MAY GAIN
LANDED NODES. A graph traversal checked that the added node has no dependency path
back to this item.

The preceding worker's stale-dispatch diagnosis confused stages. The ledger's
12:24 merge of Q89 was the stage-1 split: the current node has `reviewed` but no
`lean` or `reviewed_lean`. Its Q89 report describes eight natural-language proof
steps and no Lean module. This delivery supplies the missing stage-2 statement;
it does not re-push that split or edit its records.

Source read: Lurie, Higher Topos Theory, §3.2.5, printed pages 195–203,
especially Remarks the project server–6 (the comma/slice construction), Lemma the project server(2)
(cofibration preservation) and Lemma the project server(2)(D)–(F) (marking and boundary
attachments and use of projectively cofibrant objects). I fetched the referenced
PDF into this item's sandbox and read its text; no shared literature file was
written. The boundary and marking pushout refinements are those explicitly
spelled out in the reviewed node's eight proof steps. They are not attributed to
a separate printed theorem asserting exactly these squares.

Hypotheses and clauses, matched individually:

- Small ordinary category: `(C : Type u) [Category.{u} C]`. Here `u` is the common
  small universe containing the category, the inputs and their arrow labels, as
  in the node's final proof step. It is arbitrary; there is no finiteness,
  nonemptiness, cancellation, fibrancy or local Kan hypothesis.
- Marked simplicial sets and the absolute marked model: the types are the recorded
  `SSet.Marked`, `Marked.Hom`, `Marked.flat`, `Marked.sharp` and `Marked.cof`.
  `Statement.colimits` supplies the small colimits already included in
  `Marked.CartesianModelStatement`; they are an output proof field, not an added
  hypothesis. No model or diagram is selected with `Classical.choose`.
- Input `p : X → N(C)`: `Over (Marked.sharp (nerve C))`. Because the target is
  maximally marked, every simplicial base map is allowed. The real helper `input`
  bundles any such base map; `cellMap` bundles the actual specified underlying map
  when its base triangles commute. Their data are written in full.
- The marked C-diagram `L_C`: `Construction.L` is a functor from these inputs to
  `C ⥤ Marked`. `simplices` identifies its r-simplices with the dependent pairs
  `Σ x, (p(x).obj (Fin.last r) ⟶ c)`, in every degree and at every object.
- Simplicial operators: `operator_simplex` fixes the first coordinate to
  `X.map θ.op x`; `operator_label` fixes the label to
  `p(x).map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m.len)))) ≫ g`.
  This is the node's `g ∘ p(x_{θ(s)} → x_r)`, in Lean's composition order.
- Action in C: `action_simplex` leaves x fixed; `action_label` postcomposes g
  with the given arrow. These are fields of a genuine functor, so all naturality
  and functor laws are retained.
- Marking: `marking` is an iff, marking an edge exactly when its first coordinate
  is marked in X. Neither minimal marking nor a fibrant input is imposed.
- Maps over N(C): `map_simplex` and `map_label` fix `L(f)` to `(f(x),g)`.
  Heterogeneous equalities on dependent arrow coordinates express exactly the
  transport determined by the separately fixed first coordinate. They allow no
  arbitrary transport map or arbitrary action.
- Free diagram `F_b(K)(c) = ∐_{g:b→c} K`: the existing
  `CategoryTheory.evaluationLeftAdjoint Marked b` has precisely this object,
  postcomposition action, and summandwise map. Its `Sigma.ι` inclusions name the
  actual free summands. No new free-diagram definition is introduced.
- For every `σ : Δ[n] → nerve C`, `b = σ(n)` is
  `(SSet.yonedaEquiv σ).obj (Fin.last n)`. There is no assumption `0 < n`.
- The boundary square: `boundary_pushout` is `IsPushout` with top map the free
  image of `Marked.flatMap ∂Δ[n].ι`, bottom map `L.map (cellMap ...)`, and the two
  prescribed vertical maps. It is a pushout in the entire marked diagram category,
  not merely a degreewise assertion about unmarked sets.
- Both vertical-map formulas: `vertical_simplex` sends a simplex in the g-summand
  to first coordinate x; `vertical_label` fixes its label to
  `σ(z_last → n) ≫ g`, where z is the image under i. These formulas apply to
  both the boundary and full simplex, and to both markings of the interval.
- Marking square: `marking_pushout` uses `n = 1`, the real map
  `Marked.flatToMarked (Marked.sharp Δ[1])` with underlying identity, the same b and normalized vertical
  maps, and its actual image under L. It is again `IsPushout` of marked diagrams.
- Every underlying injection: `monomorphisms` quantifies over all inputs X,Y and
  every arrow f over the nerve, with exactly `Marked.cof f.left`, whose definition
  is injectivity in every simplicial degree. The conclusion is
  `(Marked.cof.rlp.functorCategory C).llp (L.map f)`. In the absolute marked model,
  `Marked.cof.rlp` is exactly the trivial-fibration class; the projective model
  has objectwise trivial fibrations. Thus this is its defining cofibration class,
  rather than the weaker condition of objectwise monomorphism.
- In particular every L(X) is projectively cofibrant: `cofibrant` says every
  initial arrow `hI.to (L.obj X)` belongs to that same left lifting class.
  Initial diagrams exist by `Statement.colimits` and objectwise functor colimits,
  so this quantification is not vacuous. Quantifying over an arbitrary initial
  witness avoids selecting a special initial diagram.

`Construction` and `Statement` package this node's normalized assertion as data
and property fields. The sole postponed theorem asserts `Nonempty (Statement C)`;
no definition extracts data from it. In particular this is not a definition of
L with its data replaced by sorry, nor an arbitrary diagram from a bare existence
claim. Its simplex equivalences, all operators, both markings, actions and maps
fix L up to the canonical coordinate isomorphism, which is the equality notion
used by the pushout and lifting assertions. Likewise the vertical maps are fixed
on every summand and degree. The helpers `input` and `cellMap` have real data and only the elementary structural proof for `Over.homMk`. There is
one sorry, for this DAG node, with all eight proof steps in its docstring.

Dependency declarations read and used:

- `lem-coef-marked-point-cartesian-model`:
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`, especially `SSet.Marked`,
  `Marked.Hom`, `Marked.flat`, `Marked.sharp`, `Marked.flatMap`, `Marked.cof`,
  `Marked.CartesianModelStatement` and `Marked.marked_point_cartesian_model`.
  I read the marked category, minimal and maximal markings, injection predicate,
  the complete model statement, and the theorem signature and docstring.
- `def-cbc-enhanced-diagrams-cones`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, its documented Mathlib simplicial
  primitives `nerve`, `stdSimplex`, and ordinary simplicial operators. I also read
  the recorded `SSet.Enhanced.coneCategory` declaration and docstring; this node
  uses the ordinary nerve part of that dependency, not an enhanced cone.
- `lem-coef-infinity-monomorphism-boundary-cells` is a Mathlib leaf:
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`,
  `SSet.relativeCellComplexOfMono`, lines 424–446, with its complete signature,
  docstring and data. The statement uses its actual `SSet.boundary` and inclusion;
  its relative-cell-complex construction is the stage-3 skeletal input.
- `lem-coef-simplicial-projective-model-calculus`:
  `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`,
  `CategoryTheory.ProjectiveSimplicialModelStructure` and
  `CategoryTheory.simplicial_projective_model_calculus`. I read the entire
  projective structure, in particular the objectwise weak-equivalence/fibration
  fields and free-evaluation adjunction, and the theorem's signature/docstring.
  `scompile.py --source` confirmed the current source. The module is retained as
  a proof-dependency import. For the ordinary category specialization the free
  evaluation functor is exactly Mathlib's `evaluationLeftAdjoint`; the statement
  uses the canonical lifting-class description, avoiding a second model choice.
- Mathlib `CategoryTheory.Adjunction.Evaluation`, lines 34–73:
  `evaluationLeftAdjoint` and `evaluationAdjunctionRight`. I read the construction
  on objects and maps and the normalized adjunction, not just its name.
  `MorphismProperty.functorCategory` and `MorphismProperty.llp`/`rlp` were read
  in their defining source files; they are used directly rather than redefined.

Edge cases checked before and after writing:

- n=0: `∂Δ[0]` is empty; the free point and slice point coincide by their labels.
  Both vertical formulas reduce to the identity last-vertex arrow.
- n=1: the missing surjective simplex has last vertex 1; marking the interval
  adds precisely its labelled nondegenerate copies. A degenerate base σ is allowed.
- Empty C: the only input over its empty nerve is empty, and its diagram category
  is terminal. All object-indexed assertions remain valid, without Nonempty C.
- Empty input and empty hom-sets produce empty pair sets; the cofibrant clause
  includes the unique initial arrow. Empty marking-attachment families do nothing.
- A noncancellative category does not spoil the boundary pushout: only surjectivity
  of z distinguishes the free complement; no composition cancellation is used.
- Existing source markings are retained in the injection assertion. No restriction
  on finite dimension or finite sets of nondegenerate simplices is introduced.
- Every universe and variable is explicit; `autoImplicit` is disabled. The common
  universe can be enlarged for any fixed collection of inputs, as the node says.

Searches made through the required wrapper, with actual logs in searches.jsonl:

1. LeanFinder: "The marked last vertex slice diagram sends monomorphisms to
   projective cofibrations and has free boundary and marking pushout squares".
   Eight results, all generic relative-cell-complex and small-object maps; none
   states this marked slice assertion.
2. Loogle: `"IsPushout", "Functor"`. Three generic preservation/small-object
   pushout results, no match for the displayed marked slice squares.
3. Mathlib grep: `relative.?nerve|MarkedSSet|projective.*cofibr`. Zero hits.
4. LeanSearch: "Free evaluation adjoint for ordinary diagrams is the coproduct
   over arrows from the fixed object". Eight results, including the exact
   `CategoryTheory.evaluationLeftAdjoint` and `evaluationAdjunctionRight`.
   I read and reused these declarations.
5. Loogle: `"evaluationLeftAdjoint"`. Four results identify its object, action
   and map formulas; all were read through the source construction.
6. rg in upstream WeilConjectures and side Sheaf for relative nerve, slice diagram,
   projective cofibrancy and the item id found the downstream marked and unmarked
   cone-comparison modules. The marked `sliceValue` there takes an entire
   `RelativeNerveCone.Diagrams` witness, whose comparison assertion depends on this
   item's conclusion. It cannot give this independent bottom-up theorem without
   introducing downstream data as an extra hypothesis. No downstream module is
   imported, no duplicate concrete sliceValue definition is written, and no
   datum is extracted from its comparison theorem. The normalized pair interface
   here describes the same slice construction independently. Searches for the
   new declaration/namespace across Mathlib, upstream and Sheaf found no collision.

No statement correction, new independent notion, dependency repair, or disputed
mathematical claim was needed. All original node fields and search records are
retained verbatim apart from the newly added lean record and the added landed dependency.

An additional search for flat-to-sharp marking maps found the existing
`SSet.Marked.flatToMarked` in
`Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`, lines 45–52. Its full
signature and docstring were read: for any marked X it is the underlying identity
from the minimal marking on X.underlying to X. The marking square now uses its
specialization to `Marked.sharp Δ[1]`. I removed the initially written equivalent
helper before delivery and added its owning landed node to stmt_deps. This reuses
the map and introduces no anodyne-lifting hypothesis.

Validation: the prescribed scompile.py compiled the first version both as the sandbox
probe and at its library path, exit 0, with no errors or warnings. The only
postponed proof is the node theorem. The final version reuses the existing marking inclusion; preflight and
its compile validate that version before delivery.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
