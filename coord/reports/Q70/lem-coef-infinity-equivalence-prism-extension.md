# Relative equivalence-prism extension

## Worker report

Handoff defect: when this second-reader session began, the assigned sandbox contained only
`.brief2` through `.brief5` and `.check`. There was no worker `report.md`, Lean module, or
node copy to review. The shared node also had no `lean` record. The shared Q24 report is
from stage 1 and explicitly says no Lean was written. Under the instruction to repair and
deliver, this session supplied the missing module and node binding. This report records
that fact rather than attributing a nonexistent statement to another author. No other
agent was started.

The module `Sheaf.CategoryTheory.EquivalencePrismExtension` defines the canonical helper
`SSet.Enhanced.prismVerticalEdge` and states `equivalence_prism_extension` with `sorry`.
The helper contains actual data: the identity one-simplex of the interval, paired with the
vertex degeneracy in `A`, followed by Mathlib's canonical union inclusion and `h₀`.
The source statement and all node fields except the new `lean` record are unchanged.
The theorem docstring follows all six node proof steps, including the base equation at
every stage and the opposite dual. No new definition node or dependency module is needed.

Source: [Kerodon Proposition the project server, Tag 01NX](https://kerodon.net/tag/01NX), read online
in this session. This is a Kerodon source, not a Stacks tag. Its hypothesis only requires
equivalences at final vertices of simplices outside `A`; the node deliberately assumes
equivalences at every vertex, and the Lean preserves exactly that node hypothesis.
The displayed source case is endpoint 1; endpoint 0 is its opposite dual. The full source
proof was read, including its omitted intermediate base invariant; the node's proof and
Lean docstring keep that equation throughout. No characteristic, ring, scheme, or
Noetherian hypothesis is involved.

Statement dependencies opened and checked:

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones` uses
  Mathlib's simplicial sets, standard simplices, subcomplexes, degreewise Cartesian tensor,
  and `Quasicategory`. Its `SSet.Enhanced.IsEquivalenceEdge` explicitly requires one inverse
  edge and two inverse triangles, exactly the node's equivalence notion.
- `def-weil-pbc-category-colimit`: Mathlib `CategoryTheory.Limits.colimit` and `IsColimit`
  express the universal property. Here Mathlib's existing `Subcomplex.unionProd.isPushout`
  realizes the node's pushout as a union, so no duplicate pushout construction is introduced.

Proof dependencies opened: Mathlib `SSet.relativeCellComplexOfMono` in `Skeleton.lean`
constructs the actual relative skeleton with boundary attachments and colimit; the signature
and docstring of `SSet.exists_right_prism_boundary_filtration` were read against its node.
Both are imported for the future proof. The relative outer-horn node's complete statement
was read; it has no recorded Lean module, so there is no module to import for it. It is
only a proof prerequisite, not a missing notion needed to state this item.

## Second reading by Q70

The following is a clause-by-clause check of the completed repair against the node and
source. Because the statement had to be created during this session, it is not an
independent review of a different author's Lean file; the missing handoff is documented
above for the maintainer's reviewer.

1. Simplicial sets and arbitrary small `B`: `{B C D : SSet.{u}}`, with arbitrary universe
   `u`. Verdict: matches the project's common simplicial-set size convention.
2. Quasicategories `C,D`: `[Quasicategory C] [Quasicategory D]`. Verdict: exactly the
   node's two quasicategories, with no Kan or inhabited instance added.
3. Map `p` lifting inner horns: `(p : C ⟶ D) [SSet.InnerFibration p]`. The Mathlib
   `InnerFibration` definition is right lifting against all strictly inner horns.
   Verdict: matches; no equivalence-edge lifting assumption is imposed on `p`.
4. Simplicial subset `A ⊆ B`: `(A : B.Subcomplex)`. Verdict: an actual subset, not an
   unrelated simplicial set or an arbitrary morphism.
5. All vertices of `B` lie in `A`: `hA : ∀ b : B _⦋0⦌, b ∈ A.obj (Opposite.op ⦋0⦌)`.
   Verdict: covers every vertex without a nonemptiness restriction.
6. Endpoint `ε ∈ {0,1}`: `(ε : Fin 2)`. Verdict: both and only the two endpoints.
7. Domain `P_ε`: `unionProd (ofSimplex (stdSimplex.obj₀Equiv.symm ε)) A`.
   Opened Mathlib `Monoidal.lean`: this is `(Δ[1] × A) ∪ ({ε} × B)`, and
   `unionProd.isPushout` has coprojections from those pieces with intersection `{ε} × A`.
   `ofSimplex` of this zero-simplex consists of its degeneracies. Verdict: the same
   pushout via its canonical union realization, including its ambient inclusion.
8. Prescribed map `h₀` and base map `g`: their binders have respectively that union as
   source and `Δ[1] ⊗ B` as source. Verdict: exact objects, without changing factor order.
9. Compatibility `p h₀ = g|P_ε`: `compat : h₀ ≫ p = unionProd.ι ≫ g`.
   Verdict: an equality of entire simplicial maps, not only vertices or homotopy classes.
10. Each prescribed vertical edge is an equivalence: `heq` quantifies over every vertex
    of `B` and applies `IsEquivalenceEdge C` to `prismVerticalEdge A ε h₀ b (hA b)`.
    Unfolding this helper gives exactly the edge with interval coordinate identity and
    `B` coordinate the degeneracy of `b`, included through `Δ[1] × A` then mapped by `h₀`.
    Verdict: the required source equivalence, with no arbitrary choice of lift or edge.
11. Conclusion: `∃ h : Δ[1] ⊗ B ⟶ C`, followed by `unionProd.ι ≫ h = h₀ ∧ h ≫ p = g`.
    Verdict: the exact extension, exact prescribed base, and same existential order;
    no uniqueness or extra conclusion is asserted.

Edge cases: empty `B` forces empty `A` and the empty prism admits its unique map; empty
`C` only admits prescribed data when `B` is empty. `A=B` already supplies the map on the
whole prism. For discrete `B`, `hA` forces `A=B`; no dimension-zero cell is introduced.
The first missing simplex can have dimension one, whose final prism horn has dimension
two, exactly the relative outer-horn bound. Infinite cell sets and unbounded dimensions
are allowed. Both endpoints are covered without extra equality assumptions. The zero
object, scheme, coefficient characteristic, and empty-index product cases do not impose
additional conditions here. All universe variables and object variables are explicitly bound.

Fresh independent searches, using words other than the inherited searches:

- `msearch.py ... leanfinder "Lift a simplicial interval diagram over an inner fibration
  while fixing a subcomplex and one endpoint, with invertible vertex components"`:
  eight hits, including `Subcomplex.liftPath_arrow_coe`, strict-Segal truncated lifts,
  inner horn filling, and the stronger Quillen fibration horn-lifting instance. No match.
- `msearch.py ... loogle '"InnerFibration"'`: twelve hits defining inner fibrations,
  their stability and their quasicategory consequence; no relative interval extension.
- `msearch.py ... leansearch "Extend a relative natural isomorphism across a simplicial
  subcomplex over an inner fibration"`: eight hits including relative morphism data,
  truncated homotopy-category natural isomorphisms and ordinary categorical fibers.
  No matching theorem. The relative morphism, all-horn fibration and strict-Segal
  candidate sources were opened and their signatures checked.
- Fresh `rg` over Mathlib `AlgebraicTopology`, upstream `WeilConjectures`, and
  project `lean/Sheaf` for `prism`, `homotopy.*extend`, `extend.*homotopy`, `01NX`,
  `equivalence_prism_extension`, and `prismVerticalEdge`. No existing exact declaration
  was found. `InvertiblePrismExtension` concerns a different absolute outer-horn prism;
  `IsofibrationExponentiation` cites this node in its proof but does not state it.
  Mathlib's `unionProd`, its inclusions and its pushout theorem already give the domain
  notion and are used directly. No second definition was introduced.

Repairs: supplied the absent module, canonical edge restriction helper, node Lean binding,
source/proof docstrings and this report. The helper's unsuccessful unitor expression was
replaced by the actual degree-one product simplex; the mathematical edge is unchanged.
Added imports of already stated proof dependencies. There is no statement correction,
new definition node, dependency repair, hollow definition, or theorem proof beyond `sorry`.

Validation: the module compiles with the authorized `scompile.py` wrapper, using two
threads and its default 60-second limit; final compile and delivery preflight results are
recorded below. The node's `lean.statement` is extracted verbatim from the final source.

Final validation: `scompile.py` compiled the module both in its sandbox and library
position without warnings or errors. The required `deliver2.py --no-push` returned
`OK (dry run): commit 05fa21cc00 passes the preflight and compiles; nothing pushed`.
The node differs from the shared base only in `lean`; its signature matches the source
verbatim, there are no lines over 100 characters, and only the one named theorem is
postponed with `sorry`.
