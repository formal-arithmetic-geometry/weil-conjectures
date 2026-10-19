## Worker report

The delivery states `SSet.Marked.marked_internal_hom` in
`Sheaf.AlgebraicTopology.MarkedInternalHom`. It adds the real helper
`SSet.Marked.internalHomMap` and no new notion or dependency module. The sole
postponed proof is the named theorem, with the node's seven-step proof in its
docstring. No change to the natural-language statement is needed.

Clause-by-clause correspondence:

- The simplicial sets, simplices, and operators are Mathlib `SSet.{u}`,
  `SimplexCategory`, `stdSimplex`, and `stdSimplex.objEquiv`, as used by the
  recorded `Sheaf.CategoryTheory.EnhancedDiagramsCones` dependency. The size
  convention is metatheoretic, as its record says: `universe u`, with explicit
  `Marked.{u}` binders throughout and no enlargement, renders it here.
- A marked simplicial set and preservation of markings are exactly the existing
  `SSet.Marked` and `SSet.Marked.Hom`/`markedCategory`, not an assumed model
  structure. `Marked.marking` is a subset of degree one and `Marked.degenerate`
  requires all `sigma_0` edges. All degenerate one-simplices have that form.
- `Marked.product` has underlying `X.underlying ⊗ Y.underlying` and marks exactly
  pairs of marked edges. Its data is degreewise, and `productMap` is the
  corresponding degreewise product map.
- The two markings are the existing `flat` (range of `sigma_0`) and `sharp`
  (the entire edge set). The imported `flatSimplex` and `productLeft` assemble
  the actual simplicial object
  `mapFlat X Y = (flatSimplex ⋙ productLeft X).op ⋙ yoneda.obj Y`.
  In degree n this is exactly the marked-map set from `X × (Delta^n)^flat`
  to Y; operators precompose by `id_X × Delta(alpha)`.
- The actual `internalHom X Y` uses this `mapFlat` as underlying simplicial set.
  Its edge marking tests every marked e of X and every edge a of Delta^1.
  This is precisely preservation of the product with the sharp interval.
  Its existing real `degenerate` field proves that these markings contain
  all degeneracies, so the construction clause needs no new definition.
- `internalHomMap a b` sends h to `productMap a (id _) ≫ h ≫ b`, with naturality
  and marking preservation as real structure proofs. The first two conjuncts
  of the theorem give the identity and composition laws, with a contravariant
  X variable and a covariant Y variable. No map is an arbitrary parameter.
- `E : ∀ X Y Z, (Z ⟶ internalHom X Y) ≃ (product Z X ⟶ Y)` is the claimed
  bijection for every marked Z. The third conjunct specifies its forward map
  on EVERY simplex: `(E g)_n(z,x) = (g_n z)_n(x,id_[n])`. This determines the
  equivalence uniquely and is exactly the evaluation-induced ordinary
  untranspose, restricted to marked maps. In particular evaluation itself is
  `E X Y (internalHom X Y) (id _)`, a marked map, with the stated formula.
  There is no choice of data from a mere unspecified existence theorem.
- The fourth conjunct specifies the inverse transpose on every n, m, z, x,
  alpha: `h_z(x,alpha)=F_m(Z(alpha)z,x)`. Since E is an equivalence, both inverse
  identities are included, not merely injectivity or surjectivity of one map.
- The fifth conjunct states naturality simultaneously in Z, X and Y:
  `E (c ≫ g ≫ internalHomMap a b) = productMap c a ≫ E g ≫ b`.
- The final conjunct quantifies over EVERY underlying simplicial map
  `g : Z.underlying ⟶ (internalHom X Y).underlying`, without assuming g marked.
  It says g preserves markings iff its ordinary evaluation untranspose sends
  every pair of marked z and x to a marked edge of Y. Both implications of
  the requested marking equivalence are present.
- `mapFlat` and `internalHom` have type `SSet.{u}` / `Marked.{u}` for inputs
  in that same universe. The equivalences have no larger-universe inputs or
  hypotheses. The collection of all small objects has its usual next-level
  type, which does not enlarge any degree set.

Declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the complete module,
  including its uses of Mathlib `stdSimplex`, degreewise tensor products,
  `ihom`, and `SSet.Enhanced.coneCategory`; none of its independent cone or
  horn notions is redefined here.
- `def-weil-size-convention`: read its entire convention record. It has no
  declaration or module to import; the universe is explicit in this delivery.
- `def-weil-pbc-simplicial-set`: read its full `mathlib_match` and the declarations
  `SSet`, `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, and
  `SSet.Finite` in the recorded Mathlib files. Those files are already
  transitively available through the required public imports.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: read the definitions
  listed above and the complete `CartesianModelStatement` and
  `marked_point_cartesian_model` signature and docstring. Also read the current
  server source with `scompile.py --source` to confirm the local interface.
  The stronger model-structure statement bundles one exponential equivalence
  and its forward formula among many unrelated assertions, but does not
  itself state this standalone theorem with its marking iff, all three
  naturalities, inverse formula, and functor laws. It is not an exact existing
  match for this item. We use only its preexisting definitions; its theorem
  is neither a hypothesis nor an ingredient of the proof plan.

Import-cycle bookkeeping: the parent node `lem-coef-marked-point-cartesian-model`
uses this item in its proof, but its module currently owns the foundational
marked definitions. Adding the usual proof import of this delivery back into
that parent module would close a module cycle. Under stages/2-statements.md
section 3 rule 7, that future proof import must be omitted. No parent-node
statement dependency is added here, since doing so would create a DAG cycle.
No parent source is edited. This is definition reuse, not a circular proof:
the delivered statement's proof uses none of the parent theorem.

Edge cases checked before finalizing:

- Empty X: H(X,Y) is the marked point, and maps from Z times the empty X
  form a singleton; the adjunction and formulas impose no nonemptiness.
- Empty Y: if X is empty the preceding case applies; otherwise H has no
  vertices, and the formulas continue to describe the empty mapping sets.
- Empty Z: both hom sets are singletons, with all edge conditions vacuous.
- Degree zero and parameter maps to degree zero: flat edges are precisely
  degeneracies, and the construction explicitly marks all mapping degeneracies.
- For `X=(Delta^1)^sharp`, `Y=(Delta^1)^flat`, the identity underlying map
  is not even a marked vertex of H. For flat X and flat Y, the parameter
  projection `X × Delta^1 -> Y` gives an unmarked H edge when its identity
  parameter edge has nondegenerate image. Thus the sharp test is not a
  vacuous condition and does not accidentally mark all mapping edges.
- For a marked z, all three endomorphisms of [1] (identity and two constants)
  preserve its marking, which is the nontrivial direction of the final iff.
- The declaration is polymorphic in u, including u=0; no relation between
  unrelated universes or extra Kan/quasicategory assumptions is imposed.

Searches (2026-10-17):

1. `msearch.py Q46 lem-coef-marked-internal-hom leanfinder "marked simplicial sets
   internal Hom exponential adjunction simplices maps from X times minimally
   marked simplex"`: eight hits, including `CategoryTheory.SimplicialCategory.sHom`,
   `SSet.instMonoidalClosed`, and simplicial-thickening mapping objects. These
   concern unmarked internal Homs or already assumed enrichment, not this result.
2. `msearch.py ... loogle "SSet, CategoryTheory.ihom"`: eight unmarked
   quasicategory/Kan/fibration results. No marked internal Hom theorem.
3. `msearch.py ... grep "MarkedSSet|MarkedSimplicial|marked.*[Hh]om|marked simplicial"`:
   only an unrelated nonunital-algebra-hom simp comment; no Mathlib implementation.
4. `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for those patterns
   and the item id: no marked simplicial implementation or exact theorem.
   `dag/lean_names_upstream.json` likewise has no relevant marked declarations.
5. `rg` in the shared `lean/Sheaf` found `MarkedPointCartesianModel` and its
   consumers. Read all its foundational definitions and stronger model statement;
   reused the definitions rather than making a second construction. Further
   searches for `internalHomMap`, `internalHomEvaluation`, `mapFlat`, and
   `internalHom` found no existing standalone statement matching this item.
6. Read Mathlib `SimplicialSet/Monoidal.lean`, `StdSimplex.lean`, and
   `Monoidal/Closed/FunctorToTypes.lean`: the available closed structure is
   unmarked and does not express the marked transpose criterion.
7. Source check: opening paragraph of HTT section 3.1.3, printed p.154;
   author-hosted PDF fetch timed out, but the same primary text was available
   in the search excerpt of the Rochester-hosted HTT PDF
   https://people.math.rochester.edu/faculty/doug/otherpapers/lurie-htt2.pdf .
   It asserts the marked Cartesian closure and flat/sharp mapping properties.
   The explicit elementary proof remains the node's seven-step proof.

There are no statement disputes, new nodes, dependency repairs, or statement
corrections. The final module has no new axiom, opaque data, private notation,
auto-bound variable, or definition using sorry.

## Second reading by Q141

Independent maintainer reading on 2026-10-17 of immutable delivery
81d040bee926521c901a0d05586a4f7c6064bee9. This reader did not write or previously
second-read this delivery. The reading uses the snapshot, not the current clone's
version of the delivered module. The Q141 and slopmaster2 clones were read only
for dependencies and Mathlib context.

Sources and dependencies read:

- Read packet.md, check-brief2.md in full, the snapshot item, both complete
  statement-dependency records, report, delivered module and all its docstrings.
  Read coord/brief-stage2.md, delivery-errors H1-H13, and stage-2 import rule 3.7.
- Read the author-hosted HTT PDF, https://www.math.ias.edu/~lurie/papers/HTT.pdf,
  Section 3.1.3 opening paragraph, printed p.154 (PDF page 172, zero-based 171),
  before Remark 3.1.3.1. It gives marked Cartesian closure, evaluation and the
  flat/sharp mapping properties. Corollary 3.1.4.4, printed p.162 (PDF page 180),
  is the stronger simplicial model-category assertion; it is not needed here.
  Browser text extraction succeeded; the optional screenshot fetch failed.
- Read the complete EnhancedDiagramsCones module and the size-convention record.
  The former uses Mathlib SSet, standard simplices and degreewise products; the
  latter is explicitly metatheoretic and has no declaration to import.
- Read def-weil-pbc-simplicial-set and its exact Mathlib matches: SSet in Basic,
  degenerate/nonDegenerate in Degenerate, Subcomplex in Subcomplex, Finite in
  Finite; also stdSimplex/objEquiv in StdSimplex and the product formulas in
  Monoidal. The degeneracy condition for an edge is exactly the image of sigma_0.
- Read MarkedPointCartesianModel, including Marked, Hom, markedCategory, flat,
  sharp, product, productMap, flatMap, flatSimplex, productLeft, mapFlat,
  internalHom and its actual degeneracy proof, plus CartesianModelStatement
  and marked_point_cartesian_model. Confirmed the owning definitions against
  current server source through scompile.py --source.

Clause-by-clause comparison (all pass):

1. Objects: Marked consists of SSet.{u}, a subset of degree-one simplices and
   inclusion of every sigma_0 edge. Hom is a subtype of natural transformations
   preserving that subset. No fibrancy, Kan, quasicategory, nonemptiness or
   finiteness assumption is present in the delivered theorem.
2. Products and markings: product uses the degreewise tensor product and the
   conjunction of the two marking predicates. flat uses range sigma_0; sharp
   uses all edges. These are existing definitions, not private copies.
3. H_n and restriction: mapFlat is (flatSimplex composed with productLeft X),
   opposited and composed with yoneda.obj Y. Its n-simplices are exactly marked
   maps X times the flat standard n-simplex to Y, and its operators precompose
   by the identity of X times the simplex map. internalHom has this underlying
   simplicial set and tests every marked X edge against EVERY interval edge.
   This is exactly the additional sharp-interval marking condition. Its
   degeneracy field is real data and proves the marked-set construction clause.
4. Functoriality: internalHomMap a b sends h to productMap a (identity) followed
   by h and b. Its real structure proofs check restriction and marking
   preservation. The first two theorem conjuncts give identities and composition;
   a':X''->X' followed by a:X'->X is correctly reversed under internalHomMap.
5. Adjunction and evaluation: E is an equivalence for all X,Y,Z. The third
   conjunct specifies its forward function in every degree by evaluation at
   id_[n]. In particular E applied to the identity of internalHom X Y is the
   required marking-preserving evaluation map. This is not an arbitrary
   equivalence with an unspecified underlying function.
6. Ordinary inverse transpose: the fourth conjunct specifies h_z in every
   n,m,x,alpha by F_m(Z(alpha)z,x). The map alpha has domain m.unop and codomain
   n.unop, and a.op acts in the correct direction. Equivalence supplies both
   inverse identities. These are the ordinary simplicial transpose formulas.
7. Naturality: the fifth conjunct handles Z'->Z, X'->X and Y->Y' simultaneously.
   Both sides are marked maps product Z' X' -> Y'. This includes each of the
   three individual naturalities by specializing the other maps to identities.
8. Marking equivalence: the last conjunct quantifies over every underlying
   simplicial g, not just a marked map. Its right side tests evaluation on all
   marked pairs (z,x). For any interval endomorphism alpha, naturality identifies
   h_z(x,alpha) with h_{Z(alpha)z}(x,id). The only three such endomorphisms are
   the identity and the two constants. Their images of marked z are marked,
   since the constants factor through degree zero. This proves the converse
   implication as well as the immediate forward implication; the iff is exact.
9. Size: Marked.{u}, mapFlat:SSet.{u} and internalHom:Marked.{u} keep degree sets
   in Type u. SimplexCategory is small, stdSimplex uses ULift of finite ordinal
   maps, and function sets and the countable natural-transformation conditions
   stay at u, including u=0. Choosing a common universe imposes no silent
   equality of otherwise independent site universes.

Proof and dependency audit:

Recomputed the seven node steps: restriction and degenerate mapping edges;
pre/postcomposition; simplicial and marked evaluation; flat transpose through
constant edges; the three-endomorphism sharp test; the two inverse identities
and simultaneous naturality; and the same-universe bound. They use exactly the
cited simplicial definitions and size convention. proof_deps is exactly the
union of the uses lists. The theorem docstring carries all seven steps.

The imported model module owns real foundational definitions; no assertion of
its model theorem is used as a hypothesis or in the proof plan. Its exponential
fields do not state this entire standalone result with the inverse formula,
functor laws, naturalities and marking iff. The parent DAG proof cites this
item, so adding a future reverse proof import to the parent module would cause
a module cycle. The worker explicitly lists its omission under stage-2 rule
3.7. Definition reuse here creates neither a circular mathematical proof nor
a missing independent DAG prerequisite. No helper, dependency repair, source
statement correction, or citer audit is required.

Independent duplicate searches used rg with exponential, CartesianClosed,
marked simplicial, MarkedSSet, marked.*exponential, internalHomMap and
marked_internal_hom in Q141 lean/Sheaf, slopmaster2 WeilConjectures and Mathlib
AlgebraicTopology. Read the owning marked definitions and model statement,
Mathlib's unmarked Monoidal and FunctorToTypes interfaces. Apart from the
current delivery's own module, no exact duplicate was found. Cochain internal
Homs and unmarked closure do not give this result. The worker's recorded
semantic, type-pattern and text searches are retained above as historical
search evidence; their Q46 labels are not claims of new Q141 tool invocations.

Edge cases checked:

- Empty X gives the terminal marked mapping object, even for empty Y.
- Empty Z gives singleton hom sets. Empty Y with nonempty X has no mapping
  vertices; maps from empty products are still covered.
- Degree zero and constant simplex operators are included; every degenerate
  mapping edge factors through X and therefore passes the sharp test.
- Sharp Delta^1 to flat Delta^1 excludes the identity underlying map already
  at vertices. With X a point and Y flat Delta^1, the nonconstant parameter
  edge is an unmarked mapping edge. Thus neither marking predicate is vacuous.
- Minimal/maximal markings and u=0 impose no exceptional hypotheses.

Mechanical and compiler checks:

The record's lean.statement equals the complete source signature after only
whitespace flattening, with every symbol and binder unchanged. Both delivered
declarations are listed and have source-place/blueprint docstrings. There is
one sorry, the proof of the named theorem. internalHomMap has actual data and
only the necessary structure-field proofs; no additional local theorem is
proved. No hollow definitions, arbitrary-map substitutes, private notions,
auto-implicit variables, unbound universes, lines over 100 characters or
pro-etale substitute were found. The imported EnhancedDiagramsCones module is
the recorded public dependency, so its explicit import is legitimate.

Reproduced the sole delivered file with:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py Q141 lem-coef-marked-internal-hom /home/ubuntu/weil-launcher-nt/reviews-stage2/Q141__lem-coef-marked-internal-hom__81d040bee926/snapshot/lean/Sheaf/AlgebraicTopology/MarkedInternalHom.lean

Exit 0, no diagnostics: sandbox Sheaf/Stage2/Sandbox0.lean, 1.4 s; library
Sheaf/AlgebraicTopology/MarkedInternalHom.lean, 1.5 s. The installed wrapper
currently runs the server side-overlay compiler (rather than the older local
lcompile route), with private artifacts under /dev/shm/nt-tmp and the normal
60-second per-file limit. This independently reproduces the older Q46 report's
recorded clean compile, using the Q141 immutable file and current dependencies.
No lake/global build, direct ssh command, Git mutation, project-clone edit or
live Lean write was performed. Only the prescribed wrapper accessed the server.

Findings and fixes:

H11 / H1 report requirement: the delivered Q141 heading contains only a policy
placeholder, not a real independent reading. The retained Q46 section describes
a different immutable head and has corrupted source references (“Remark the
project server”, “Corollary the project server”). The complete report replacement
preserves the Worker report and replaces both obsolete sections with this actual
independent Q141 reading and accurate source/compile evidence. No Lean or node
change is needed. The statement and mathematics pass.

WANTED: archive the author-hosted HTT PDF in literature/; it is not included in
the supplied read-only literature checkout. The source was read online for this
review, and the elementary proof remains explicitly supplied by the node.
