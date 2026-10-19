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

## Second reading by Q46

Independent maintainer reading, 2026-10-17, of immutable delivery
`e23266b5b3df9a899b749838c62c04e0d85e7ba2`. This reader neither wrote nor
previously second-read the delivery. Read packet.md, the full check-brief2.md,
the snapshot item and both statement dependencies, the delivered module, and
this report. Opened the actual dependency modules and exact definitions in the
read-only Q46 clone, and Mathlib sources in slopmaster2.

Clause-by-clause findings:

- Objects and simplices: `SSet`, `stdSimplex`, and `stdSimplex.objEquiv` are the
  dependency's Mathlib presheaves and ordinal maps, including degree zero.
  `Marked` and `Hom` in MarkedPointCartesianModel give precisely a subset of
  edges containing degeneracies and marking-preserving natural transformations.
- Products and flat/sharp markings: the existing `product` marks exactly the
  pairs of marked edges; `flat` uses the range of sigma_0 and `sharp` uses all
  edges. These are real constructions, reused without a second definition.
- Mapping object: `mapFlat = (flatSimplex ⋙ productLeft X).op ⋙ yoneda.obj Y`
  has exactly the node's marked-map sets and restriction operators.
  `internalHom` uses that underlying object and tests every marked X edge
  against every interval edge, exactly the sharp-interval extension condition.
  Its real degeneracy field includes every degenerate mapping edge.
- Variance: `internalHomMap` is the actual pre/postcomposition map; its structure
  proofs establish naturality and preservation of markings. The first two
  theorem conjuncts assert identity and composition with the correct reversed
  variance in X. There is no arbitrary map parameter replacing the construction.
- Adjunction: the existential E is an equivalence for every marked X,Y,Z.
  The third conjunct fixes its forward function on every simplex by evaluation
  at id_[n]. Taking g to be the identity yields the required marked evaluation.
  The fourth fixes the inverse at every n,m,alpha by F_m(Z(alpha)z,x).
  Equivalence supplies both inverse equations. These formulas specify the
  ordinary simplicial transpose rather than an unspecified bijection.
- Naturality: the fifth conjunct handles simultaneous precomposition in Z and X
  and postcomposition in Y. Its two sides have matching domains and codomains.
- Markings: the last conjunct quantifies over every underlying simplicial g,
  without assuming it marked. It tests evaluation on every pair of marked
  edges. For a marked z the two constant endomorphisms of [1] give degeneracies,
  and the third endomorphism is the identity. Thus the evaluation test implies
  the full sharp marking, as well as conversely. Neither direction is omitted.
- Size and hypotheses: all degree sets and marked objects remain at universe u;
  `stdSimplex` uses ULift of finite ordinal maps. No universe equality between
  independent objects is imposed beyond choosing their common universe. There
  are no Kan, quasicategory, fibrancy, finiteness, or nonemptiness assumptions.

Read the author-hosted HTT PDF at
https://www.math.ias.edu/~lurie/papers/HTT.pdf, Section 3.1.3, printed p.154
(zero-based PDF page 171; viewer page 172), before Remark 3.1.3.1. It states the
evaluation universal property and the flat/sharp mapping properties used here.
Also read Corollary 3.1.4.4, printed p.162, which concerns the stronger simplicial
model structure and is not needed for this elementary adjunction.

Edge cases: empty X gives the marked terminal mapping object; empty Z gives
singleton hom sets; empty Y is allowed (and has no maps from nonempty X).
The empty-X/empty-Y combination still has the unique empty map. Degree zero,
constant parameter maps, minimal and maximal markings, and u=0 are included.
For sharp Delta^1 to flat Delta^1 the identity underlying map fails the marked
vertex condition, so the marking check is substantive.

Independent searches with `rg` for `exponential`, `CartesianClosed`,
`cartesianClosed`, `marked.*exponential`, `marked simplicial`, `internalHomMap`,
and `marked_internal_hom` in Q46 lean/Sheaf, slopmaster2 WeilConjectures, and
Mathlib simplicial-set sources found the owning marked definitions in
MarkedPointCartesianModel and unrelated unmarked/cochain internal Homs.
Read its CartesianModelStatement exponential fields: these do not give this
standalone full statement, including inverse formula, functor laws, all
naturalities and the unmarked-g marking criterion. No exact duplicate found.
The worker's semantic and type-pattern searches are recorded above.

Dependency/import review: EnhancedDiagramsCones is imported; the size node is
an explicit metatheoretic convention, with no module. Simplicial-set primitives
are transitively imported. The marked definitions live in the downstream model
module, but the theorem does not use its model theorem. The documented omission
of the reverse future proof import is expressly allowed by stage-2 rule 3.7
for import cycles. No new mathematical prerequisite or dependency repair is
needed, and no source-based statement correction is made.

Checks: `lean.statement` equals the complete theorem signature verbatim.
Both declarations are recorded, have source/blueprint docstrings, and the
seven-step proof docstring covers the node. The sole theorem proof is `sorry`;
the helper has real data and only structure-field proofs. There are no hollow
definitions, local theorem proofs, private notions, auto-bound variables,
overlong lines, pro-etale substitutes, or extra axioms.

Compiler evidence: invoked the prescribed scompile.py with Q46,
lem-coef-marked-internal-hom and the absolute immutable snapshot module path.
The installed wrapper currently delegates to the server side-overlay compiler.
It returned exit 0: sandbox Sheaf/Stage2/Sandbox0.lean, 1.7 s; library
Sheaf/AlgebraicTopology/MarkedInternalHom.lean, 2.2 s; no diagnostics.
No global build, direct ssh command, repository edit, Git mutation, or live
Lean write was performed by this reader.

Finding and correction: H11 (also the substantive report requirement in H1):
the delivered second-reading section explicitly described a worker self-check,
not an independent reading. Replace that section with this actual independent
reading, preserving the Worker report. The complete replacement report is the
only fix; the Lean module and node record need no changes.
