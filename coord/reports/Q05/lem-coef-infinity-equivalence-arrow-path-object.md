## Worker report

This stage-2 delivery states `SSet.Marked.equivalence_arrow_path_object` in
`Sheaf.AlgebraicTopology.EquivalenceArrowPathObject`. It constructs the sharp-interval
exponential as a functor and its two endpoint maps with real degreewise data. The main
postponed proof is the named theorem, with the node's five proof steps in its docstring.
The maintainer replacement also postpones seven construction laws as named theorems;
all map data remain explicit.
There are no new DAG nodes, dependency repairs, or statement corrections.

The earlier Q160 merge recorded in the ledger was this item's stage-1 proof split.
The assigned node has no Lean record on the shared snapshot. The preserved Q05 sandbox
had only dispatcher briefs; this delivery supplies its missing stage-2 statement.

Clause-by-clause reading:

- "For any small quasicategory C": `(C : SSet.{u}) [Quasicategory C]`, with `universe u`
  explicitly bound and `autoImplicit false`. There is no vertex, inhabitance, chosen
  object, or constraint on `u`.
- "W = (C-natural)^((Delta1)-sharp)":
  `equivalenceArrowFunctor.obj (natural C)`. The functor's object field is exactly
  `internalHom (sharp (Δ[1] : SSet.{u})) X`; it uses the dependency's exponential,
  without defining a replacement internal Hom or replacement marked simplicial set.
- "V is its underlying simplicial set":
  `(equivalenceArrowFunctor.obj (natural C)).underlying` everywhere in the theorem.
- "V is the full subcategory of Fun(Delta1,C) on equivalence edges": the first
  conjunct gives an isomorphism to
  `(Enhanced.equivalenceDiagrams (Δ[1] : SSet.{u}) C).toSSet`.
  The dependency defines this as `Enhanced.fullSubcomplex ((ihom Δ[1]).obj C)` on
  diagrams carrying every interval edge to an equivalence. The interval has only its
  nondegenerate 0-to-1 edge and two degenerate edges, so this is exactly the stated vertex predicate.
  Simplicial maps preserve degenerate edges, which have degenerate inverse triangles.
  The comparison is fixed on all degrees: for `n m`, `h`, `a : n ⟶ m`, and `x` in
  the interval's m-simplices, its underlying functor simplex evaluates to
  `h.val.app m (x, stdSimplex.objEquiv.symm a.unop)`. Thus it is the canonical
  forgetful comparison onto the full subcategory, including all higher simplices.
- "W = V-natural": the second conjunct is the equality of marked simplicial sets
  `equivalenceArrowFunctor.obj (natural C) = natural (...).underlying`.
  It identifies the marking as well as the underlying simplicial set, using the
  dependency's natural marking and its `natural_marking` characterization.
- "The endpoint map W -> C-natural x C-natural is a model fibration": the third
  conjunct is `(cof ⊓ weak).rlp (equivalenceArrowEndpoints (natural C))`.
  This is precisely `CartesianModelStatement.fibrations`, not an unmarked Kan
  fibration. `equivalenceArrowEndpoint X i` evaluates a marked map on the constant
  interval n-simplex at `i` and the identity n-simplex. `equivalenceArrowEndpoints`
  pairs the restrictions in order 0,1, using `Marked.product` and its product marking.
  Mark preservation follows directly from `internalHom.marking`; it uses no theorem
  choice or unspecified map.
- "These constructions are natural in C": `equivalenceArrowFunctor` acts by
  actual postcomposition `h ≫ f`, with its identity and composition fields supplied.
  For every quasicategory D and every simplicial map `F : C ⟶ D`, the final conjunct
  gives `f : natural C ⟶ natural D` with `f.val = F` and the endpoint square
  `equivalenceArrowFunctor.map f ≫ equivalenceArrowEndpoints (natural D) =
  equivalenceArrowEndpoints (natural C) ≫ productMap f f`.
  A marked map is a subtype of its underlying map, so `f.val = F` uniquely determines
  `f`; this is not an arbitrary map or extra assumption. The degreewise comparison
  formula above commutes with postcomposition and therefore identifies this action
  with the usual action on the full equivalence-arrow subcategory. All its markings
  are retained.
- "Every input universe, including empty C": all simplex types, markings and
  internal Homs are in `u`, with no equality to a fixed universe. For the empty
  simplicial set each `Δ[1] × Δ[n]` is inhabited, so there is no map to C and V and
  W are empty in every degree. The endpoint target is empty too; the lifting proof
  in the docstring applies without choosing a point. For C = Delta0 the construction
  has the unique constant arrow, with its degenerate marked edge. For the nerve of
  an ordinary category with a noninvertible arrow, that arrow is excluded while
  all identity arrows and all invertible arrows remain. These cases check that the
  comparison uses the full subcategory of equivalence objects and does not retain
  only the core of that arrow category.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.equivalenceDiagrams`, `fullSubcomplex`, `IsEquivalenceEdge`, and
  Mathlib's `ihom` and `Quasicategory`, reexported by this module. I read their full
  definitions/docstrings, including the two inverse-triangle equations.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `Hom`, `markedCategory`, `flatSimplex`, `sharp`, `natural`,
  `internalHom`, `product`, `productMap`, `cof`, `weak`, and
  `CartesianModelStatement.fibrations`. The proof plan uses
  `marked_point_cartesian_model`, especially its exponential formula, natural
  marking, fibrant-object characterization and Cartesian pushout-product fields.
  The entire model-statement signature and its proof docstring were read. The
  lifting class in the new theorem is the exact one recorded there.

Source checked: Lurie, Higher Topos Theory,
https://www.math.ias.edu/~lurie/papers/HTT.pdf, Section 3.1.3 opening internal-Hom
adjunction and flat/sharp mapping formulas (printed p. 154), Proposition 3.1.4.1
(printed pp. 160-161), and Corollary 3.1.4.3 (printed pp. 161-162). The browser
fetch timed out; a copy was fetched into this sandbox's scratch directory and the
specified pages were read through its text extraction. The marked endpoint assertion
is the node's explicit adjunction/pushout-product consequence of these results.

Searches performed with `msearch.py Q05 lem-coef-infinity-equivalence-arrow-path-object`
(the unmodified tool result records are also preserved in `searches.jsonl`):

- LeanFinder: "The full subcategory of equivalence arrows of a quasicategory is the
  marked interval internal hom and its endpoint projection is a model fibration".
  Eight results concerning `SSet.modelCategoryQuillen` generating cofibrations and
  fibrations; none is the marked theorem.
- LeanSearch: "The equivalence arrow full subcategory of Fun(Delta1,C) is the marked
  sharp interval exponential and its endpoint map is a fibration". Eight results:
  ordinary arrow-category equivalences, abstract fibrant-object instances and
  exponentiable morphisms; none states this assertion.
- Loogle: `SSet.Marked.internalHom, HomotopicalAlgebra.PathObject` returned no hits
  and reported the project-only first identifier unknown. This is not positive
  search evidence. The corrected query
  `HomotopicalAlgebra.PathObject, SSet.Quasicategory` returned no hits without error.
- Mathlib grep: `equivalence.*[Aa]rrow|marked.*[Ee]ndpoint|[Pp]athObject` restricted
  to `AlgebraicTopology`, 21 hits in abstract path objects and their homotopies.
  I read `ModelCategory/PathObject.lean`; it specifies abstract diagonal/retraction
  data and cannot replace this marked interval and full-subcategory statement.
- Project/source/name searches: `equivalenceArrow|equivalence_arrow|marked.*[Ee]ndpoint|
  lem-coef-infinity-equivalence-arrow-path-object` in `lean/Sheaf`, upstream
  `WeilConjectures`, and `dag/lean_names_upstream.json`. The existing marked endpoint
  prism generators and the Segal-space equivalence-arrow constructions are different
  notions. `InfinityFunctorPushout` cites this node only in its proof plan. No existing
  declaration states the item or constructs these endpoint maps. Additional targeted
  searches for internal-Hom maps, evaluation, natural maps and equivalence preservation
  found no reusable sharp-interval endpoint declaration. The existing natural marking,
  internal Hom and full subcategory are reused rather than copied.

No STATEMENT-DISPUTED issue was found. The raw statement and all dependencies, proof
steps and metadata are unchanged; only the item's Lean record is supplied. Compilation
and the required dry-run/preflight are run through the prescribed wrappers. The
maintainer's independent delivery review supplies the independent mathematical reading.

Validation: `scompile.py Q05 lem-coef-infinity-equivalence-arrow-path-object
lean/Sheaf/AlgebraicTopology/EquivalenceArrowPathObject.lean` completed successfully,
with no errors or warnings: sandbox check 14.4 seconds, library-name check 12.0 seconds.
The original module had one theorem with `sorry` and three explicit helper definitions.
The maintainer replacement has six data definitions and eight named theorems, each
proved only by `sorry`, and no diagnostic declarations. Maximum source width is below 100 characters.
A comparison of the node copy to the shared original finds only the `lean` field changed.

WANTED: archive Lurie, Higher Topos Theory, https://www.math.ias.edu/~lurie/papers/HTT.pdf;
Section 3.1.3 and Proposition 3.1.4.1 / Corollary 3.1.4.3 are used here.

## Second reading by Q05

Independent maintainer second reading, 2026-10-17. I did not write or previously
second-read this delivery. This section is supplied by the maintainer reviewer,
not attributed to an unperformed Q05 worker review. I read the immutable packet,
all three snapshot node records, the delivered module and worker report, both
recorded dependency modules in the read-only Q05 clone, and the source places.
The disclaimer formerly under this heading was not a second reading (H1/H11).

Clause-by-clause verdict:

1. The only input assumption is `(C : SSet.{u}) [Quasicategory C]`. All variables
   and the arbitrary universe u are bound. No inhabitance, chosen vertex, Kan
   condition, or additional model structure is assumed.
2. W is exactly `internalHom (sharp Δ[1]) (natural C)`, through the object field
   of `equivalenceArrowFunctor`. V is its underlying simplicial set. These reuse
   the recorded marked objects, products, natural marking and internal Hom.
3. The first conjunct identifies V with the full simplicial subcategory
   `Enhanced.equivalenceDiagrams Δ[1] C`. I read `IsEquivalenceEdge`'s two inverse
   triangles, `fullSubcomplex`'s all-vertices condition and `equivalenceDiagrams`'s
   evaluation of every interval edge. For Δ[1] this excludes precisely the
   non-equivalence arrows; degenerate interval edges impose no additional condition.
   The isomorphism is normalized by the displayed evaluation formula for all n,m,a,x.
   It is therefore the forgetful comparison, not an arbitrary isomorphism or a core.
4. The second conjunct identifies the actual marked object with `natural V`.
   I checked the dependency's `natural_marking` and `fibrant_objects` fields,
   including its explicit degenerate-edge disjunct. Degenerate edges are equivalences,
   so this does not enlarge the intended marking.
5. The third conjunct is `(cof ⊓ weak).rlp` of the ordered endpoint pair. I checked
   the definitions of cof, weak, product and productMap, and the exact
   `CartesianModelStatement.fibrations` field. This is the marked Cartesian model
   fibration, not an unmarked Kan fibration or a Cartesian fibration over C × C.
   Endpoint i really evaluates the interval at the constant simplex i and the
   parameter at its identity. The pairing is ordered 0 then 1 with the product marking.
6. The last conjunct quantifies over every D and simplicial functor F, constructs
   its marking-preserving lift f with `f.val = F`, and asserts the endpoint square.
   The subtype representation makes f unique. `equivalenceArrowFunctor` is actual
   postcomposition with identity and composition laws; the comparison formula
   automatically commutes with it. Thus naturality is fully retained.
7. Every input universe is allowed. The constructions involve finite simplices,
   subtypes and function sets in u; there is no hidden equality of universes.
   For inputs at different sizes one works in a common enlarged universe, using
   the marked-model dependency's enlargement assertion. Empty C is allowed.

I checked each of the five proof-plan steps against the cited statements. Step 1
is the flat-parameter marking calculation and the dependency's full-subcategory
construction. Step 2 identifies the two constant components of the interval boundary
and its exponential with the product. Step 3 transposes a lifting problem to j □ i,
uses exactly the model dependency's pushout-product and fibrant-object assertions,
and transposes the extension back. Step 4 repeats this with the empty-to-interval
cofibration for both sharp and flat intervals; this establishes the natural marking
and the ambient functor quasicategory without an extra hypothesis. Step 5 transports
the inverse triangles by F and uses the same degreewise formulas. No additional
non-elementary input or missing DAG prerequisite was found.

Sources actually read: online HTT Section 3.1.3 opening internal-Hom formulas,
printed p.154 (PDF p.171); Proposition 3.1.4.1, printed pp.160-161 (PDF pp.177-178);
Corollary 3.1.4.3, printed pp.161-162 (PDF pp.178-179); and the point-case explanation
in Remark 3.1.4.6. The endpoint assertion is the node's stated pushout-product
consequence of those results. I also read the archived Scholze Six-Functor Formalisms,
Lecture II, Definitions 2.1-2.2 and facts (1)-(7), printed pp.13-15, for the dependency's
quasicategory, functor and equivalence conventions.

Edge cases checked: empty C gives empty W,V and endpoint target; each domain
Δ[1] × Δ[n] is nonempty, including n=0. C=Δ[0] gives its constant arrow.
For N([1]), only the identity arrows are objects of V, but the noninvertible square
between those identities remains a transformation. This is a full arrow subcategory,
not a Kan core. For a discrete category the endpoint map is the diagonal; for a
one-object groupoid the nonidentity invertible arrows remain. No characteristic,
geometric finiteness or pro-etale substitution occurs in this item.

Independent duplicate searches used different formulations: Loogle
`"Quasicategory", "exponential"` returned zero hits; LeanFinder queried the sharp
interval exponential and marked endpoint fibration, returning nerve, horn/Segal,
simplicial thickening and unit-Hom declarations, none an exact match. The attempted
LeanSearch query returned HTTP 403 and is recorded as unavailable, not as no match.
I searched Mathlib/AlgebraicTopology, upstream WeilConjectures, the Q05 lean/Sheaf
modules and dag/lean_names_upstream.json for equivalence-arrow, marked evaluation,
endpoint/exponential and exact declaration names. I read Mathlib's
ModelCategory/PathObject.lean:45-145: it supplies abstract path-object data and
presupposes the object, so it cannot replace this construction. SegalSpace's
`equivalenceArrows` is a different model and is not substituted. The existing
marked internal Hom and Enhanced full subcategory are reused. The worker report
contains all three required search kinds.

Mechanical repairs in this complete replacement:

- H6 (and the well-definedness provision of brief-stage2 §2): moved the inline
  naturality, marking and functor-law proofs to seven named construction-law
  theorems with source/blueprint and proof-plan docstrings, all with `sorry`.
  The six definitions retain explicit simplex functions, postcomposition and
  endpoint pairing. No data are chosen from a mere existence theorem; no `sorry`
  occurs in a definition. These helpers belong to this node's canonical
  construction and are recorded in lean.declarations under the permitted helper rule.
- H1/H11: replaced the non-reading disclaimer with this actual independent reading.
- Corrected the garbled source labels and the report's use of "identity edge" for
  the nondegenerate interval edge; added the missing explicit WANTED source line.

The mathematical node statement, all dependencies, proof steps, source, main theorem
signature and main proof-plan docstring are unchanged. Only the Lean declarations
list changes in the JSON record. The main lean.statement is verbatim equal to the
replacement file's signature. Imports are the two used statement dependencies,
all declarations have source/blueprint docstrings, autoImplicit is false, maximum
line width is 98, and every theorem body is exactly `by sorry`.

Compiler evidence: the prescribed scompile.py wrapper successfully reproduced the
immutable original in sandbox and library modes, 1.9 s each, with no errors or
warnings. It then compiled the complete replacement in sandbox mode in 1.8 s and
library mode in 2.3 s, with no errors or warnings. The currently installed wrapper
is server-only and invokes the server's private side-overlay compiler; the local
mode described in the brief is no longer exposed. I used only the prescribed
wrapper, with its normal confirmation, and did not invoke SSH directly, build the
library globally, write live Lean files, edit a clone, or change the delivery head.
Verdict: FIX; the mathematics is accepted with these complete mechanical repairs.
