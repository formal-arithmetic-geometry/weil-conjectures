## Worker report

The module `Sheaf.CategoryTheory.DgDerivedAdmissibleTriangles` states
`CategoryTheory.DgAlgebra.nonempty_derivedAdmissibleTriangles`. It has one theorem,
whose proof is `sorry`. `DerivedAdmissibleTriangles` is a structure packaging this
node's assertions; it constructs no object by choice and postulates no additional
hypothesis on the algebra. No natural-language statement was corrected.

Clause-by-clause correspondence:

- The explicit `universe u` and `A : Algebra.{u}` implement the size convention.
  `Algebra` is the existing monoid object in integer cochain complexes of
  `ModuleCat.{u} (ULift.{u} ℤ)`. Monoid associativity/unit and the chain-map condition
  on multiplication are exactly the associative unital DG algebra and signed
  Leibniz rule over the integers. Integer modules are equivalent to abelian groups;
  the universe lift changes no coefficients or algebraic condition.
- `RightModule A`, from the same dependency, is the existing module object in the
  reversed tensor category. Its underlying differential squares to zero, and the
  action is a chain map on M tensor A, giving precisely the sign (-1)^degree(m).
  No commutativity, boundedness, flatness, countability or nonzero assumption occurs.
- `HomotopyCategory A` and `homotopyQuotient A` are the existing quotient by
  degree-minus-one right A-linear chain homotopies. `Derived A` and `Q A` are the
  actual Gabriel--Zisman localization at underlying quasi-isomorphisms.
  `localization`, `factorIso` and `isLocalization` assert that the homotopy category
  localizes to that very category at maps inducing isomorphisms on every
  `HomotopyStructure.cohomology n`. The factorization is a natural isomorphism,
  not a newly chosen arbitrary identification of objects or arrows.
- The `homotopy` and `derived` fields are existentially supplied structural data,
  not assumed typeclasses in the theorem's hypotheses. `HomotopyStructure` fixes
  signed shifts with unchanged right action and the iff with DG cone triangles.
  `DerivedStructure` fixes the same shifts and cone predicate on the localization,
  and includes `Pretriangulated` and `IsTriangulated` (TR1--TR4). This is the stated
  triangulation. The imported standard data also supplies its usual small
  coproducts; that field is part of the already-landed definition of D(A,d), not
  an additional assumption on A in this theorem. Stacks Tag 09QI,
  lemma-derived-products (1)--(2), supplies these coproducts as direct sums of DG
  modules; its proof computes maps into K-injective resolutions.
- `commShift : localization.CommShift ℤ` and
  `exact : localization.IsTriangulated` are exactness of the homotopy localization:
  its coherent shift comparison and preservation of distinguished triangles.
  The new `shiftComparison` field pins that comparison for EVERY integer n,
  modules M,S and `e : ShiftComparison A n M S`. Its component is exactly
  localization.map of the inverse homotopy shift identification, then
  factorIso.hom at S, then the derived shift identification, then the shifted
  factorIso.inv at M. Thus `exact` uses the induced comparison specified in the
  return, rather than an arbitrary CommShift structure.
- `admissible` quantifies over every K,L,M and every
  `S : GradedSplitShortExact A K L M`. The existing S contains the SPECIFIED
  `inclusion` and `projection`, degreewise injectivity, surjectivity and exactness,
  and an additive degree-zero section with its right A-linearity and right-inverse
  identity. This is precisely a short exact sequence split on graded right modules.
- The conclusion is an actual morphism
  `δ : (Q A).obj M ⟶ ((Q A).obj K)⟦(1 : ℤ)⟧` and membership of
  `Triangle.mk ((Q A).map S.inclusion) ((Q A).map S.projection) δ` in
  `distTriang (Derived A)`. Thus both first arrows are literally the images of the
  supplied maps, not unspecified isomorphic arrows.
- S's section is an additive homogeneous family, not a DG morphism: there is no
  equation involving its differential. No compatibility with differentials is
  required. An A-linear retraction is recoverable from this section and the exact
  kernel identification, so no second splitting assumption was added.

Dependency declarations read and reused:

- `def-weil-size-convention` is explicitly recorded as a metatheoretic convention
  with no declaration. Explicit universe parameters implement it.
- `def-weil-triangulated-category`: Mathlib's `CategoryTheory.Pretriangulated`,
  `CategoryTheory.IsTriangulated`, `Functor.CommShift`, `Functor.IsTriangulated`
  in Triangulated/Pretriangulated, Triangulated/Triangulated and Triangulated/Functor.
- `def-sfb-dg-derived-category`: `CategoryTheory.DgAlgebra.Algebra`, `RightModule`,
  `underlying`, `Derived`, `Q`, `ShiftComparison`, `ConeComparison`, `DerivedStructure`
  from `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`. Read its full source.
- `def-sfb-dg-homotopy-structure`: `homotopyRel`, `HomotopyCategory`,
  `homotopyQuotient`, `HomotopyStructure` from
  `Sheaf.CategoryTheory.DgAlgebraHomotopyStructure`. Read its full source.
- `def-sfb-dg-graded-split-short-exact`: the already-defined structure
  `CategoryTheory.DgAlgebra.GradedSplitShortExact` is used, from
  `Sheaf.CategoryTheory.DgGoodCharacterEmbedding`. Its full signature was read:
  it gives exactly the admissible sequence needed here. Its embedding theorem
  is not used and is no longer a statement dependency. The new definition node
  records this existing structure directly without using the embedding theorem.

The statement dependencies now cite the two landed definition nodes for the DG
derived and homotopy structures and the new definition node recording the already
existing graded-split sequence structure. The theorem node
lem-sfb-dg-good-character-embedding is not a statement dependency. No structure
was redeclared, no dependency module was repaired, and the node statement,
proof and proof dependencies are unchanged.

Proof imports retain the stated proof plan: DgCompositeConeContraction,
HomologySequence, Localization.Triangulated, Triangulated.Subcategory, with the
triangle-morphism isomorphism lemma in the publicly imported Pretriangulated file.
The cone-rotation node has no recorded Lean module in the inspected base and is
therefore referenced in the proof docstring without an invented import. All seven
proof steps are in the theorem docstring, including every use of a named node.

Edge cases checked against the definitions and source: A=0 (all unital modules
then vanish), zero modules and the zero exact sequence, identity-inclusion and
identity-projection sequences, complexes with negative degrees and unbounded in
both directions, noncommutative DG algebras, and sequences with a graded section
that is not closed. None is excluded. In particular a cone extension may have
nonzero off-diagonal differential: the section is still admissible. All integers
are allowed as shift and cohomology degrees. Components use Type u and the formal
localization's larger morphism universe; no equality of unrelated universes is
imposed. There are no auto-implicit variables or file-local notations/instances.

Searches performed:

- msearch LeanFinder: "Derived category of right differential graded modules over
  a differential graded algebra and graded split exact triangles" returned ordinary
  DerivedCategory, Qh and triangleOfSES declarations. Their signatures concern
  ordinary complexes in an abelian category and do not retain an arbitrary DG action.
- msearch Loogle: "Differential, GradedRing, Localization" returned 0 hits.
- msearch grep: "DGModule|DifferentialGraded|Graded.*Differential|ModuleObject"
  in Algebra returned only HomologicalBicomplex's graded-object constructor.
- msearch LeanSearch: "A graded split short exact sequence of right differential
  graded modules splits without commuting with differentials" returned the
  ordinary ShortComplex.Splitting API. It is not a DG graded splitting: using it
  in DG modules would require the section to be a chain map.
- msearch Loogle: '"Graded", "Splitting"' returned 0 hits.
- msearch grep: "GradedSplit|GradedMap|graded.split" in Algebra returned 0 hits.
- Local rg of Mathlib Algebra/Homology and CategoryTheory/Monoidal for DG module
  vocabulary found no specialized DG module-localization statement. Local rg of
  WeilConjectures and Sheaf found the landed DgAlgebra infrastructure and then
  GradedSplitShortExact in DgGoodCharacterEmbedding. Other graded splitting hits
  concerned Cartan--Eilenberg complexes and filtered-object symbols.
- Local rg for the item ID in WeilConjectures and dag/lean_names_upstream.json
  found no existing declaration. Local rg for DerivedAdmissibleTriangles and its
  theorem name found no collision. DAG searches found the already-landed
  def-sfb-dg-derived-category and def-sfb-dg-homotopy-structure; their exact modules
  are used. blueprint_refs.py search "graded split" and "dg derived" returned
  0 matching blueprint nodes. The repair adds a definition node recording the
  existing graded-split structure; it introduces no second Lean definition.

Source checked directly in literature/stacks-project/dga.tex:
definition-dga (multiplication as a chain map), definition-admissible-ses,
lemma-admissible-ses (09JU), proposition-homotopy-category-triangulated (09KJ),
lemma-the-same-up-to-isomorphisms (09KF), lemma-acyclic (09KW), and
 definition-unbounded-derived-category (09KX), including the universe discussion.
The theorem is consistent with the node and these sources; no disputed statement
or node fault was found.

Validation: the prescribed scompile.py checks the repaired statement module in
module mode against the live server library. Only the theorem uses sorry; the
structure has no postponed data. The delivery dry run also checks the existing
GradedSplitShortExact declaration named by the new definition node. The final
packet is compiled and preflighted before redelivery.


## Repair of returned head eb26d7870e01

H2: replaced stmt_dep lem-sfb-dg-good-character-embedding by
`def-sfb-dg-graded-split-short-exact`. Its record is existing:true,
branch:newtargets-dag, module:Sheaf.CategoryTheory.DgGoodCharacterEmbedding,
declaration:CategoryTheory.DgAlgebra.GradedSplitShortExact, as requested.
The source is Stacks 09JT. No Lean definition was duplicated. The existing
inclusion, projection, degreewise exactness and graded A-linear section fields
were reread and match this new node hypothesis by hypothesis.

H3: added `shiftComparison` for every n,M,S,e with exactly the returned equation.
The left side has source localization(q(M)[n]) and target localization(q(M))[n].
The right side first maps the inverse identification q(M)[n] to q(S), then uses
the factorization at S, the derived shift identification, and the shifted inverse
factorization at M. Both sides therefore use the same actual objects, shifts,
functor and factorIso; this pins the comparison used by the exactness field.
At n=0 or a zero module the same equation applies without a new restriction.
All previous hypotheses, cone comparisons and literal first arrows are retained.

The report and Lean docstrings now cite Stacks 09QI for the coproducts bundled
in the already-landed DerivedStructure. Read lemma-derived-products (1)--(2)
and its argument: Hom from a direct sum into a K-injective resolution is the
product of the individual Hom groups. No additional coproduct hypothesis is
imposed on A.

Compared the returned sandbox with the current read-only main node: only lean
and the previously added stmt_deps differed. Regenerated the node copy from the
current main record, preserving all other fields and replacing the theorem-node
reference as requested. The prescribed delivery wrapper builds the repaired
commit on current origin/sheaf-dag. No direct repository Git command was run.

## New nodes

`def-sfb-dg-graded-split-short-exact` records the existing
CategoryTheory.DgAlgebra.GradedSplitShortExact, without a new module. Its source
is Stacks dga.tex Tag 09JT, definition-admissible-ses (3). It packages specified
DG inclusion and projection, injectivity, surjectivity and kernel=image in each
degree, and an additive homogeneous right A-linear section. No section/differential
commutation is imposed. The graded retraction follows uniquely from exactness
and the section. Thus the statement is exactly admissibility with a chosen
splitting, not the unrelated character-embedding theorem.

Fresh searches for this repair: msearch LeanSearch for admissible short exact DG
right modules split on graded modules returned ordinary ShortComplex.Splitting
lemmas; Loogle for GradedSplitShortExact and grep for
GradedSplitShortExact|DGModule.*Splitting|GradedSplitExact returned zero Mathlib
hits. Local rg found only the existing structure and its theorem use in
DgGoodCharacterEmbedding; the DAG helper occurred only in the embedding theorem's
record, not a definition node. blueprint_refs.py search graded split short exact
returned zero matches. The exact search results are recorded in the new node's
mathlib_searches. Blueprint ancestry uses the item's inherited null ancestor and
prepends the item to its via chain.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
