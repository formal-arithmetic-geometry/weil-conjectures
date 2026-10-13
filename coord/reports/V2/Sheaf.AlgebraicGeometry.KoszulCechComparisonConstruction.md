## What changed

Proved `AlgebraicGeometry.koszulCech_basis_card`,
`AlgebraicGeometry.koszulCech_basis_degree`, and
`AlgebraicGeometry.koszulCech_evaluation_degree` in
`Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction`. The cardinality result
uses positivity of the cardinality of a nonempty finite set and `omega`; the degree
identity unfolds `ComplexShape.embeddingDownNat.f` and uses the same arithmetic; the
evaluation identity is integer ring arithmetic. Existing construction and comparison
definitions are unchanged.

## Proved and sorry left

Closed 3 holes: `koszulCech_basis_card`, `koszulCech_basis_degree`, and
`koszulCech_evaluation_degree`. The module still has 2 unproved declarations:
`koszulCechHomDiagram_exists` and `koszulCechCocone_exists`, both carried by
`def-sc-koszul-cech-comparison-construction`. Added 0 holes. No other theorem or
definition has a `sorry` introduced by this delivery. No new statements or nodes were
needed.

## No longer needed

No imports or DAG nodes were pruned. The proof uses only existing imports and elementary
finite-cardinality and integer arithmetic lemmas.

## Where the brief, the DAG or earlier work was wrong

No errors in the statement, DAG, or proof plan were found. The three elementary
arithmetic steps compile directly with the existing Mathlib API.

## Second reading by V2

1. Compared the entire sandbox module with the repository using `diff -u`.
   Only the bodies of the three arithmetic theorems differ. Every existing signature,
   definition, docstring, visibility, and import is byte for byte unchanged; there are
   no additional delivered modules or change records. Pass.
2. Compiled the delivered module with `lcompile.py`: exit 0, no warnings. Read every
   declaration and checked a scratch copy with `#print axioms` for all twelve declarations.
   The three closed theorems use only the permitted axioms; the other declarations use
   only those axioms and `sorryAx` from still-open construction/verification theorems.
   The only textual holes are the two reported named existence theorems, with source
   citations and natural-language proofs; no forbidden declaration or definition hole
   occurs. The unchanged choices are specified by object equalities and all component
   maps: the Hom diagram is fixed up to transport, and the cocone formula determines
   components because the denominator is invertible on the indicated principal open.
   They are not choices of unspecified existence witnesses. Pass.
3. No new or split-off statements occur. For the arithmetic proofs, checked Mathlib's
   `Finset.card_pos` and the integer embedding formula, and searched the project and
   upstream for the theorem names and related cardinality/degree facts. The proofs use
   the existing API directly. At cardinality one the tail degree is zero; at larger
   cardinality it is the negative of card minus one. The nonempty hypothesis is essential
   for both subtraction identities; when r is zero these hypotheses have no witnesses.
   The evaluation identity also holds for an empty J and arbitrary negative n. Pass.
4. The two positivity-plus-`omega` proofs and the `ring` proof are direct elementary
   reductions, without moving the target to a lower hole. Read all three Sheaf imports:
   ModuleHomComplex supplies the Hom construction, KoszulOpenSystem supplies tails,
   transitions and the open, and PrincipalOpenCechTotal supplies sections and comparison.
   HomologicalComplexLimits supplies degreewise colimits used by the public construction;
   no proof-only public import was added. No old proof dependency is unused: the node's
   old `proof_deps` is empty. The unit `sk-thm-picard-duality` has empty realized statement
   and step lists; the unchanged construction retains the prescribed Koszul-to-Cech route.
   No module or node is pruned. Pass.
5. Read `def-sc-koszul-cech-comparison-construction.json`, its full declaration list,
   statement, source, and unit record. The diagram, colimit, exterior basis, localization
   cocone sign and derived composite remain unchanged. This is an existing definition
   node with empty `proof`, empty `proof_deps`, and null `proof_origin`; the elementary
   arithmetic proofs introduce no node-level dependency or alternative construction
   route, so those fields need no change. There are no new nodes to validate. Pass.

Second reading changed only this report: made the zero added-hole count and the nodes
of the remaining holes explicit, and recorded the review. No Lean repair was needed.
