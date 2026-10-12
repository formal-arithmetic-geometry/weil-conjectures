## What changed

Proved AlgebraicGeometry.etaleInverseImageModuleLinearCriterion from two new, strictly partial
statements: the transported unit lifts to a module morphism, and the transported counit lifts
to a module morphism. Added proof-only imports of their modules. The existing signature and
public imports are unchanged. Updated the criterion node to follow this Lean proof.

The forward witness is k_G followed by RM.map h. The reverse witness is LM.map k followed by
h_F. The underlying-map equations follow from adjunction naturality, naturality of e, and
symm_apply_apply for the abelian hom equivalence. All three modules compile locally.

## Proved and sorry left

The original module's sole sorry, AlgebraicGeometry.etaleInverseImageModuleLinearCriterion,
is replaced by a complete Lean proof from the following named remaining statements:

- AlgebraicGeometry.etaleInverseImageModuleUnitLinearLift
  (lem-weil-pbc-inverse-image-module-unit-linear-lift).
- AlgebraicGeometry.etaleInverseImageModuleCounitLinearLift
  (lem-weil-pbc-inverse-image-module-counit-linear-lift).

Each is in its own new module and has exactly `:= by sorry`, a source, and a full proof in
words. There are no other sorries added. The criterion still depends transitively on these
sorries; this is a reduction, not a claim of a sorry-free target.

## No longer needed

No imports or nodes are pruned. The algebraic-structure module and module pushforward module
are public imports required by the unchanged signature. The original node's algebraic
structure and sheaf-of-modules dependencies remain needed by the new unit/counit nodes;
the old direct proof dependencies
`lem-weil-pbc-etale-inverse-image-algebraic-structures` and
`def-weil-sheaf-of-modules-category` are replaced by the two lift nodes as direct
proof dependencies of the criterion, but remain transitive dependencies and are not pruned. The
adjunct-counit identity remains a direct dependency and is implemented by the Mathlib
adjunction hom equivalence inverse identity.

## Where the brief, the DAG or earlier work was wrong

The algebraic-structures dependency gives existence and compatibility of algebraic lifts,
not the linearity of the module unit or counit. Those two calculations were still hidden in
the criterion node's first two proof steps. They are now separate named statements, rather
than being mistaken for consequences already stated by the imported theorem.

The source file literature/stacks-project/sites-modules.tex is absent on this machine.
Read the primary source at https://stacks.math.columbia.edu/tag/03D3 instead. It supplies the
unit calculation and explicitly omits the counit direction; the counit calculation is the
agent-written projection and triangle-identity argument already in the parent node.

Searches: LeanFinder returned unitHomEquiv (sections), chosen module pullback adjunctions,
and pushforwardPushforwardAdj unit/counit formulas, none matching arbitrary LM with the
given scalar-action comparison. Loogle confirmed homEquiv_naturality_right. LeanSearch
returned Internal Server Error and is recorded as unavailable. Grep and local rg found
only topological/Zariski analogues and this criterion and its parent. Blueprint searches
for unit linear, counit linear, and adjoint-push-pull-modules returned no matching node.

Edge cases checked mathematically: zero modules give zero unit/counit lifts; for the identity
site map the formulas are the comparisons conjugating identity maps. No faithfulness,
flatness, nonzero-ring, or extra module-action hypothesis was added. In general both lifts
are valid by the stated naturality/product-projection calculations. Neither new statement
asserts the full linearity criterion or an adjunction. The unit route sk-def-exchange is
unchanged (its realized statement nodes are not bypassed).

## New nodes

lem-weil-pbc-inverse-image-module-unit-linear-lift: isolates step 2, existence of a module
lift of the abelian adjunct of e_G.inv. Module EtaleInverseImageModuleUnitLinearLift.

lem-weil-pbc-inverse-image-module-counit-linear-lift: isolates step 3, existence of a module
lift of e_(RM F) followed by the abelian counit. Module EtaleInverseImageModuleCounitLinearLift.

No change records are needed: no existing statement, definition, or public import changed.


## Second reading by A2

1. PASS: diffed all three delivered modules against the repository. Only the criterion
   already exists; its declaration signature is byte for byte unchanged after restoring
   the original single space before `:=`. No existing definition, docstring, or public
   import changed. The two additional imports are proof-only. No change record is needed.
2. PASS: all three files compile locally in import order with lcompile.py. Separate scratch
   copies with `#print axioms` show exactly propext, Classical.choice, Quot.sound, and
   sorryAx for each declaration. The criterion has no sorry; the only two sorries are the
   reported named unit and counit lift theorems. No forbidden code or hollow definition.
   The scratch copies were removed before delivery. This remains a reduction with two
   open dependencies, not a sorry-free result.
3. PASS: both lifts are strictly partial steps, not renamed copies of the criterion.
   Checked the unit's scalar equation using unit naturality and both product projections;
   checked the counit's scalar equation using counit naturality, the restricted action on
   RM(F), and the left triangle identity on the scalar projection. These arguments work
   for arbitrary displayed comparisons satisfying the stated compatibility equations.
   Zero modules, zero rings, empty schemes, and the identity site map create no exception;
   the zero and identity cases reduce to the corresponding zero maps and conjugated
   units/counits. Each new theorem has a complete proof docstring and matching node.
   Independently searched LeanFinder for lifting adjunction unit/counit to module sheaves,
   Loogle for homEquiv_unit, and grep for homEquiv/linear/smul and toSheaf/unit/counit.
   Also searched lean/Sheaf and lean/WeilConjectures for scalar-unit/counit and transported
   action. Results give sheafification or chosen pullback adjunctions, not these arbitrary
   transported lifts. Existing module construction and algebraic-structure theorems do
   not assert either lift. Read https://stacks.math.columbia.edu/tag/03D3: its unit argument
   agrees, and it explicitly omits the converse supplied by the counit calculation.
   Neither open lift can be closed by one of these search results in a few minutes.
4. PASS: read the proof from the criterion downward. The forward witness is kG followed
   by RM.map h; naturality and inverse-isomorphism cancellation establish its underlying
   adjunct. The reverse witness is LM.map k followed by hF; naturality of e and
   symm_apply_apply establish its underlying alpha. No shorter existing theorem found.
   Both public imports supply names in the signatures; both new proof imports are used.
   No module is pruned. The two old direct dependencies replaced by lift nodes remain
   transitive dependencies, now explicitly named under No longer needed. Checked
   dag/units/sk-def-exchange.json: its realized statement nodes and route are untouched.
5. PASS: the criterion node's proof and proof_deps follow precisely the two witnesses and
   adjunct-counit inverse identity. The two new nodes have the required source, searches,
   creation, blueprint, chapter, unit, and Lean records; their lean.statement fields match
   their declarations verbatim. The criterion's pre-existing normalized statement agrees
   with the unchanged signature. Corrected the unit node's copied proof_origin place,
   which unnecessarily referred to the counit converse, to cite the unit calculation.

Changes made on second reading: restored signature-boundary whitespace, clarified the
retained transitive dependencies in No longer needed, and corrected the unit node's
proof_origin citation. No mathematical proof or statement changed.
