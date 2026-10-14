## What changed

Copied the already-proved `cartier_equality` theorem into the F2 sandbox and added
one explanatory comment at the final finite-dimensional specialization. The proof
compiles and introduces no new declarations or imports.

## Proved and sorry left

`cartier_equality` has a complete proof (one theorem of one); F2 closed zero holes. There are no `sorry`s left and
no `sorry` declarations were added. The repository baseline already contained this
complete proof, so this delivery closes no additional hole.

## No longer needed

No imports, nodes, or modules were removed. The proof uses the complete-intersection
model, fraction-field cotangent model, and finite transcendence-basis dependencies
recorded by `lem-weil-pbc-cartier-equality`.

## Where the brief, the DAG or earlier work was wrong

The item remains listed in `coord/repairs.txt` for upstream review #1428, but the
qualified field-generation hypothesis has already been repaired. The brief
describes this module as containing `sorry`, but the current repository
already contains a compiling proof (landed previously). The DAG proof plan agrees
with the implementation; no statement or definition was changed.

## New nodes

None.

## Second reading by F2

1. Interface: `diff -u` against the repository shows only one added explanatory
   comment before `exact_mod_cast heq.symm`. The full `cartier_equality` signature,
   declaration visibility, imports, and definitions are byte-for-byte unchanged.
   In particular `IntermediateField.FG` remains the hypothesis, not algebra finite
   type, and the untruncated equality is still in `Cardinal`. Pass.
2. Proof: compiled the delivered file with `lcompile.py` (exit 0, no warnings).
   A scratch copy with `#print axioms cartier_equality` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No sorry, axiom, unsafe,
   opaque, implemented_by, extern, or data definition is added. Pass.
3. Split statements: none. There are zero new declarations and zero new nodes;
   no restatement or arbitrary witness is introduced into a definition. The
   existential model and linear map are eliminated only inside a theorem proof.
   Pass; small-case testing of new statements is inapplicable.
4. Route and pruning: read both model theorem signatures and the full cotangent
   model proof. The first supplies c <= n, n-c = s.card, length f = c,
   regularity, the domain instance, and the fraction-field equivalence. The second
   supplies the kernel and cokernel equivalences used by the proof. Rank-nullity
   and the quotient dimension formula give the claimed natural-number equality;
   the basis-cardinality theorem casts it to Cardinal. In the finite case zero
   transcendence degree gives the equality with its orientation reversed at the
   final cast. This also covers an empty transcendence basis; no separability or
   characteristic assumption was added. The Loogle search `Algebra.H1Cotangent`
   found finiteness for finitely presented algebras and vanishing for formally
   smooth algebras, neither a shortcut for arbitrary finitely generated field
   extensions. Repository searches found no alternate Cartier formula. All public
   imports provide notions in the signature (differentials, H1Cotangent, trdeg,
   finrank, FG); the private imports supply the basis, dimension lemmas, and two
   models. No dependency module was removed. Read `dag/units/sk-thm-p1.json`:
   its realized route is untouched. Pass.
5. DAG: read `lem-weil-pbc-cartier-equality.json`; its three proof steps match
   finite basis/model selection, cotangent kernel/cokernel comparison, and the
   dimension calculation. All six old proof dependencies are retained and used
   through these steps; the document origin still describes Tag 07E1's route.
   No DAG field needs changing for an explanatory comment. Pass.

Second reading changed the report to distinguish the existing complete proof
from F2's zero newly closed holes. The delivered Lean change remains solely the
first worker's explanatory comment. This delivery records review of an already
repaired queued item; it is not new proof progress or a decomposition.
