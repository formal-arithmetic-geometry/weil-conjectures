## What changed

Implemented the remaining generatorReductionCoherence proof as a case assembly of
its declared structural-square and open-square theorems. Existing statements,
definitions and public imports of the item are unchanged. Added a proved private
short_word_formulas induction: tensor/pullback use the quotient augmentation
transpose, proper image is its counit, and the open inverse laws use the existing
short-word integral domain and open reconstruction effectivity. This proves both
endpoint primitiveFormulas through length three.

The structural-square theorem supplies a universal family of short structural
squares. A new structuralReductionWordSubstitution theorem isolates its extension
to arbitrary admissible substituted words. That extension is needed specifically
because openInterchangeReductionSquares requires StructuralSquares without a
length bound for its internal clopen-factorization systems. The parent splits the
nine structural cases from the four open cases, uses the short family directly
in the former and the stated open theorem in the latter, and retains their
forward Assertion conjuncts. This is a decomposition, not a claim that all
remaining theory is proved.

Forced import-only adaptations in TensorAdjunctionReductionSquares and
OpenInterchangeReductionSquares redirect their parent import to the already
published GeneratorReductionData. No declaration or theorem proof in either
held module changes. Change record:
coord/changes/K4-generator-reduction-import-cycle.md.

LeanSearch, LeanFinder, Loogle and the launcher Mathlib grep were run; generic
adjunction naturality and monoidal coherence do not state the fixed coefficient
comparison. The full imported blueprint search for structural coefficient found
no duplicate. The new lemma keeps the unit's tensor/adjunction/mate route.

Validation: lcompile.py compiled both adapted dependencies and the new substitution
module, in 55.1, 48.1 and 41.0 seconds respectively. The parent then compiled cleanly
in 24.3 seconds against those sandbox outputs. Its first full compile failed in a
simp_all case split; replacing that with explicit constructor reasoning removed
the unnecessary geometric-context simplification. The private primitive induction
had already compiled independently in 11.4 seconds. No time limit was increased.

## Proved and sorry left

Closed the one textual hole in the assigned item:
WeilConjectures.GeneratorReduction.generatorReductionCoherence
(node lem-sf-generator-reduction-coherence). Its proof is a complete Lean assembly from the named dependencies; it is not
asserted axiom-free.

Added one named hole:
WeilConjectures.OpenInterchangeReduction.structuralReductionWordSubstitution
(node lem-sf-structural-reduction-word-substitution), in its own module, exactly
`:= by sorry`. It states only structural-word substitution given all short
structural squares; it asserts none of the four open-generator squares and none
of the parent's primitive-formula conclusions.

Unchanged holes in the two import-only adaptations:
WeilConjectures.GeneratorReduction.tensorAdjunctionReductionSquares
(node lem-sf-tensor-adjunction-reduction-squares), and
WeilConjectures.OpenInterchangeReduction.openInterchangeReductionSquares
(node lem-sf-open-interchange-reduction-squares).

All other existing item declarations remain proved, including
primitiveReductionTranspose and completionMap_isIso. The new private
short_word_formulas is completely proved. Item holes: 1 to 0. Packet holes:
3 old (the item and two adapted siblings), 3 new (the two siblings and the new
substitution theorem); one upper hole closed and one lower hole added, net zero.
The new proof imports also expose the existing dependency holes; the project
ledger, rather than this packet count, determines target-closure progress.

## No longer needed

No mathematical dependency module is withdrawn or claimed pruned. Both declared
generator-square nodes are used. No source-library declaration is removed.
The two lower modules no longer need their public import of
Sheaf.SixFunctors.GeneratorReductionStatement: GeneratorReductionData supplies
all referenced definitions, and neither lower theorem uses the parent theorem.

The parent's old direct proof dependency on lem-sf-primitive-reduction-transpose
is replaced by an explicit induction using lem-sf-primitive-quotient-augmentations,
lem-sf-short-word-integral-domain and lem-sf-open-reconstruction-effectivity.
The published primitiveReductionTranspose remains unchanged and proved. The old
explicit setup edges to lem-coef-derived-system-evaluation-calculus and
lem-coef-semilinear-derived-sections are no longer direct proof steps: their
actual adjunction and section constructions remain used through the data and
square dependencies. No claim is made that either node is globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The planned application of the open-square lemma requires structural squares on
all admissible words, including its internal length-four terms. The structural
lemma only provides endpoints of length at most three. The new substitution
lemma makes exactly this previously unstated extension a separate task.

The two lower modules still import the parent theorem module after the T7 data
extraction. They cannot serve as parent proof dependencies until those imports
are redirected. No statement is disputed, weakened or replaced, and there is no
change to the unit or chapter route.

## New nodes

lem-sf-structural-reduction-word-substitution records the extension from universally
quantified short structural squares to arbitrary admissible substitutions. Its
statement, complete source-based proof in words, independent dependency list,
actual three-kind Mathlib searches and Lean attachment accompany the new module.
Edge cases checked: empty input families, scalar units, repeated variables,
identity maps, empty opens and zero inputs. Substitution introduces at most three
independent variables and can use ULift to preserve the input universe. Its proof
must use the actual recursive coefficient and completion maps; equality of finite
evaluations is not assumed. The parent node now records the actual five-step Lean
assembly and the substitution dependency. Import repair record:
coord/changes/K4-generator-reduction-import-cycle.md.

## Forced adaptations

TensorAdjunctionReductionSquares is held by C2 and
OpenInterchangeReductionSquares by E3. Against the parent with its new proof
imports, their original files fail lcompile import ordering with:
`the modules import one another in a cycle` followed by the parent, both lower
modules and StructuralReductionWordSubstitution. The diagnostic was reproduced
in scratchpad/original-cycle. The only changed line in each is its public import
of the parent: line 8 in TensorAdjunctionReductionSquares and line 23 in
OpenInterchangeReductionSquares now import GeneratorReductionData. This is forced
by the new parent proof dependencies; all existing signatures and visibility are
identical. There are zero existing direct or transitive source importers of the
two lower modules, according to tools/downstream.py. The adapted modules and parent
are compiled together in normal import order.

## Forced adaptations

### Sheaf.SixFunctors.OpenInterchangeReductionSquares
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

### Sheaf.SixFunctors.TensorAdjunctionReductionSquares
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
