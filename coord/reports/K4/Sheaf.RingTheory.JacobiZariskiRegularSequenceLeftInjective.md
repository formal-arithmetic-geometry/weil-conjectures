## What changed

Proved `Algebra.jacobiZariski_left_injective_of_regularSequence` with its signature unchanged.
The proof constructs the composed polynomial presentation, transports the given regular
sequence through the quotient by the coefficient kernel, applies the existing ideal
intersection theorem, restricts the injective conormal map to the differential kernel,
and compares with the canonical presentation. The ambient formula is checked using
Mathlib's explicit homotopy between maps of extensions.

Added the proved module `Sheaf.RingTheory.ComposedConormalInjectiveOfIntersection`.
It gives conormal injectivity from the ideal intersection identity, with arbitrary variable
sets, using only Mathlib. Its two proved private helpers identify the extended ideal under
flat base change and identify the quotient by the presentation kernel with a tensor product.
Both modules compile cleanly using lcompile.py, with no added sorries or warnings.
The helper publicly imports only Mathlib.RingTheory.Extension.Generators; tensor quotient
and flatness imports are private. The item privately imports Mathlib JacobiZariski for
the differential square used only in its proof.
The new theorem's printed axioms are exactly propext, Classical.choice, Quot.sound.
The original theorem still reaches the existing sorryAx through its unchanged ideal
intersection dependency; this delivery does not claim that dependency is closed.

## Proved and sorry left

Closed one original hole: `Algebra.jacobiZariski_left_injective_of_regularSequence`
(node `lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective`).
Added zero holes; zero sorries remain in either delivered module.
`Algebra.Generators.Cotangent.toComp_injective_of_intersection` is fully proved, not a
split-off sorry. This is one hole closed, not a decomposition.

## No longer needed

Removed the proof-only import `Sheaf.RingTheory.JacobiZariskiHomologySequence` and its
node `lem-weil-pbc-jacobi-zariski-homology-sequence` from this theorem's proof dependencies.
No six-term exactness, Tor comparison, snake lemma, or connecting-map formula is needed
for left injectivity: Mathlib provides the kernel restriction and presentation equivalence.
This removes that module and its proof closure from this item's route; other targets may
still need it. Also removed `def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-regular-sequence`, and
`def-weil-pbc-smooth-ring-map` from `proof_deps`: these are still unchanged statement
dependencies in `stmt_deps`, not additional proof lemmas. Their mathematical notions
remain in the statement and public imports; their modules are not claimed as pruned.
The other original proof dependency nodes remain used through their Mathlib interfaces
or the ideal-intersection theorem. No unit statement or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan is valid, but importing the full
Jacobi–Zariski sequence to name the leftmost map is unnecessary. Mathlib's
`Cotangent.map_sub_map` proves the required equality on the base-changed kernel directly.
The locally named literature tex files are absent in this read-only checkout; read the
primary Stacks pages https://stacks.math.columbia.edu/tag/07D4 and
https://stacks.math.columbia.edu/tag/07CX. LeanSearch returned HTTP 500 and is recorded
as unavailable, not as a failed mathematical match.

## New nodes

`lem-weil-pbc-composed-conormal-injective-of-intersection` records the proved conormal
injectivity implication in step 2 of the original plan. This is strictly an algebraic part
of the argument: its statement has arbitrary presentations and an ideal identity, with
no regular sequence, homology, canonical presentation, or existential kernel map.
The empty-variable case reduces to the same ideal quotient argument; zero ideals give
the zero source; zero rings give zero modules. No nontriviality assumption or finite
variable assumption is introduced. Searches of the existing DAG and blueprint for
conormal and Tag 07D4 found no duplicate of this implication. Existing tensor quotient,
flat tensor exactness, scalar cancellation and coefficient kernel nodes are cited.
No definition, existing statement, or public import was changed; no change record is needed.

## Second reading by K4

1. Interface: compared the whole existing module with its repository version using diff,
   then compared the text from the public theorem name to `:= by`: its signature is byte
   for byte unchanged. No definitions were changed or added, no existing declaration was
   removed, and no other existing module is delivered. The existing public imports remain
   unchanged. No change record is needed. Verdict: pass.
2. Proof: compiled both delivered modules in import order with lcompile.py, cleanly and
   without warnings, and compiled scratch copies with explicit `#print axioms` commands.
   `Algebra.Generators.Cotangent.toComp_injective_of_intersection` has precisely propext,
   Classical.choice, Quot.sound; `Algebra.jacobiZariski_left_injective_of_regularSequence`
   also has inherited sorryAx through the existing intersection dependency. Neither file
   contains sorry or forbidden declarations/options. The chosen polynomial lifts come
   from the proved surjectivity hypothesis, not from an unproved existence theorem.
   In the conormal proof, `hf` identifies the kernel with K times J, `k` is injective on
   the quotient, and `H` checks the map on tensor generators. In the item, the differential
   square establishes the restriction, `map_sub_map` establishes the requested canonical
   ambient equation on the kernel, and equivalence plus ambient injectivity proves the
   final injectivity. Verdict: pass, one original hole closed and zero holes added.
3. New statement: no statement is split off with sorry. The proved conormal helper is
   strictly the algebraic part of the original argument and has no regularity or homology
   assumption. Read Stacks 07D4 and 07CX at their primary web pages; the helper isolates
   the intersection/tensor argument of 07D4. Checked J <= K, the free polynomial extension,
   C = T/K, and the tensor cancellations in the Lean proof. For empty variable sets the
   polynomial equivalence still applies; for J = 0 the source is zero; for J = K the
   identity is tautological and the map is the expected conormal identification; for the
   zero ring the modules are zero. Arbitrary variable universes and infinite sets are
   allowed. Independently searched msearch leanfinder for ideal inclusions and conormal
   injectivity, msearch grep for conormal/intersection and cotangent injectivity, and rg
   in Mathlib, upstream WeilConjectures and lean/Sheaf. Hits give CotangentSpace injectivity
   (degree zero), flat base change, localization, or smoothness results, not this map under
   this intersection hypothesis. No duplicate or shorter existing theorem found. Verdict: pass.
4. Route and pruning: the proof starts at the item's hole and uses the existing intersection
   theorem, proved tensor/flatness API and presentation comparison. It does not rename the
   item into a new hole. Inspected dag/units/sk-thm-p1.json, including `realized`: neither
   this item nor the removed homology-sequence node realizes a unit statement or step;
   the chapter and unit route remains intact. The old proof_deps difference consists of
   the homology-sequence node and the three definition nodes now explicitly listed above.
   Existing statement dependencies stay. Narrowed the new helper's public import from
   Mathlib JacobiZariski to Extension.Generators, with proof-only imports for Flat.Basic
   and TensorProduct.Quotient; the item now privately imports Mathlib JacobiZariski for its
   differential-square proof. Recompiled the complete delivered set successfully. Verdict: pass.
5. DAG: the existing node changes only proof, proof_deps and proof_origin; its statement,
   stmt_deps and lean record are unchanged. Read the new node and matched its public Lean
   signature verbatim. Its three proof steps follow flat ideal base change, the ideal
   quotient injection, and scalar cancellation, with proof_deps equal to the union of uses.
   Its source, searches, creation, blueprint ancestry, chapter, unit and lean record are
   present. The item's four recorded steps match the construction, regularity transport,
   kernel restriction and homotopy comparison in its proof. Verdict: pass.

Second reading changed only import visibility/scope and completed the pruning report;
no mathematical proof body or statement was rewritten. Final local compilation and axiom
checks were clean within the qualifications above.
