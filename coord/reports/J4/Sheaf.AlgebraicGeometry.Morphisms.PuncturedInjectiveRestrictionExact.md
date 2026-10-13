## What changed

The existing declaration `AlgebraicGeometry.Scheme.injective_punctured_restriction_exact`
keeps its signature byte for byte. Its kernel clause now uses the fully proved
`injective_punctured_restriction_kernel`, valid for every module. Its surjectivity
clause uses the general `injective_tilde_isFlasque`, then lifts sections through
the top restriction and `tilde.isoTop`; `tilde.toOpen_res` verifies the resulting lift.
Both helper imports are private. The three original public imports are needed by
the existing signature and remain. No definition or existing statement changes.

The second reader replaced the original two-clause sorry decomposition: proved the
kernel using the annihilator radical, and replaced the puncture-surjectivity hole
with the sourced general flasqueness theorem, in `InjectiveModuleTildeFlasque.lean`.

## Proved and sorry left

Hole closed in the existing item:
`AlgebraicGeometry.Scheme.injective_punctured_restriction_exact`.
New theorem completely proved:
`AlgebraicGeometry.Scheme.injective_punctured_restriction_kernel`
(node `new-punctured-kernel`).
One hole added:
`AlgebraicGeometry.Scheme.injective_tilde_isFlasque`
(node `lem-sbc-injective-module-tilde-flasque`).

No sorry remains in the item module or kernel module. The flasqueness theorem
is exactly `:= by sorry`, with a full sourced proof in its docstring.
This is a partial proof and reduction, not an axiom-free proof of the item:
one existing hole closed, one added, net zero holes in the import closure.
Relative to the first worker, the kernel hole is closed and the other hole
replaced by the general flasqueness input. The original
`injective_punctured_restriction_surjective` and its module/node are not delivered.

`#print axioms` in a temporary copy reports only `propext`, `Classical.choice`,
`Quot.sound` for the kernel. The item and flasqueness theorem additionally use
`sorryAx`, solely through the named flasqueness hole.

## No longer needed

No original Lean import or library module is pruned.
The item's old proof dependencies `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-scheme-conventions`, and `def-sbc-ideal-power-torsion-functor`
are replaced as direct proof dependencies by `new-punctured-kernel` and
`lem-sbc-injective-module-tilde-flasque`. Those definitions remain statement
dependencies and dependencies of the new helper nodes; they are not globally pruned.
The first worker's new `PuncturedInjectiveRestrictionSurjective` module and
`new-punctured-surjective` node are removed from this delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's report called conjunction assembly a proof without recording
the net increase from one to two holes. The target node still described the old
proof, neither helper had a complete sourced docstring proof, and search entries
claimed no matches without recording actual results. These are repaired.

The kernel has a shorter formal route than a finite principal-open covering:
use the radical of the annihilator and
`Ideal.exists_pow_le_of_le_radical_of_fg`. This closes the first worker's kernel hole.
The upstream `Scheme.Modules.isFlasque_of_injective` requires injectivity among
all sheaves of modules, while the affine equivalence gives injectivity in QCoh;
it cannot be applied directly to this M. Stacks Tag 09T2 is the applicable input.

Independent searches used leanfinder for annihilator/support and associated-injective
flasqueness, loogle for `Ideal.primaryComponent`, `TopCat.Presheaf.IsFlasque`, and
surjectivity of `tilde.toOpen`, and grep in Mathlib, lean/Sheaf, upstream
lean/WeilConjectures, and the chapter DAG. No duplicate of either helper was found.
LeanSearch was attempted and returned Internal Server Error, recorded as unavailable.
The search results and candidate rejection reasons are in both new nodes.

## New nodes

`new-punctured-kernel`: arbitrary-module kernel computation, now fully proved.
Its proof uses evaluation at prime localizations, the annihilator radical,
Noetherian finite generation and Mathlib's ideal-power containment lemma.

`lem-sbc-injective-module-tilde-flasque`: the general flasqueness input for an
injective module over a Noetherian ring, with no local-ring or puncture assumptions.
This is Stacks Tag 09T2 transported through the affine equivalence. Its complete
natural-language proof and sole remaining sorry are in
`lean/Sheaf/AlgebraicGeometry/Morphisms/InjectiveModuleTildeFlasque.lean`.
No change record is required: no existing signature, visibility or definition changed.

## Second reading by J4

1. Compared all delivered files against the repository. Only the target exists
   there; its declaration signature and original docstring are byte for byte
   unchanged. Added proof-only imports and a local elaboration option do not
   change its public interface. The two other modules are new. No definitions,
   target statements, hypotheses or conclusions were changed.
2. Compiled all three files together in import order using lcompile.py, without
   errors or warnings. Inspected all theorem bodies and checked #print axioms:
   the kernel is free of sorryAx; the target depends on the one named flasqueness
   sorry. No forbidden declarations, hollow definitions or arbitrary witness
   choices occur. The proofs choose only witnesses from proved existence results.
3. Read Stacks Tags 09T2 and 0A6T and the relevant Mathlib sources. The kernel
   needs no injectivity: zero values at primes force m into radical Ann(Rx),
   then finite generation gives a power annihilating x. Conversely a scalar
   in m outside each puncture prime kills x after taking its nth power.
   For a field m=0 and W is empty, so the kernel is all M and restriction is
   surjective onto zero. For an Artinian local ring m is nilpotent and W empty,
   with the same conclusions. For the zero module both clauses hold. Exponent
   zero in primaryComponent only adds the zero element. A DVR puncture recovers
   localization and ordinary power torsion. The remaining general flasqueness
   input is exactly the consequence of 09T2 for injectives in QCoh, including
   the empty open. Searches above found no usable replacement. Both new
   docstrings now contain complete proofs and source places.
4. Pruning checked from the top: the target uses the proved kernel and constructs
   surjective lifts from flasqueness using Mathlib APIs. Proof-only helper imports
   are private. The new kernel's Finiteness.Ideal import is private and used.
   The helpers' public imports occur in their signatures. The three removed
   direct proof dependencies are all listed above; no library module is pruned.
   The unit sk-prop-input-spreading has empty realized slots, and this lower-level
   restriction computation is not a unit step. The original flasque/localization
   route is kept, with no change to the unit or chapter.
5. Compared each node with its Lean declaration. The target node now records
   the two helpers and the actual lifting argument. The kernel node records
   the annihilator/radical proof; the flasqueness node records the sourced
   QCoh argument and exact signature. Every proof_deps list is the union of
   its proof-step uses. New nodes carry statement dependencies, sources,
   searches, ancestry, chapter/unit, creator and verbatim lean records.

Changes from this reading: closed the kernel hole, replaced the surjectivity
restatement with general flasqueness and a real restriction-lift proof, rewrote
new docstrings and node proofs, recorded actual independent searches, corrected
hole accounting and pruning, and updated the target DAG to match Lean.
