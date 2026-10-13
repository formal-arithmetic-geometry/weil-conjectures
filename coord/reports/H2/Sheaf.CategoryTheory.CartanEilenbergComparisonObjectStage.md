## What changed

Replaced the proof of `CategoryTheory.exists_cartanEilenberg_comparison_object_stage`
with a compiling horseshoe argument. Its signature and existing docstring are unchanged.
The private helper `cycleObjectRow_shortExact` proves short exactness of the explicit
kernel/object/image row using Mathlib's kernel and image APIs. Mapping and evaluating
that row supplies the exactness inputs, proved in this delivery.

Added `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage.Rows`. Its real row
constructor and augmented-row structure contain no postponed data. Its theorem presents
canonical single-complex augmentations and their degree-zero transport identities. It
constructs no comparison morphism and has no injectivity or prescribed-cycle-map hypotheses.
The main proof builds the three target injective resolutions from their actual columns,
lifts the outgoing endpoint with the source library's `descOfQuasiIso`, proves the cycle
augmentation square by monomorphic cancellation, applies the existing exact-source
horseshoe theorem, then transports its middle augmentation equation back to the original.

Read Stacks [015I](https://stacks.math.columbia.edu/tag/015I),
[015K](https://stacks.math.columbia.edu/tag/015K), and
[013P](https://stacks.math.columbia.edu/tag/013P). The local literature source named by the
old node is absent on this machine; the official online text supplies those same tags.
Updated the item's proof route in its DAG copy. All writes are in the sandbox.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.exists_cartanEilenberg_comparison_object_stage`
(node `lem-weil-pbc-ce-comparison-object-stage`). Added one remaining hole:
`CategoryTheory.exists_cartanEilenberg_comparison_augmented_rows`
(node `lem-weil-pbc-ce-comparison-augmented-rows`). This is a decomposition, not a
sorry-free proof of the target's dependency closure: one hole closed, one hole added.
The existing `CategoryTheory.InjectiveResolution.exists_horseshoe_morphism_lift_exact_source`
remains an imported proof obligation; this delivery does not change it.

Both delivered modules compile. The private exactness helper and the row constructor
are fully proved; the new row-presentation theorem has exactly `:= by sorry`.
No `sorry` remains in the item's module, and no definition contains `sorry`.

## No longer needed

Removed the proof-only import `Mathlib.Algebra.Homology.ModelCategory.Injective`.
The concrete nonnegative-degree augmentation lift from
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution` replaces that API.
The existing lifting node remains a conceptual proof dependency, realized by this
source-library specialization. No existing DAG node or Sheaf module is bypassed;
the exact-source horseshoe dependency and the unit's route are retained.

Discarded the earlier sandbox-only modules `Augmentation` and `CycleCompatibility`
and their two unlanded nodes. Neither is a dependency of this proof.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt claimed that every object-column map agreeing on the augmentation
agrees with a specified cycle-column map in all degrees. That is false. For example,
in vector spaces take an acyclic column with the identity differential in resolution
degrees 1 to 2 and zero degree 0; take a zero horizontal differential, so its entire
column is cycles. Take K=L=0 and zero augmentations, which are quasi-isomorphisms;
the object map zero and the cycle map identity agree on the zero augmentation but do
not give the same cycle square in degree 1. All vector-space terms are injective.
Thus the previous cycle-compatibility theorem was unusable and is removed, not weakened.
Its node was never in the repository. The earlier new modules also lacked full source
proofs and complete DAG records. No existing project statement is changed.

The original DAG route itself remains valid. The hard residual glue is the canonical
single-complex kernel/image identifications and augmentation transport, now isolated
from both the outgoing lift and the middle comparison construction. Its zero-object,
zero-differential and identity-functor cases were checked against that construction;
none requires injectivity or restrictions on the base map u.

## New nodes

`lem-weil-pbc-ce-comparison-augmented-rows` records the new row-presentation theorem
in `Sheaf.CategoryTheory.CartanEilenbergComparisonObjectStage.Rows`. It covers the
single-complex transport portion of the original Steps 1 and 2, with a complete
construction in words, real Lean statement and logged LeanSearch/Loogle/grep searches.
It is strictly a part of the argument: it has no comparison-map conclusion, and
neither y nor any target-column injectivity is among its inputs. No change record or
forced adaptation is needed; every existing public signature is preserved.


## Second reading by H2

1. Compared both delivered modules against the repository (Rows is new), and the
   existing node JSON against its original. The existing theorem signature and
   docstring are byte-for-byte unchanged. No existing definition or target changed;
   the existing node changes only its proof route, dependencies and origin. PASS.
2. Compiled both modules in import order with lcompile.py. In a scratch copy, printed
   axioms of the main theorem, the residual row theorem, the row constructor, and the
   private exactness helper. The first two use only propext, Classical.choice,
   Quot.sound and sorryAx; the constructor and helper use only the three permitted
   axioms. The only delivered sorry is the named row theorem, exactly `by sorry`.
   No forbidden declaration forms or postponed definition data occur. The main proof
   eliminates the row existence locally; it does not define an arbitrary chosen
   witness from it. PASS, conditional on the explicitly reported open dependencies.
3. Read the residual theorem, its complete docstring proof and its node. The base
   rows can be constructed as F of the kernel/object/image row of K and the row of L;
   their augmentations come from the canonical exact-single-functor kernel/image
   isomorphisms. The four equations express only degree-zero naturality and
   augmentation transport. For a zero complex all rows and equations are zero; with
   zero horizontal differentials the image endpoint is zero and the cycle inclusion
   is an isomorphism; with F the identity the source transport reduces to the standard
   single-complex identifications. None of these cases needs injectivity or a
   prescribed cycle map. This is a true, strictly smaller part of the argument, not
   the original comparison assertion under another name. Independently searched
   leanfinder for natural single-complex/kernel/image augmentation transport, loogle
   for the cycle-preservation API, and grep for singleMapHomologicalComplex,
   mapCyclesIso and image preservation; also searched the project Lean sources.
   Found component isomorphism APIs, but no existing theorem giving this augmented
   row presentation with its four equations. Closing it requires substantial
   canonical transport formalization, rather than a few-minute proof. PASS.
4. Read the proof from its conclusion backward: the two required equations follow
   from the existing exact-source horseshoe theorem and the four transport equations;
   the outgoing endpoint lift uses the proved source-library descOfQuasiIso API.
   The monomorphic cancellation proving the prescribed cycle endpoint square is
   valid. The kernel/image exactness helper proves the degreewise inputs directly.
   No shorter complete route emerged in the searches. Checked sk-prop-h2.json:
   its realized statement and sole step are empty, so no realized unit node is
   bypassed. Both original proof-dependency nodes are retained, the lifting node
   being implemented by the source-library specialization; the removed model-
   category import is already recorded above. PASS.
5. Checked the new node's statement verbatim against Lean, its source, proof steps,
   empty elementary proof-dependency union, creation/blueprint/Lean fields and search
   record. Checked the original node's six steps against the compiled proof and its
   dependency union. PASS.

Second-reading changes: replaced the new Rows module's unnecessarily broad public
`Mathlib.CategoryTheory.Preadditive.Injective.Resolution` import with the public
`Mathlib.Algebra.Homology.QuasiIso` import its statements actually require. The
existing module retains its original public resolution import, which also supplies
symbols used in its signature. Both files compile after this import cleanup. Added
this independent review; no mathematical statement, proof or definition changed.
