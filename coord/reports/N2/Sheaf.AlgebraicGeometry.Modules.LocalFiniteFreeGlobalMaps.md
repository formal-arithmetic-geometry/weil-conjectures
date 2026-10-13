## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_free_map_isIso_near_of_isFiniteLocallyFree`
without changing its signature or existing docstring. The proof obtains a finite local
trivialization from the existing `FiniteDescent` theorem, applies a denominator-clearing
morphism-extension theorem, deduces invertibility from its restriction identity, and
reindexes by `ULift (Fin (Fintype.card I))`.

Added `Sheaf.AlgebraicGeometry.Modules.ExtendLocalFreeMap`, with the named open theorem
`AlgebraicGeometry.Scheme.Modules.exists_global_map_of_local_free_map`. Its input is an
arbitrary local morphism into a quasi-coherent module, and its output is a global morphism
and an explicit restriction identity after an automorphism of the source. It does not
assume a local trivialization of the target or conclude that any map is an isomorphism.
Thus it isolates extension of sections, rather than restating the item's conclusion.
The new module imports `ClearDenominators` privately, keeping the original proof route.
The item imports `FiniteDescent` and the new module privately.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_free_map_isIso_near_of_isFiniteLocallyFree`
(node `new-sbc-quasi-affine-local-free-global-map`), the only original hole in the item.
No direct holes remain in the item's module.

Hole added: `AlgebraicGeometry.Scheme.Modules.exists_global_map_of_local_free_map`
(node `new-sbc-local-free-map-extension`), in the new module. Its complete construction
in words is in its docstring: principal-open shrinking, basis images, section clearing,
a common exponent, the free-sheaf universal property, and the scalar automorphism.

This is a decomposition: one hole closed, one hole added, net zero holes closed in the
import closure. The upper proof is conditional on the named extension theorem. Both
`#print axioms` checks return precisely `propext`, `Classical.choice`, `Quot.sound` and
`sorryAx`. The new extension construction was not completed in Lean; the existing
section-clearing theorem is already proved, but the restriction and free-sheaf assembly
still need formalization. No definition or data construction contains a hole.

## No longer needed

Removed the item's direct import of
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`; that module remains
privately imported by `ExtendLocalFreeMap`, which needs its theorem for the planned
extension proof. Removed `lem-pc-section-clearing-denominators` from the item's direct
`proof_deps`, replacing it with `new-sbc-local-free-map-extension`. The former node
remains the new node's dependency. Hence no old dependency node or module is pruned
from the import closure. No other original proof dependencies existed.

Removed the first worker's unused public import of `FiniteDescent` from the new module;
the item now imports it privately for its local-trivialization proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's split theorem imposed no quasi-coherence on N, although its proposed
proof applied a theorem requiring quasi-coherence. It also asserted the same final
local-isomorphism property as the item, rather than spelling out what extension supplies.
The second reader replaced that undelivered theorem with arbitrary local morphism
extension, with the required quasi-coherence and an explicit restriction identity.
The target's finite-local-freeness instance supplies quasi-coherence, so its statement
has not changed.

The split node had no searches, its Lean signature was a placeholder, and the item node
still described the old proof rather than the worker's proof. These records are repaired.
Three `letI` style warnings were removed. Tag 0EKP itself invokes ample global generation;
the actual denominator-clearing input is Tag 01PW. The new theorem cites that precise
source, and the report distinguishes the specialization from the source's statement.

## New nodes

`new-sbc-local-free-map-extension`, stated in
`lean/Sheaf/AlgebraicGeometry/Modules/ExtendLocalFreeMap.lean`, is the extension-only
part of the argument. It is valid for quasi-coherent N with no global local-freeness
assumption and for noninvertible local maps. No existing declaration was changed in
signature, and no change record or forced adaptation is necessary.

Actual Mathlib searches were logged with `msearch.py`: LeanFinder for extension of
quasi-coherent sections and local finite free morphisms, Loogle for free sheaves and
restriction, and grep for extension and power-scalar existence lemmas. No exact match
was found; the hits concern affine tilde sections, functions, or local generators.
LeanSearch returned Internal Server Error, recorded as unavailable. Repository searches
of `lean/Sheaf/AlgebraicGeometry/Modules`, `FiniteDescent`, `ClearDenominators` and `Ample`
found the existing local-trivialization and section-clearing results, but no theorem
with the required global-extension identity. The blueprint search for denominators
found `lem-pc-section-clearing-denominators`, which is reused, not duplicated.

## Second reading by N2

1. Compared the delivered item with the repository using `diff`, and separately checked
   the entire existing theorem signature as literal bytes. Verdict: unchanged, including
   R, Noetherianity, V, N, finite local freeness, x, the neighbourhood assertion, the
   natural-number rank, the `ULift` universe, and restricted `IsIso`. The additional
   theorem belongs to a new, undelivered module, so its repair changes no existing API.

2. Compiled both modules in import order using the required `lcompile.py --all`; both
   compile with no errors or warnings. Searched the delivered text for forbidden
   declarations and direct holes. The item has zero holes; the sole hole is the named
   extension theorem with its full docstring proof. Scratch `#print axioms` checks of
   both public theorems show only the three allowed axioms and `sorryAx`. The target
   proof uses only local proof witnesses; it adds no definition chosen from existence.
   Verdict: kernel-checked reduction with one explicitly reported remaining hole.

3. Read Stacks Tags [01PW](https://stacks.math.columbia.edu/tag/01PW) and
   [0EKP](https://stacks.math.columbia.edu/tag/0EKP), and the full existing
   `exists_tensorPowSection_eq_restrict` signature and proof. Checked its hypotheses:
   V is quasi-compact because R is Noetherian, V embeds separatedly into affine Spec R,
   O_V is invertible, and N is now explicitly quasi-coherent. Shrinking to ambient D(f)
   makes f a global function on V that is invertible on W. Finite I permits one common
   exponent; its inverse defines the source automorphism. Tested empty I (unique map,
   identity automorphism), zero local morphism, arbitrary/noninvertible local morphisms,
   rank one, and empty V or the zero ring (no point x exists). The equality has the
   correct types: c identifies restriction to W with restriction to U followed by W.
   Verdict: true extension-only subproblem, strictly less of the target argument;
   searches above found no duplicate. The first worker's unchecked statement was
   replaced rather than accepted.

4. Read the proof from the target downward. `FiniteDescent` already proves local
   trivialization, so that step is reused. The new lemma supplies only extension and
   its identity; the item proves local invertibility by composition and finite
   reindexing using the free functor. Kept the denominator-clearing route of the
   original node. The public imports provide signature notions; both added imports
   in the item are private proof imports. The old direct denominator-clearing import
   was transferred to the split module. Checked `dag/units/sk-prop-input-spreading.json`:
   its `realized` statement and step lists are empty, and no realized node or unit
   route is removed or bypassed. Verdict: reduction and pruning accounting are accurate;
   no closure module is claimed pruned.

5. Checked both node files against Lean. The item's proof steps now describe local
   trivialization, the actual extension identity and isomorphism inference, and finite
   reindexing. Its direct dependency is the new extension node. The new node's sole
   non-elementary input is `lem-pc-section-clearing-denominators`, whose declaration
   gives exactly the lifted sections used in its docstring. `proof_deps` equals the
   union of step uses. The new node records its actual source, complete verbatim Lean
   signature, group/item/date, chapter/unit, logged searches, and blueprint provenance
   through the existing quasi-affine embedding chain to
   `sbc-thm-spreading-finite-etale-galois`. Verdict: records match the delivered reduction.

Changed during second reading: replaced the unsound/underspecified split with the
quasi-coherent arbitrary-morphism extension identity; adjusted the target proof to
infer `IsIso` from that identity; corrected import visibility and placement; removed
`letI` warnings; supplied the full docstring, searches, node proofs, signatures and
provenance; and corrected the report to count a decomposition with net zero closure
holes closed. No existing signature, definition, target, or unit record changed.
