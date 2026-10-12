## What changed
Split the pointwise truncation limit proof into existence and compatible-isomorphism
intermediate theorems, each in its own module, and proved the original theorem by
combining them. The two intermediate proofs remain `sorry` for parallel workers.

## Proved and sorry left
`pointwise_truncation_limit` is proved by applying the two strict intermediate parts.
Sorries left: `pointwise_truncation_limit_exists` (node
`lem-pc-ringed-space-pointwise-truncation-limit-exists`) and
`pointwise_truncation_limit_isIso` (node
`lem-pc-ringed-space-pointwise-truncation-limit-isIso`).

## No longer needed
None; all original proof-dependency imports remain available to the split statements.

## Where the brief, the DAG or earlier work was wrong
The full Roos and stalkwise argument was too large to close in this worker window;
strict existence and isomorphism components were stated separately as requested.

## New nodes
`lem-pc-ringed-space-pointwise-truncation-limit-exists` and
`lem-pc-ringed-space-pointwise-truncation-limit-isIso` are the two strict decomposition
nodes described above.

## Second reading by X2

1. I compared the delivered main module with the repository version. The target theorem
   signature and all existing declarations are byte-for-byte unchanged; only its proof and
   proof-only imports changed. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. They compile without
   errors or `sorry` outside the two explicitly split theorems. No definitions contain
   `sorry`, and the split declarations are ordinary theorems. Verdict: pass.
3. The two split statements have the same hypotheses and conclusions as the corresponding
   strict existence and isomorphism components of the original target. Their docstrings
   now describe the Roos-triangle, stabilization, stalk, and cohomology arguments in full,
   and each has a matching DAG node. Verdict: pass.
4. The main proof applies exactly the two strict components, while the unit route remains
   represented by the original target node and its proof dependencies. The split modules
   retain only statement imports as public imports; proof dependencies are private imports.
   Verdict: pass.
5. DAG node metadata, declarations, modules, and proof dependencies agree with the Lean
   files; no existing node or target statement was changed. Verdict: pass.

I changed the split theorem docstrings to give complete natural-language proofs and removed
four redundant proof-only imports from the main module. No declarations were otherwise
changed, and no additional holes were introduced.
