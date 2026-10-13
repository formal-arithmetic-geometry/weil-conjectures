## What changed

Replaced the proof hole in `Sheaf.AlgebraicGeometry.AffineSheafificationTorAmplitude`
by a compiling reduction. Its signature and public imports are unchanged. The proof
unpacks the original global interval, specializes each test to the actual direct image
under `hU.isoSpec.inv ≫ U.ι`, transfers its degreewise vanishing, and applies the existing
`AlgebraicGeometry.affine_torAmplitude_iff`. It adds two proof-only imports:
`Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion` and
`Sheaf.AlgebraicGeometry.AffineSheafificationTensorVanishingTest`.

The new module states just the first two steps' remaining single-test transport.
It has no finite-Tor hypothesis or existential Tor-amplitude conclusion: it transfers
vanishing in one degree for one explicitly specified global test sheaf. The affine
Tor criterion and the quantifier/interval assembly are completed in the item's proof.
The DAG records this route. No existing interface or other module was changed.

## Proved and sorry left

Closed the direct proof hole of
`AlgebraicGeometry.Scheme.finiteTorAmplitude_of_affine_sheafification`
(node `lem-pc-affine-sheafification-tor-amplitude`). There is no `sorry` in the item.

Added one hole:
`AlgebraicGeometry.Scheme.affine_sheafification_tensor_vanishing_test`
(node `lem-pc-affine-sheafification-tensor-vanishing-test`). Its proof is exactly
`:= by sorry`, with its source and complete intended argument in the docstring.
This is a decomposition: one upper hole closed, one strictly smaller single-test
hole added, net zero holes. The item still depends transitively on this hole and
is not claimed axiom-free.

Both modules compile without warnings through `lcompile.py --all`.

## No longer needed

No original import or planned dependency is pruned. The original open-restriction
and localized-site-transport nodes remain needed below the new single-test node;
the affine Tor criterion remains a direct dependency. The abandoned sandbox-only
`AffineSheafificationTorAmplitudeAux` module and its existential bounds theorem
were removed, replaced by the narrower single-test statement. That earlier module
had never been delivered and had no repository node.

## Where the brief, the DAG or earlier work was wrong

The prior worker's derived-category-instance objection was avoidable:
`HasDerivedCategory.standard` supplies the spectrum sheaf localization at universe
`u + 1`, independently of the global universe `w` and ring-module universe `wR`.
Trying to assign that standard instance universe `w` produced a genuine type mismatch;
using its actual standard universe compiles. No target or intermediate signature
was weakened to do this.

The existing first two proof dependencies give derived tensor restriction and
an affine derived equivalence, respectively. Neither signature states the complete
single-test direct-image vanishing implication with the representing isomorphism.
That remaining glue is isolated in the new node rather than left inside the item.

Edge cases checked mathematically: empty affine opens and zero rings have zero
module sheaves, so the open counit and zero-cohomology transfer still apply; the
zero complex and zero test sheaf give zero tensors; arbitrary degrees and unbounded
representatives use K-flat restriction and unbounded total tensor, with no truncation.
The unit's `realized` fields do not designate this node as a unit statement or step;
its original locality, transport and criterion route is retained.

## New nodes

`lem-pc-affine-sheafification-tensor-vanishing-test`, in
`lean/Sheaf/AlgebraicGeometry/AffineSheafificationTensorVanishingTest.lean`, isolates
one-degree tensor vanishing for the actual direct-image test sheaf. It retains the
original locality and affine transport tools, has independent localization universes,
and needs no module-derived localization, Tor bounds or pseudo-coherence. Its source
is the locality calculation of Stacks Tag 08DX and the original Tag 08CG test argument.
Searches used LeanSearch (unavailable), LeanFinder, Loogle, and Mathlib/repository grep.
No change record is needed: all existing signatures and public imports are unchanged.

## Second reading by R1

1. Compared the delivered Tor-amplitude module with the repository version. The theorem
   signature is byte-for-byte unchanged; the added imports are proof-only. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors, unsafe
   declarations, or unintended `sorry`s; the single-test theorem is the named split-off
   hole. Verdict: pass.
3. Read the split-off statement and node against the existing declarations. It is a true
   one-test vanishing implication, strictly weaker than the target and needed by the
   reduction; its docstring, source, proof plan, and Lean signature agree. Verdict: pass.
4. Checked the proof route and imports. The proof uses the affine criterion and the
   single-test transport, while retaining the unit's locality, transport, and criterion
   route. No unused original import or proof dependency was found. Verdict: pass.
5. Checked the DAG records and unit route. The target node records the new proof and
   dependency, and the split node records its module, declaration, source, and proof
   dependencies. No target or unit statement changed. Verdict: pass.

Changed only this report section; no Lean declarations or DAG statements were altered.
