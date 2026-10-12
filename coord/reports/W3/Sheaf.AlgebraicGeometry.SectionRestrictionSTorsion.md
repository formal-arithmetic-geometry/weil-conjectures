## What changed

Proved `AlgebraicGeometry.Scheme.Modules.section_restriction_s_torsion` using a finite affine
cover trivializing the invertible module. The proved affine localization kernel criterion
kills each restricted section by a power of its local coefficient. A finite supremum exponent,
the local tensor-power formula, and sheaf uniqueness give the global tensor-power vanishing.
Added the proof-only import `Sheaf.AlgebraicGeometry.SectionNonvanishingZeroLocus`; updated the
DAG proof route to record this bridge. The statement and existing docstring are unchanged.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.Modules.section_restriction_s_torsion`
(node `lem-sc-p1-section-restriction-s-torsion`). No holes were added; no sorries remain
in the delivered module. This is a proof, not a decomposition: every lemma used is already proved.
The launcher compilation passes without warnings. Empty covers use exponent zero; the local
argument also applies to the zero section and to nilpotent local coefficients.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.Coherent` and
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`. Their required APIs are already exposed
by the unchanged public imports. No planned mathematical nodes are bypassed: affine localization,
local rank-one freeness, the residue-field dictionary, and finite-cover uniqueness all remain
parts of the argument. No whole modules are claimed to leave the targets' closure because the
removed imports may still be reached elsewhere.

## Where the brief, the DAG or earlier work was wrong

The DAG did not explicitly list the existing proved
`nonvanishingLocus_eq_compl_support_zeroLocus` bridge needed to translate the supplied set equality
into the zero-locus complement used by `basicOpen_coeff_eq`; its node is now a proof dependency.
Quasi-separatedness is not needed by this injectivity argument, but the theorem signature retains
it unchanged. No new statements, definitions, or nodes were introduced.

## Second reading by W3

1. **Unchanged statements:** Compared the delivered module and node with the repository versions. The theorem signature and existing declarations are byte-for-byte unchanged; only the proof and proof-only import differ. Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it has no `sorry`, forbidden declarations, or warnings. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Split statements:** No statements were split off or added. Existing localization and nonvanishing-locus lemmas are used; searches found no duplicate declaration. Verdict: pass.
4. **Pruning and route:** The proof uses the finite affine trivializing cover, affine localization criterion, tensor-power chart formula, and sheaf uniqueness from the planned route. The unused `Coherent` and `Invertible` proof imports are removed; `SectionNonvanishingZeroLocus` is proof-only. Verdict: pass.
5. **DAG and unit:** The node proof, dependencies, and origin match the proof, including the nonvanishing-locus bridge; the theorem's unit route remains unchanged. Verdict: pass.

Changed in this reading: restored the node's bridge dependency and route metadata to agree with the Lean proof, and documented the review above. No mathematical statements or definitions changed.
