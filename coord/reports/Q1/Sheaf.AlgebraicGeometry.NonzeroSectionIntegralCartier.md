## What changed

Proved AlgebraicGeometry.Scheme.Modules.nonzero_section_integral_cartier with its signature unchanged. The proof first establishes that the section morphism and its locally principal zero-locus ideal are nonzero, then uses the existing integral locally principal ideal criterion. The affine ideal formula and regularity of affine Cartier generators give all local conclusions. Updated the item's proof plan and attached two already proved source results as DAG nodes. The Jacobian unit route stays unchanged.

## Proved and sorry left

Closed 1 hole: AlgebraicGeometry.Scheme.Modules.nonzero_section_integral_cartier (lem-pc-nonzero-section-integral-cartier). No holes remain in the item, no holes added, and no statements split off. This is a proof, not a decomposition. All lemmas used have proofs in the existing library.

## No longer needed

Removed proof imports Sheaf.AlgebraicGeometry.InvertibleModuleGenericStalk, WeilConjectures.AlgebraicGeometry.Modules.Invertible, and WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme. The first and third modules are unnecessary for this proof; Modules.Invertible remains available transitively for the unchanged statement. Pruned proof dependency lem-sc-invertible-module-generic-stalk. Replaced the broad lem-pc-zero-scheme-properties dependency with the precise local-principal, ideal-local, and zero-iff nodes. The definition nodes def-pc-zero-scheme, def-sc-invertible-module, def-nagata-effective-cartier-ideal and def-pc-divisor-line-bundle are no longer direct proof dependencies; relevant definitions remain in the unchanged statement environment. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The planned generic-stalk argument was unnecessary: the source library already proves that a nonzero locally principal ideal on an integral scheme is invertible. The recorded declaration of lem-pc-zero-scheme-properties points to the unrelated Hilbert center theorem; the precise child nodes correctly name the zero-locus lemmas, which this proof uses. No signature or definition changes were required.

## New nodes

lem-pc-nonzero-locally-principal-ideal-invertible attaches the existing proved AlgebraicGeometry.Scheme.IdealSheafData.IsLocallyPrincipal.isInvertible. The zero ideal is excluded explicitly; integrality is essential. No new Lean module or hole.

lem-pc-cartier-affine-generator-regular attaches the existing proved AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.mem_nonZeroDivisors. It applies also on the empty affine open; coefficient nonzeroness in the item separately uses nonemptiness. No new Lean module or hole. No change records are needed.

## Second reading by Q1

1. Compared the sole delivered Lean module with the repository using diff. PASS: the existing theorem signature is byte-for-byte unchanged; no definition, declaration visibility, instance, or file option changed. The changes are the proof, its explanatory proof paragraph, and removal of three proof-only imports. No change record is required. The existing node changes only proof, proof_deps, and proof_origin.
2. Compiled the delivered file with lcompile.py: clean, 3.6 seconds. PASS: no sorry or forbidden declarations in the delivered module. Compiled a scratch copy with #print axioms for AlgebraicGeometry.Scheme.Modules.nonzero_section_integral_cartier and both newly attached source theorems; each reports exactly propext, Classical.choice, Quot.sound, with no sorryAx. No data is chosen from an unproved existence statement.
3. PASS: no statement was split off and no Lean declaration or hole was added. Read the proofs of both existing source results attached as new nodes. On Spec of a domain, a nonzero principal ideal has a regular generator; the zero ideal is correctly excluded. The affine regular-generator statement also holds on the empty affine open (zero ring), whereas the item's coefficient-nonzero assertion correctly assumes nonemptiness. A reducible scheme with zero divisors shows why integrality cannot be omitted. Independent Loogle and LeanFinder searches using principal ideals, regular generators, and effective Cartier divisors found only lower-level results, not a shorter replacement; rg found no duplicate source attachments or alternative Sheaf theorem.
4. PASS: the proof goes directly from the nonzero section morphism through proved local-principality and ideal-sheaf criteria to the local coefficient assertions. It does not import or use the open generic-stalk theorem or the open module-level local-principality wrapper. Retained public imports support the unchanged statement environment; the sole proof import EffectiveCartier supplies generator regularity. The No longer needed section lists every old proof dependency removed. Read dag/units/sk-prop-jacobian.json and its realized fields: this changes only the argument below the zero-divisor step, preserves that step, and bypasses no realized unit result.
5. PASS after clarification: the item's dependency union equals the uses of its proof steps, the two new nodes attach existing proved source declarations, and their hypotheses/conclusions match those declarations. Their records contain source, mathematical proof, searches, provenance, chapter, unit, and Lean attachment. The local-principality node records an open module-level wrapper, while this proof uses its proved source theorem after explicitly supplying the invertibility bridge; clarified this distinction in the item's proof plan rather than introducing a duplicate theorem or depending on the wrapper's sorry.

Second reading changed only this review report and the proof-plan clarification above. The Lean proof required no repair. Holes closed: AlgebraicGeometry.Scheme.Modules.nonzero_section_integral_cartier. Holes added: none.
