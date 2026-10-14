## What changed

Closed the original amalgamation hole without changing its signature. Added two fully proved public lemmas: fpqc descent of normalized Picard classes over an arbitrary base with a section and universal structure-pushforward isomorphism, and fpqc descent of the relative Picard sheaf of a smooth proper geometrically integral curve. The main proof glues in the full Picard sheaf and then lifts the result through the sheafified degree-subfunctor inclusion. Updated its DAG proof and dependencies accordingly.

The normalized proof adapts the existing fppf argument and scalar-cocycle argument in Picard.Defs to fpqc covers, using the proved quasi-coherent descent API. The full Picard proof chooses a finite separable residue-field point, uses the rational-point splitting and Picard base-change isomorphism, and descends the sheaf condition by Mathlib's transitivity criterion. This keeps the unit's finite-extension, normalization and fpqc-descent route.

Compiled all three modules individually through lcompile.py; all compile without warnings. The private descent comparison supplies explicit family parameters to avoid expensive metavariable inference. It does not change any existing definition or interface. Edge cases: the normalized lemma handles empty test schemes and empty covering families through the general descent API; the curve lemma obtains nonemptiness from geometric integrality, and the degree argument works for arbitrary integers and arbitrary test schemes.

## Proved and sorry left

Closed: AlgebraicGeometry.exists_amalgamation_fpqc_sheafify_picardDegree (lem-pd-degree-picard-sheaf-fpqc-existence), one of one original holes.

Added and proved: AlgebraicGeometry.isSheaf_fpqc_picardFunctorNormalized (lem-pd-normalized-picard-fpqc) and AlgebraicGeometry.isSheaf_fpqc_picardFunctor (lem-pd-picard-sheaf-fpqc). All private helpers are proved. No sorry remains in any delivered module; no holes were added or split off.

Axiom probes for both new public theorems list only propext, Classical.choice and Quot.sound. The original amalgamation theorem additionally inherits sorryAx through the existing Picard degree theory; this delivery does not close those existing downstream obligations. The original hole is closed from existing degree declarations and the fully proved new descent lemmas.

## No longer needed

Removed direct proof imports from the item: WeilConjectures.AlgebraicGeometry.DensePoints, WeilConjectures.AlgebraicGeometry.Descent, WeilConjectures.AlgebraicGeometry.Picard.Defs and WeilConjectures.AlgebraicGeometry.Picard.RationalPoint. They are used transitively by the helper proofs, so their modules and original mathematical obligations remain needed; no node or module is globally pruned. The item imports only Sheaf.AlgebraicGeometry.PicardSheafFpqc for its new proof. Its original public imports stay unchanged.

No original route node is discarded: lem-pc-fpqc-descent, lem-pc-rational-hyp, thm-pc-pic-split and lem-pc-dense-separable-points are moved to the helper nodes; lem-pd-degree-locally-constant stays a direct dependency. No unused helper import remains.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The original plan is sound but omitted a Lean implementation of the fpqc normalized sheaf condition. Existing Picard.Defs proves the fppf version and contains the normalization and scalar-cocycle machinery; the same construction works with effective fpqc descent. The library also contains the generic over-site and sheaf-condition transitivity lemmas needed to descend from the finite field extension. No interface change or forced adaptation was necessary.

## New nodes

lem-pd-normalized-picard-fpqc: lean/Sheaf/AlgebraicGeometry/PicardNormalizedFpqc.lean. Fully proves normalized fpqc descent; there is no remaining work or new sorry. Source: Stacks Project [0D28](https://stacks.math.columbia.edu/tag/0D28), [0D2B](https://stacks.math.columbia.edu/tag/0D2B) and [023T](https://stacks.math.columbia.edu/tag/023T), with the existing Picard.Defs proof as the Lean construction.

lem-pd-picard-sheaf-fpqc: lean/Sheaf/AlgebraicGeometry/PicardSheafFpqc.lean. Fully proves the full curve Picard sheaf's fpqc condition by finite-point extension, normalized splitting and site transitivity. There is no remaining work or new sorry. No change record is needed: every existing public signature and definition remains unchanged.

## Second reading by S1

1. Compared the delivered target module with the repository version. The theorem signature is
   unchanged byte for byte; only its proof, explanatory comment, and proof-only imports changed.
   The two added helper modules introduce the declarations recorded by their DAG nodes and do not
   alter existing interfaces. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all` and searched the delivered Lean
   and DAG files for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, and
   `debug.skipKernelTC`. No prohibited proof holes or commands occur. Axiom probes for the two
   helper theorems and the target theorem give only `propext`, `Classical.choice`, and
   `Quot.sound`. Verdict: pass.
3. Checked both split-off statements against the existing definitions and declarations, including
   the normalized subfunctor, the full relative Picard sheaf, and the fpqc topology. The statements
   are true, strictly useful reductions, and are not duplicates of existing library or Mathlib
   declarations; the recorded searches and sources are present in the nodes. Verdict: pass.
4. Read the proofs from the target downward. The target uses the full Picard fpqc sheaf helper;
   that helper uses the normalized fpqc sheaf helper, finite separable point extension, base change,
   and the existing normalization route. Imports are minimal with proof-only dependencies plain;
   the unit route and its realized nodes are preserved. Verdict: pass.
5. Compared each helper's Lean declaration with its node's `statement`, `proof_deps`, and
   `proof_origin`, and checked the target node's updated route against the proof. The DAG records
   the two new modules and the target dependency exactly. Verdict: pass.

Changed during second reading: removed the temporary axiom-probe file after checking it and added
this review record; no Lean proof or statement required repair.
