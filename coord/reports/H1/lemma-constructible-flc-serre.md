1. Files written:
   - `dag/nodes/sec-proper-base-change/lemma-constructible-flc-serre.json`: repaired extension proof using Stacks 03RX (3), with closed kernel/cokernel attachments retained.
   - `dag/nodes/sec-proper-base-change/lem-constructible-constant-exact.json`: new statement-only node for exactness of finite constant etale sheaf sequences.
   - `dag/nodes/sec-proper-base-change/lem-constructible-shortexact-local-lift.json`: completed new-node metadata (`created`, `merged_into`, and `lean_audit`).
   - `citations.json`: updated verbatim citations for the repaired proof.

2. Attachments:
   - `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel` belongs to `lemma-constructible-flc-serre` (sorry-free, KernelCokernel.lean lines 309–330).
   - `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.cokernel` belongs to `lemma-constructible-flc-serre` (sorry-free, KernelCokernel.lean lines 321–342).

3. WANTED:
   - None. The extension route is sourced from Stacks Project `etale-cohomology.tex`, Lemma 03RX (3), proved through Modules on Sites Lemma 093U.

4. What was wrong or incomplete:
   - The imported extension step falsely claimed that the sheaf of splittings is locally inhabited and hence that every extension splits etale-locally. This fails for the nonsplit sequence `0 -> Z/2 -> Z/4 -> Z/2 -> 0` over `Lambda = Z/4`; its stalk sequence is nonsplit at every geometric point. The conclusion that the middle stalk is `M (+) N` was therefore also false.
   - I replaced that paragraph with the Stacks 03RX (3) finite-presentation route: choose `0 -> K -> Lambda^m -> N -> 0`, lift generators locally, form `g : K_U -> M_U`, identify `E|_U` as the cokernel of `(-g, incl)`, and apply the finite locally constant cokernel clause.
   - No existing DAG node stated exactness after passing a finite module sequence to constant etale sheaves, so I added `lem-constructible-constant-exact` after searching the DAG, blueprint, Lean source, and Mathlib.

5. What I could not finish:
   - The two new supporting nodes remain statement-only unsplit nodes because no exact Mathlib declaration closes either specialized etale-sheaf fact.

## Source error

The blueprint's torsor-of-splittings paragraph is mathematically false for a non-semisimple coefficient ring. For `Lambda = Z/4`, the constant sheaf extension `0 -> (Z/2)_X -> (Z/4)_X -> (Z/2)_X -> 0` is nonsplit on every nonempty etale object: at every geometric point its stalk is the nonsplit `Z/4` module sequence. Thus the splitting sheaf has no local section and is not a torsor. The corrected proof follows Stacks 03RX (3) instead.

## Review by H1

I read the item's Lean source `WeilConjectures/ConstructibleSheaf/KernelCokernel.lean`, including the sorry-free kernel and cokernel declarations at lines 309–342 and the sorried `of_shortExact` declaration at lines 344–359. I also read Stacks `etale-cohomology.tex`, Lemma 03RX (label `lemma-kernel-finite-locally-constant`), and its Modules on Sites proof route (Lemma 093U). The item statement agrees with the Lean declarations and with the Stacks closure statement; the finite-ring hypothesis makes the coefficient ring Noetherian and makes the chosen modules finite.

Step 1 uses the existing biproduct statement for a common trivialising cover and the existing Hom-constant statement for the induced module map; their statements explicitly give the cover and the constant kernel/cokernel restrictions. The kernel and cokernel declarations attach to the sorry-free Lean names listed above.

Step 2 uses `lem-constructible-shortexact-local-lift` only for local lifts of each chosen generator, and `lem-constructible-constant-exact` for exactness of `0 -> K_U -> Lambda^m_U -> N_U -> 0`; both cited statements say exactly those facts. It uses the biproduct statement to make `M_U (+) Lambda^m_U` finite locally constant and the Hom-constant statement for the cokernel clause applied to `(-g, incl)`. The remaining kernel computation is written out: surjectivity follows from `pi` and `q`, and a kernel pair has `v` in `K_U` and `a = -g(v)`. No torsor or splitting claim remains.

For the new constant-exact node I searched all DAG nodes and blueprint records, then searched Mathlib with LeanSearch, LeanFinder, and source grep; no exact declaration was found. For the local-lifting node I rechecked its same three searches and added the missing `created`, `merged_into`, and `lean_audit` fields. I checked hypotheses at each step, including finiteness of `K` from finite `Lambda` and exactness of the constant sequence. I tested the extension clause on the split extension, the zero extension, and the nonsplit `Z/4` extension above: the repaired cokernel construction applies to the nonsplit case and does not assert a splitting, while the old torsor route fails exactly as the counterexample predicts.
