# Worker report

1. Files written:
   - `dag/nodes/sec-purity-real-sheaves/lem-tw-root-of-unity-modulus.json`: item, split with one proof step; no direct Mathlib match for the full item.
   - `dag/nodes/sec-purity-real-sheaves/lem-tw-complex-norm-root-of-unity.json`: statement, Mathlib leaf; exact match `Complex.norm_eq_one_of_pow_eq_one` in `Mathlib/Analysis/Complex/Basic.lean:101-102`.
   - `citations.json`: verbatim citations for step 1.
2. Attachments: none. The source declaration `AlgebraicGeometry.WeilGroup.frobeniusWeight_eq_zero_of_pow_eq_one` was checked but is not an exact attachment: its conclusion is only `frobeniusWeight ι qx ζ = 0`, while the item also asserts both modulus-one clauses.
3. WANTED: none.
4. The imported item proof was a single paragraph. I retained its route and made the non-elementary norm fact explicit as the Mathlib leaf above. The source theorem in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/RankOne.lean:56-58` is finished and sorry-free, but it does not state the full natural-language item. The item's absolute-value convention is the current `def-tw-eigenvalue` convention (complex modulus through `ι`), so the two modulus clauses agree; the weight clause is its `w=0` instance.
5. Nothing remains unfinished. The server-side `check_dag` passed before this report was written.

## Review by Q64

I read the item node, `def-tw-eigenvalue`, the `sk-p-real-rankone` unit, the `sec-purity-real-sheaves` chapter, and both the master and main-20261015 blueprint files for this item. The two blueprint statements and proof paragraphs agree. I also read the source declaration and its proof at `RankOne.lean:53-58`; it invokes the project theorem `norm_eq_one_of_pow_eq_one` but exposes only the weight-zero equality, which is why I did not attach it to the full item.

The only proof step takes `m ≥ 1` and `ζ^m = 1`, applies the field isomorphism to obtain `(ι ζ)^m = 1`, and uses the cited Mathlib statement “For every complex number `z` and natural number `n`, if `z^n=1` and `n≠0`, then its complex norm satisfies `‖z‖=1`.” The nonzero exponent hypothesis follows from `m ≥ 1`. The cited `def-tw-eigenvalue` statements say verbatim that `|β|_ι = |ι(β)|` and that weight `w` means `|α|_ι = q^(w/2)`, so the norm equality gives the absolute-value and complex-modulus clauses and `w=0` gives weight zero. The step is marked non-elementary because it relies on the Mathlib theorem; the remaining transport through `ι`, and `q^(0/2)=1`, are the elementary parts of that same argument.

For the new node I searched the whole DAG and blueprint for root-of-unity norm statements and found no duplicate. LeanFinder and LeanSearch returned the exact Mathlib declaration; Loogle's name query and msearch's grep index returned no hit, so I read the pinned Mathlib source directly and recorded those index misses together with the confirming source location. I tested the statement on `n=1,z=1` and `n=2,z=-1`; the field-isomorphism transport preserves the power equation, including the general `m` case. No additional hypotheses are needed beyond `n ≠ 0`.
