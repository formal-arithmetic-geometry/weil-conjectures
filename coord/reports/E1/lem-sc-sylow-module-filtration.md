# E1 worker report: lem-sc-sylow-module-filtration

## Files

- `dag/nodes/sec-curve-estimates/lem-sc-sylow-module-filtration.json`: split into four steps; no new nodes.

## Source and declarations

- Read Stacks `etale-cohomology.tex`, Lemma `0A3R` (`lemma-pullback-filtered`), proof, and Lemma `0GIZ` (`lemma-action-l-group`), statement and omitted-proof hint. The finite-module monodromy passage is repeated in Lemma `0GJ0` (`lemma-pullback-filtered-modules`), proof. Tags were checked against `/home/ubuntu/c1-stacks-review/tags/tags` and labels against its `etale-cohomology.tex`.
- Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, Sylow, and filtration. No declaration there states the whole finite ell-primary module reduction. `Representation.invariants_ne_bot_and_exists_filtration_of_isPGroup` in `WeilConjectures/Mathlib/RepresentationTheory/Invariants.lean:132` gives only the finite-dimensional `F_ell` representation step. It belongs to the existing node `lemma-weil-pbc-finite-l-group-filtration`, already audited `closed`; the compressed sorry map records that declaration and its private proof dependencies as sorry-free. `Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_reduction` in `ConstructibleSheaf/LocallyConstantReduction.lean:51` has `sorry` and concerns sheaves, so it is not an attachment for this item.
- Blueprint search `tools/blueprint_refs.py search 'Sylow reduction'`, `'finite l-group representation'`, and `'prime-index filtration'` found no other blueprint node with this full statement. The related finite `F_ell` representation node is narrower, and the existing Sylow node supplies the index clause.

## Split

1. The continuous action on finite `M` factors through its finite image `Q`; the kernel is the finite intersection of open stabilizers. The definition cited by this step states the continuity condition.
2. `lem-weil-pbc-sylow-subgroup-prime-index` supplies an ell-Sylow `P` of `Q` and its prime-to-ell index. Its inverse image `H` is open, and the coset bijection gives `[G:H]=[Q:P]`.
3. The finite ell-primary group has a common exponent `ell^n`. The explicitly written subgroups `M_j={m:ell^j m=0}` are stable, and each successive quotient is a finite `F_ell[P]`-module.
4. `lemma-weil-pbc-finite-l-group-filtration` supplies a flag with trivial one-dimensional quotients for each nonzero quotient of step 3. Pullback flags along `M_{j+1}->M_{j+1}/M_j` and concatenate. The quotient calculation is explicit in the node.

No new statement, source, unit, or chapter file was changed. No `WANTED` source: the Stacks TeX is available in the read-only local checkout, and `literature/LIST.md` records it as obtained. The imported proof hid the Sylow theorem and group-representation theorem in one paragraph and described the powers-of-ell filtration ambiguously; the split now cites both existing nodes and uses annihilator subgroups.

## Edge cases and checks

- `M=0`: take exponent `n=0`, `Q=P=1`, `H=G`, and the one-term filtration. Zero intermediate quotients are skipped; no nonzero-vector hypothesis is applied to them.
- `ell M=0`: the exponent filtration has one nonzero quotient, and the existing finite-group representation theorem gives its flag.
- Trivial group action: `Q=P=1`, so `H=G` and the filtration is an ordinary composition flag of finite `F_ell`-vector spaces.
- JSON parsed; `proof_deps` equals the union of step uses; every step has a Boolean `elementary`. Mathlib searches were made with LeanSearch, LeanFinder, Loogle, and a read-only Mathlib source grep. The available source checkout for the grep is a separate project, so the LeanSearch results and the existing, reviewed Mathlib leaf are the version-specific evidence here. The shared clone is read-only and its `review_split.py` cannot inspect sandbox files without packaging; the lead's delivery preflight will run it on the packaged commit.

## Review by E1

I read the item's statement and its four proposed steps beside Stacks `etale-cohomology.tex`, Lemma `0A3R` (`lemma-pullback-filtered`), and Lemma `0GIZ` (`lemma-action-l-group`); `0GJ0` repeats the finite-module monodromy argument. The Stacks tags and TeX labels agree. The source's `0GIZ` conclusion gives trivial group action on successive quotients, while this item asks for one-dimensional `F_ell` quotients. The split supplies that stronger conclusion by filtering the ell-power quotients with the existing representation theorem; it does not attribute the stronger conclusion to `0GIZ` alone.

For step 1, `def-exc-continuous-cohomology` states precisely that every element of a discrete continuous module has open stabilizer. Finiteness of `M` makes their intersection an open normal kernel, and compactness of profinite `G` makes its quotient finite. For step 2, `lem-weil-pbc-sylow-subgroup-prime-index` states both the existence of an ell-subgroup `P` of finite `Q` and the indivisibility of `[Q:P]`; openness and equality of coset indices follow from the quotient map. For step 3, the finite ell-primary hypothesis supplies a uniform exponent. The calculation `ell M_{j+1} subset M_j` makes each quotient an `F_ell`-space, and equivariance preserves every `M_j`; this step needs no unstated theorem. For step 4, `lemma-weil-pbc-finite-l-group-filtration` states the needed flag for each nonzero finite-dimensional `F_ell[P]`-module and is `closed` on slopmaster2. The inverse-image quotient calculation identifies each pulled-back factor with the corresponding trivial line; concatenating over all `j` yields the item, rather than merely relabelling it.

I checked the hypotheses at each use: `Q` is finite before invoking Sylow, `P` is an ell-group before invoking the representation node, and each nonzero `V_j` is finite-dimensional over `F_ell`. At `M=0` choose `n=0`; for a zero intermediate quotient skip the representation theorem; for `ell M=0` the construction reduces to a single `F_ell` representation; a trivial action permits `H=G`. No new node was needed, so there is no new-node statement or source to validate. I corrected two source tags during this review: `lemma-action-l-group` is `0GIZ`, and `lemma-pullback-filtered-modules` is `0GJ0`, not the adjacent `0A3S`/`0A3T` tags. I also corrected the Lean line of the nonmatching sheaf theorem in the report to 51. The imported statement itself was preserved.
