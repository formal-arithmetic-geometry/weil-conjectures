Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-support-iterated-cones.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-sc-single-cone-principal-support.json` (statement, Mathlib no match)
- `dag/nodes/sec-picard-framework/lem-sc-zero-cone-binomial.json` (statement, Mathlib no match)
- `citations.json`

Attachments: none.

WANTED: none.

The Lean source under `WeilConjectures/` has no declaration tagged `lem-sc-affine-support-iterated-cones` and no declaration stating this iterated-cone theorem. The item was therefore split. The source is Stacks Tag 08EK (Lemma 36.13.10), cone construction. The two child statements isolate facts used by that construction and are strictly smaller than the item; neither is a restatement of an existing DAG node. The `Mathlib` searches were run for the item and both children with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

## Not duplicates

`lem-sc-single-cone-principal-support` vs `lem-pc-perfect-two-out-of-three`: the former concerns localization support of a cone of multiplication and optionally perfection; the latter only states the abstract two-out-of-three property for perfect objects in a distinguished triangle.

`lem-sc-zero-cone-binomial` vs `lem-pc-kflat-cone-direct-sum`: the former computes finite iterated cones of zero endomorphisms with binomial multiplicities in a derived category; the latter concerns K-flatness closure under countable direct sums and arbitrary cones.

`lem-sc-single-cone-principal-support` vs `lem-sc-affine-support-iterated-cones`: the child treats one multiplication cone and one principal open, while the item treats an iterated family of cones, their union support, and the restriction decomposition.

`lem-sc-single-cone-principal-support` vs `lem-sc-affine-perfect-support-extension`: the child is the single-cone local support/perfectness input; the existing node constructs a global extension with a prescribed restriction using several additional lemmas.

`lem-sc-zero-cone-binomial` vs `lem-sc-affine-support-iterated-cones`: the child is only the finite combinatorial calculation for zero cones on U; the item also proves support on X and perfection of the successive cones.

`lem-sc-zero-cone-binomial` vs `lem-sc-affine-perfect-support-extension`: the child computes the restriction of a fixed cone iteration, whereas the existing node proves the broader affine support-extension theorem and uses the item as an input.

## Review by G1

I read the item source, Stacks Tag 08EK, and checked that its affine hypotheses, the generators `g_i`, the closed set `T=V(g_1,\\dots,g_s)`, the perfect object `E`, and the optional quasi-compact open `U` and object `F` match the item statement. I also searched the whole DAG and blueprint for the cone-support and zero-cone facts before creating the two child nodes; no existing node states either fact. Both child statements introduce all objects they use and carry the same Stacks source place.

Step 1 uses `lem-pc-perfect-two-out-of-three`, whose statement explicitly says that the third object in a distinguished triangle is perfect when the other two are perfect; this supplies the induction from `C_0=E` to every `C_i`. Step 2 uses the exact principal-open clause of `lem-sc-single-cone-principal-support`; after restriction to `D(g_i)`, later cone triangles have zero terms, so the vanishing propagates, and the principal opens cover `X\\setminus T`. Step 3 is elementary from the stated zero action on `F`, direct sums and shifts, and exactness of restriction on cone triangles. Step 4 uses the verbatim binomial decomposition statement of `lem-sc-zero-cone-binomial`.

I tested the decomposition on `s=0`, giving `F\\oplus F[1]`, on `s=1`, giving `F\\oplus F[1]^{\\oplus 2}\\oplus F[2]`, and on `s=2`, giving multiplicities `1,3,3,1`. The support argument was checked on each principal open `D(g_i)` and on their union. No source or statement error was found.

What could not be finished: no Lean compilation is permitted at stage 1, and no Lean declaration currently states the item.

## Second reading by G1

- Item statement: checked against `/home/ubuntu/c1-stacks-review/perfect.tex`, Tag 08EK, `lemma-lift-perfect-complex-plus-shift-support`, including affine `X`, finite principal equations, successive multiplication cones, support on `T`, and the restriction formula; verdict: hypotheses and conclusion agree.
- Step 1: checked against the item cone triangles and `lem-pc-perfect-two-out-of-three`; verdict: the induction uses exactly the cited perfectness statement.
- Step 2: checked against the principal-open localization argument in Tag 08EK and the statement of `lem-sc-single-cone-principal-support`; verdict: restriction to each `D(g_i)` vanishes and later cones preserve that vanishing, with `X\\setminus T=\\bigcup_iD(g_i)`.
- Step 3: checked against the zero-action hypothesis and restriction of cone triangles; verdict: the direct-sum and shift action is elementary and the restriction construction is stated explicitly.
- Step 4: checked against the zero-map cone calculation in Tag 08EK and `lem-sc-zero-cone-binomial`; verdict: the binomial multiplicities match the source.
- `lem-sc-single-cone-principal-support`: checked for self-contained affine, derived, cone, and perfectness hypotheses, and searched the DAG for duplicates; verdict: a strict single-cone input, with no Mathlib match.
- `lem-sc-zero-cone-binomial`: checked for self-contained scheme, derived-object, and `s\\ge0` hypotheses, and searched the DAG for duplicates; verdict: a strict finite combinatorial input, with no Mathlib match.
- Small cases checked: `s=0` gives `F\\oplus F[1]`, `s=1` gives multiplicities `1,2,1`, and `s=2` gives `1,3,3,1`; the empty scheme and zero endomorphism cases are consistent.

Changes made in this second reading:

- Corrected the item's `created.item` metadata to `lem-sc-affine-support-iterated-cones`; the worker had incorrectly named the parent support-extension item.
- Removed the redundant `def-weil-abstract-derived-category` citation from the zero-cone statement; `def-pc-derived-category` already defines the notation used.
