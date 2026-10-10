Files written:

- `dag/nodes/sec-picard-framework/lem-sc-kahler-differentials-diagonal-ideal.json`: item, Mathlib leaf.
- No new nodes; there are no unsplit dependencies introduced by this item.

Attachments:

- None. No sorry-free project declaration carries the item under its blueprint tag.

WANTED:

- None.

What was checked and changed:

- The source item and its Stacks source are the affine diagonal calculation, Tag 00RW. The available Stacks checkout does not contain that tag text, but the node statement is the standard affine formulation and agrees with Mathlib's implementation.
- I searched the whole DAG and blueprint for the tag, diagonal conormal, and Kähler differential formulations. Existing Kähler-differential nodes concern the universal property and the first exact sequence, not this diagonal identification, so there is no duplicate.
- I read Mathlib `RingTheory/Kaehler/Basic.lean`: lines 64-65 define `KaehlerDifferential.ideal` as the kernel of the multiplication map; lines 153-154 define `KaehlerDifferential` as that ideal's cotangent quotient; lines 218-221 (`KaehlerDifferential.D_apply`) give the class of `1 ⊗ₜ[R] a - a ⊗ₜ[R] 1`. I also read `RingTheory/Ideal/Cotangent.lean`, lines 41-47, which define the cotangent quotient as `I/I²` and provide its quotient module structures. Taking `S = A` gives every clause of the item, with the displayed isomorphism being the definitional identification.
- I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`. LeanSearch was unavailable and is recorded as unavailable; the other searches found the declarations above. The item is therefore marked `status: mathlib` with a multi-declaration `mathlib_match` and no proof steps.

## Review by M1

I checked the statement against the imported item and verified each hypothesis: `R` and `A` are commutative rings with the algebra structure induced by the ring homomorphism, `I` is exactly the kernel of the tensor-product multiplication map, and the cotangent module is `I/I²` with the quotient action. The Mathlib declarations supply the construction and formula directly, so no auxiliary node or citation step is required. I tested the identification on the degenerate cases `A = R` (the kernel and differentials are both zero) and a polynomial algebra (the formula gives the usual generator differentials). The only correction was changing the imported unsplit status to a Mathlib leaf and recording the exact declarations and source lines; no mathematical statement was changed.

What could not be finished:

- Nothing remains for this item.

## Second reading by M1

- Item statement: checked against Stacks Algebra Tag 00RW (algebra-lemma-differentials-diagonal); the local checkout has no imported `algebra.tex`, so the tag text was cross-checked against the tag index and the standard affine statement. The hypotheses and conclusion agree, including the kernel of multiplication, the quotient module structure, and the formula for `\mathrm da`.
- New node `lem-sc-kahler-differentials-diagonal-ideal`: checked as a statement-only Mathlib leaf against `KaehlerDifferential.ideal` (Basic.lean 64-65), `KaehlerDifferential` (153-154), `Ideal.Cotangent` (Cotangent.lean 41-47), and `KaehlerDifferential.D_apply` (Basic.lean 218-221). Its definitions are self-contained through `[def-weil-pbc-kahler-differentials]`, and the recorded searches include grep, LeanFinder, Loogle, and the unavailable LeanSearch service.
- Proof steps: none; the node is intentionally a Mathlib leaf, so there are no uncited non-elementary steps or citation quotes required.
- Small cases checked: `A = R` gives `I = 0` and zero differentials; `A = R[x]` gives the expected class of `1\otimes x-x\otimes1` mapping to `dx`; the zero ring and a field specialization are consistent with the same definitions.

Changes made in this second reading: appended this audit section to satisfy the delivery contract. No node statement, Mathlib metadata, or proof dependency required mathematical repair.
