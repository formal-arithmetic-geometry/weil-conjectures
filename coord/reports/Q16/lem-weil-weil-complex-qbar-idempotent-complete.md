# Q16: lem-weil-weil-complex-qbar-idempotent-complete

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-weil-complex-qbar-idempotent-complete.json`: statement, split into four steps; no Mathlib match for the whole statement. Generic Mathlib Karoubi-equivalence results cover only the last clause after idempotent completeness has been established.
- No new nodes and no new Mathlib leaves.
- `citations.json`: eight verbatim statement excerpts, one for every step/dependency pair.
- `searches.jsonl`: actual search-command log. Both LeanFinder phrasings, LeanSearch, Loogle and two Mathlib grep queries were read and recorded; all services answered.

## Attachments

None. The blueprint tag and idempotent/Weil searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration stating this item. `WeilConjectures/WeilSheaf/Category.lean:156-177, 235-244` instead constructs the bounded constructible subcategory of the derived category of Weil sheaves. That category has Ext morphisms and is not the fixed-pair category required by the reviewed definition. Neither this construction nor the generic Karoubi theorems is an attachment for this item. The item itself has Lean-audit state `none`; no open Lean declarations need importing into the DAG.

## Wanted literature

None. The item and its proof were read in both the master blueprint and current main-20261015 snapshot, at `sec-six-functors-basics/sk-def-purity-conv/lem-weil-weil-complex-qbar-idempotent-complete.{md,proof.md}` for the latter. I also read the current conventions unit, the chapter record, all cited DAG statements, the underlying coefficient lemma's current blueprint proof, and Balmer–Schlichting, Definition 1.2 and Remark 1.4, PDF p. 2. The replacement Frobenius calculations are an agent proof and are marked as such.

## Statement corrected

STATEMENT-DISPUTED: “exact equivalence” is not a well-typed assertion for the category actually defined by `def-weil-weil-sheaf-complex`. That reviewed definition explicitly says that no triangulated structure is supplied, and defines objects as fixed pairs in the underlying derived category. Both blueprint snapshots incorrectly identify this with the derived category of Weil sheaves, then apply a bounded-t-structure theorem. This identification fails already at a geometric point.

Take Y_0 = Spec(k_0), coefficients E or Qbar_l, trivial Frobenius on A = Lambda and C = Lambda, and B = Lambda^2 with Frobenius matrix [[1,1],[0,1]]. The inclusion of the first coordinate and projection onto the second give an equivariant short exact sequence 0 -> A -> B -> C -> 0, with no equivariant section: the Frobenius of a lift (x,1) is (x+1,1). This is a nonsplit extension of Weil sheaves, hence gives a nonzero derived-of-Weil-sheaves Ext^1 class. In fixed pairs the group Hom((C,1),(A[1],1)) is zero, since the underlying geometric-point Hom is zero, as the reviewed definition itself notes. Thus the categories used by the old proof differ. Nor can one simply declare every equivariant triangle with underlying distinguished triangle to be distinguished: this very sequence, with zero connecting map, is distinguished after forgetting, but a distinguished triangle with zero connecting map would split equivariantly.

The correction removes precisely the word “exact” from the statement. All original hypotheses and the idempotent-completeness and canonical-equivalence conclusions are retained. The proof also verifies additivity of the category and equivalence. No triangulated structure is invented. If one later gives these additive categories their split exact structures, this additive equivalence preserves split exact sequences, but that extra convention is not required or inserted here.

The old use of `prop-weil-filtered-retract-descent` also took more than that node states: its statement concerns the underlying coefficient pair category P_T, not a colimit of Weil-pair categories. I removed that misuse, and the unrelated abelian-heart and bounded-t-structure inputs, instead of treating their proofs as statements about equivariance. The already split `lem-weil-qbar-idempotent-complete` supplies exactly the needed non-equivariant input.

The conventions unit has no proof steps, and the item is not its key statement. I did not modify its realization fields or any chapter/unit metadata. This repair occurs below the unit level and does not replace a proof step prescribed by the unit. The generic use of the underlying coefficient lemma is declared in `split_report.tool_uses` for the maintainer's judgment.

## Unfinished work

None at stage 1. The single non-elementary input is an existing split node. No new lemmas are left unsplit by this delivery.

## Not duplicates

No new nodes. Whole-DAG keyword searches and `tools/blueprint_refs.py search` for `idempotent`, `fixed pair`, and `Weil complex` found the existing underlying coefficient lemma, fixed-pair definition and fully faithful Karoubi-inclusion lemma. They are reused, not restated. No other blueprint node states the corrected Weil-category result, so `same_as` is empty.

## Review by Q16

I checked B–E against the actual JSON and source statements, not just the imported dependency list. There are no new nodes to test for statement-only shape, sources, duplicates or Mathlib-leaf coverage. The item's statement introduces the original datum and scheme and keeps its three definition dependencies; the only statement change is explained above. Searches were made with the required msearch command and copied with their exact query texts, without treating the generic results as a theorem about the Weil category. The source and audit metadata and import flags are preserved.

For step 1, I reread `def-weil-weil-sheaf-complex`: it specifies precisely pairs (K,theta), equivariant arrows, and the faithful forgetful functor, so an idempotent gives e^2=e and e theta = theta T(e) in the underlying category. `def-weil-finite-type-morphism` gives the finite affine-cover criterion used to check the hypothesis on Y; tensoring finite algebra generators with k proves the required base-change assertion directly, without adding a node. `lem-weil-qbar-idempotent-complete` explicitly asserts idempotent completeness of C_Y for a finite-type k-scheme and l different from p. Those are exactly the hypotheses here; it requires no separatedness. Its conclusion supplies L,i,r with ri=1 and ir=e, not an equivariant splitting or a chosen finite-stage Frobenius structure. There is no cycle: this underlying coefficient lemma's dependencies involve coefficient rationalization, colimit and Karoubi results, not this Weil-pair item.

For step 2, I reread the rational-level morphism formulas and their extension to sums, and the algebraically closed-level comparison formulas, in `def-weil-derived-pullback-tensor-hom`. They justify that T is additive, including at a common coefficient stage; conjugation by the comparison isomorphisms preserves addition. The fixed-pair morphism equation in `def-weil-weil-sheaf-complex` then defines subgroups of the underlying Hom groups. Direct sums with the displayed structure isomorphism give the actual zero object and biproducts, with the inclusions and projections satisfying the same equivariance equations. This is an elementary verification from these two definitions, not a hidden assertion that fixed pairs are triangulated.

For step 3, I checked every domain and composition: theta_L = r theta T(i) goes TL -> L and psi = T(r) theta^{-1} i goes L -> TL. The two displayed inverse calculations use only ir=e, ri=1, functoriality, and e theta=theta T(e). The two additional equations are exactly the fixed-pair morphism condition for i and r, so the splitting is in the desired category. No inverse image needs to preserve images or kernels, no Frobenius-stable lattice is chosen, and no unproved descent of equivariance is assumed. This is a few-line algebraic check, so it remains an elementary step rather than a new generic fixed-pair lemma.

For step 4, `def-weil-karoubi-envelope` gives the morphism condition, the identity e of (X,e), and the canonical inclusion. The displayed retract maps satisfy that condition and are inverse in the envelope. `lem-weil-karoubi-envelope-fully-faithful` states precisely full faithfulness of this inclusion for an additive category; step 2 verified the hypothesis. Thus essential surjectivity is proved by the explicit splitting, not taken from the cited node. I also read Mathlib's generic `toKaroubi_isEquivalence` at Karoubi.lean:233 and its surrounding construction at 223-236; it matches this final inference but presupposes the central result, so the whole item is not a Mathlib leaf.

Small cases: for e=0 the underlying retract is a zero object, its unique Frobenius map is invertible, and the formulas still give the correct splitting; for e=1 choose L=K and i=r=1, recovering theta itself. The empty scheme causes no exceptional step. For a nontrivial Frobenius-stable direct summand, theta_L and its displayed inverse are exactly the restrictions induced by the retraction, so no unsupported stability assumption occurs. The Jordan-block example tests the source error but does not obstruct splitting actual idempotents. Every proof step has fewer than 800 characters; no long step conceals a sublemma. Each citation quote was checked as a literal substring of the current cited statement before writing citations.json.

The only correction to the source's route is the necessary fixed-pair repair described above. The resulting proof has one existing non-elementary input and three explicit elementary verifications, no clause moved to a new node, no unrecorded lemma or tag, and no forbidden SGA source. No Lean file was written and no compiler, Lake command or local DAG checker was run.

Dry-run repair: the first citation check required a longer excerpt for the fully faithful Karoubi-inclusion statement. Replaced the short predicate by the full assertion, including its functor formula; no mathematical step changed.
