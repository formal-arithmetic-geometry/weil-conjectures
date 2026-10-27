1. Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-epp-normal-base-branch-conjugacy.json` — statement split into four proof steps; no Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-tensor-invariant-powers.json` — new unsplit statement node; no Mathlib leaf.

Attachments: none.

WANTED: none. The proof follows the available Stacks source and an explicitly recorded invariant-power repair for its inseparable case.

The imported item had an empty proof, so it was not already split. I searched the complete Lean source for the blueprint tag and the relevant normal-branch names and found no matching declaration. I searched the DAG for Tag 09EU, normal tensor products, complete DVR normalization, and ramification; I reused the existing nodes `lem-sfb-dvr-algebraic-normalization-structure`, `lem-per-complete-dvr-finite-normalization`, `lem-weil-pbc-algebra-tensor-pushout-universal-property`, `def-weil-pbc-integral-closure`, `def-weil-pbc-localization-at-prime`, and `lem-weil-pbc-dvr-unit-times-uniformizer-power`. The new invariant-power assertion was searched with LeanFinder, LeanSearch, Loogle, and Mathlib grep; the recorded results do not state it as a one-line specialization.

The Stacks proof of Tag 09EU says “Since K = (K_1)^G” even when the normal extension is allowed to be inseparable. That equality is not valid in general; the corrected proof uses the new strictly smaller invariant-power statement, which is enough for the orbit-idempotent contradiction. The target statement itself remains faithful to Tag 09EU and to the imported blueprint.

## Not duplicates

lem-sfb-normal-tensor-invariant-powers vs lem-sfb-epp-normal-base-branch-conjugacy: the new node is only the invariant-power lemma for fixed elements of a reduced field tensor; the item additionally constructs normalized DVR branches, proves the automorphism action on integral closures, proves transitivity on maximal ideals, and transports ramification indices.

## Review by NZ

I read the item source in `literature/stacks-project/more-algebra.tex`, Tag 09EU (`lemma-galois-relative`), together with Remark 09EM (`remark-construction`) and the complete-normalization argument of Tag 09F8. I also read the statements of every cited DAG node. Step 1 uses the existing normalization-structure statement for the finite reduced tensor product and the existing complete-DVR normalization theorem; those statements give the field factors, finite/integral closures, local DVR maps, and unique maximal ideal of the lower normalization. The product description of the integral closure and the description of maximal ideals of a finite product are elementary coordinate arguments written in the step.

Step 2 uses the tensor universal property and the integral-closure definition exactly as stated: the tensor automorphisms preserve nilpotents and monic equations, hence descend to the reduced tensor and restrict to both integral closures. The action on the lower ring preserves its unique maximal ideal because ring automorphisms permute maximal ideals.

Step 3 is the repaired transitivity argument. I checked that coordinate idempotents of a finite product of fields are exactly the primitive idempotents, so an orbit gives a nontrivial fixed idempotent. The new node says every fixed reduced-tensor element has a positive power in the scalar image; applying this to the idempotent forces a scalar idempotent in the field (L), a contradiction. The actions on the product of integral closures have the same coordinate permutation, so this proves transitivity on maximal ideals. The new node is strictly smaller than the item and carries only this invariant-power input.

Step 4 uses the localization definition to write the induced isomorphism on localizations and uses the existing DVR factorization statement for a nonzero element. Locality makes the image of a lower uniformizer a nonunit, hence its exponent is positive; cancellation in the DVR domain gives uniqueness. Transporting the ideal equality along the conjugating localization isomorphism proves branch-independent ramification and the final index-one implication.

I checked the hypotheses in each use: the normalization node is applied only in its finite-extension case; the complete-DVR node is applied to the finite field factors; the scalar map from the field (L) is injective because the reduced tensor product is nonzero; and the localization denominators are transported by the prime correspondence. I corrected the source's inseparable fixed-field inference without changing the target statement.

## Source error

Tag 09EU's proof uses (K_1^G=K), which fails for a nontrivial purely inseparable normal extension: in characteristic (p), take (K=\mathbf F_p(t)), (K_1=\mathbf F_p(t^{1/p})). Its automorphism group is trivial, so its fixed field is (K_1), strictly larger than (K). This affects the source proof, not the item statement; no statement correction or hypothesis addition is made.

For the new node I read the invariant-lift paragraph of 09EU and `fields.tex`, Tag 030M (`lemma-normal-case`), including its fixed-field description. A proof plan is as follows, retained here rather than inside the new statement-only node. Let (T=L\otimes_KE), lift (x\in T_{red}^G) to (t\in T), and put (F=E^G). In characteristic (p>0), each (\sigma(t)-t) is nilpotent; since (G) is finite, choose one (p)-power (q) annihilating all these differences. Then (t^q) is invariant in (T). Invariant elements of (L\otimes_KE) are (L\otimes_KF): write an element with (K)-linearly independent (L)-coefficients; invariance forces each (E)-coefficient to lie in (F). Tag 030M says (F/K) is purely inseparable. Raising the finitely many coefficients in (F) to one further sufficiently large (p)-power puts them in (K), and Frobenius additivity gives the required scalar power. In characteristic zero, (E/K) is separable and the tensor is reduced, while (F/K) is purely inseparable and therefore (F=K); the same coefficient argument works with exponent one. This also explains why the Mathlib purely inseparable tensor-power lemma is useful downstream but does not itself state the new node.

I read `Mathlib/FieldTheory/PurelyInseparable/Basic.lean:669` and `:695`; those are the actual Loogle and grep hits for the pure-inseparability case. They assume (E/K) itself purely inseparable, so the normal fixed-field and nilpotent-lift steps above remain necessary. I tested the new statement on (E=K), on purely inseparable (E/K) (where the group is trivial), on (L=E), on a nontrivial finite Galois extension, and in characteristic zero. None requires a separability assumption to be added. The item's zero-ring/empty-product issue is excluded by nonempty field factors in the existing structure lemma; a one-factor tensor has a single branch and the same argument applies. All four non-elementary steps are under 2000 characters, and no proof was moved into the new node's statement.

The `latest` blueprint direct-image proof (3) currently does not state the historical Epp auxiliary; the item's existing provenance already records this. `tools/blueprint_refs.py ancestor` returned `None`, and searches for “normal branch”, “normal extension”, “invariant tensor”, “integral closure” and “purely inseparable” produced no blueprint node stating the new invariant-power assertion. Its provenance preserves that historical chain rather than inventing a current blueprint occurrence. The only off-unit non-leaf tool is the complete-DVR normalization theorem; its generic algebra role is declared in `split_report.tool_uses` and explained above.

Unfinished work: the new node is intentionally unsplit, as required for a one-level split. No part of the item's proof is left unexplained beyond that cited statement.
