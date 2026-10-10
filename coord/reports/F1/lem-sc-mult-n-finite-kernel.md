Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-finite-kernel.json`: statement split, three proof steps, Mathlib searches recorded.
- `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-locally-quasi-finite.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every step citation.

Attachments:

- `AlgebraicGeometry.isMonHom_npow_id` belongs to existing node `lem-sc-mult-n-homomorphism`.

WANTED:

- None.

What was checked and changed:

- The source item and unit were read from the master blueprint and compared with `WeilConjectures/AlgebraicGeometry/AbelianVariety/Isogeny.lean`. The existing `isFinite_npow_id` declaration is not attachable because its transitive audit rests on sorry declarations.
- The algebraically closed locally-quasi-finite argument is a genuine intermediate theorem, so it was made a new statement-only node. Its source is the unit's algebraically closed fibre paragraph, and its Lean declaration and open dependencies were recorded in `lean_audit.slopmaster2`.
- Step 1 uses exactly the commutativity and homomorphism statements cited. Step 2 uses projectivity/ample data, the pullback formula, the new algebraically closed result, and the existing proper-plus-quasi-finite finiteness statement. Step 3 uses the definition of multiplication to identify the kernel fibre; the pullback finiteness argument is written explicitly.
- I searched the whole DAG and blueprint for duplicates and searched Mathlib with LeanFinder, Loogle, grep, and LeanSearch for both the item and new node. LeanSearch was unavailable and Loogle rejected the patterns; those results are recorded as unavailable.
- Small edge checks: the positivity hypothesis is represented by `n >= 1`, so the zero map is excluded; the kernel is taken over the unit section, not an arbitrary point.

## Review by F1

I read the unit record, the imported item, the exact Lean theorem and docstring, and each cited DAG statement. The homomorphism statement supplies only the homomorphism claim; the projectivity, symmetric ample tensor, and pullback nodes supply the line-bundle inputs; the new node supplies local quasi-finiteness over the algebraic closure; and the proper quasi-finite corollary supplies finiteness. The kernel step uses the stated fibre interpretation and base-change stability of finite morphisms. I corrected the imported two-paragraph proof into explicit route steps, replaced its use of the broader finite-with-finite-fibres theorem by the existing proper-quasi-finite corollary, and recorded all quotes in `citations.json`.

What could not be finished: no Lean compilation is performed at stage 1, and the new theorem remains statement-only for the later queue.

## Not duplicates

lem-sc-mult-n-locally-quasi-finite vs lem-sc-mult-n-finite-kernel: the new node is only the algebraically closed local quasi-finiteness intermediate; the existing item asserts finiteness over an arbitrary field and finiteness of the kernel.
lem-sc-mult-n-locally-quasi-finite vs lem-sc-divisible-group-structure: the new node concerns local quasi-finiteness of the morphism; the existing node concerns divisibility and group structure on points.
lem-sc-mult-n-locally-quasi-finite vs lem-sc-mult-n-isogeny: the new node proves local quasi-finiteness over an algebraically closed field; the existing node concerns the isogeny conclusion and surjectivity.
lem-sc-mult-n-locally-quasi-finite vs lem-sc-mult-n-finite-flat: the new node proves local quasi-finiteness only; the existing node asserts finite flatness.
lem-sc-mult-n-locally-quasi-finite vs lem-sc-isogeny-surjective: the new node is a local finiteness property; the existing node is surjectivity of an isogeny.
lem-sc-mult-n-locally-quasi-finite vs lem-sc-isogeny-facts: the new node is the algebraically closed local quasi-finiteness sublemma; the existing node packages stronger finite-flat-surjective isogeny and degree facts.

## Second reading by F1

- Item statement: checked against the unit blueprint and Stacks Tags 03RP, 0BFG, 04KV, and 02OG; the hypotheses (A/k) and (n\geq1), finite homomorphism conclusion, and finite kernel agree.
- Step 1: checked against `def-sc-mult-n`, `lem-sc-av-commutative`, and `lem-sc-mult-n-homomorphism`; the cited statements provide the multiplication map, commutativity, and homomorphism claim.
- Step 2: checked against the algebraically closed reduction in Tags 03RP and 0BFG and the proper quasi-finite implication in Tag 02OG; added the abelian-variety definition citation for properness and separatedness, and wrote the fibre descent argument explicitly.
- Step 3: checked against the kernel fibre clause in Tag 03RP and the existing kernel-subgroup statement; added the kernel citation and made the pullback-finiteness inference explicit as an elementary stability fact.
- New node `lem-sc-mult-n-locally-quasi-finite`: checked against the algebraically closed paragraph of Tags 03RP and 0BFG; statement is self-contained, uses (n\geq1), and is not a duplicate of the finite-kernel item or isogeny nodes. Its recorded Mathlib searches were rerun and retained.

Changes made: added `def-sc-abelian-variety` and `lem-sc-kernel-subgroup` citations, repaired the corresponding proof dependency union and citation quotes, and expanded the reduction and kernel steps to state the omitted fibre and pullback arguments. Small cases (n=1), the zero-dimensional/empty fibre case, and the unit kernel were checked; no statement change was needed.
