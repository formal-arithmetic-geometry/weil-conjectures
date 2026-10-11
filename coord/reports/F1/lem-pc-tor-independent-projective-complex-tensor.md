# Stage 1 report

1. Files written: `dag/nodes/sec-picard-framework/lem-pc-tor-independent-projective-complex-tensor.json` (split); `dag/nodes/sec-picard-framework/lem-pc-finite-projective-tor-acyclic.json` (statement-only unsplit child, no Mathlib match); `dag/nodes/sec-picard-framework/lem-pc-termwise-tor-acyclic-derived-tensor.json` (statement-only unsplit child, no Mathlib match).
2. Attachments: none.
3. WANTED: `literature/stacks-project/perfect.tex`, Tag 08IB, for the item and both child statements; the checkout contains no Stacks source file, so the proof follows the imported Tag 08IB route and the cited algebraic constructions.
4. No statement error was found. The prior parent split had correctly isolated this algebraic child; this split removes the remaining black-box proof content without restating the item's localization conclusion. No sorry-free slopmaster2 declaration states the item or either child.
5. Nothing remains unfinished for this split.

## Not duplicates

lem-pc-finite-projective-tor-acyclic vs lem-sc-p1-tor-free-vanishing: the existing node treats a free module over the same ring, while this child treats a finite projective module over an R-algebra A and derives Tor vanishing from Tor-independence of A and B over R.
lem-pc-termwise-tor-acyclic-derived-tensor vs lem-pc-module-bounded-flat-kflat: the existing node requires termwise R-flatness and proves K-flatness, while this child uses termwise Tor-acyclicity specifically against B and concludes that one derived tensor is computed by the ordinary tensor complex.
lem-pc-finite-projective-tor-acyclic vs lem-pc-base-change-map-cech: the existing 08IB node states a scheme-level Cech/base-change comparison, while this child is the algebraic direct-summand Tor-vanishing input for one finite projective module.
lem-pc-finite-projective-tor-acyclic vs lem-pc-tor-independent-perfect-pullback-comparison: the existing 08IB node is the stalkwise scheme conclusion for a perfect complex, while this child only proves Tor vanishing for one finite projective module over the base ring.
lem-pc-termwise-tor-acyclic-derived-tensor vs lem-pc-base-change-map-cech: the existing 08IB node compares a Cech complex under a base-change map, while this child compares derived and ordinary tensor for a bounded ring-module complex under termwise Tor acyclicity.
lem-pc-termwise-tor-acyclic-derived-tensor vs lem-pc-tor-independent-perfect-pullback-comparison: the existing 08IB node includes stalk localization and pullback geometry, while this child is the ring-level derived-to-ordinary tensor computation used before localization.

## Review by F1

I read the target node, the `sk-thm-picard-duality` unit, the `sec-picard-framework` chapter, and the neighboring Tag 08IB parent split. The target statement agrees with the Tag 08IB local affine comparison: R, A, B, E, the bounded finite-projective A-complex, localization D, Tor-independence, and the displayed cohomology map are all present. The Stacks source file is absent in this checkout, which is recorded above as WANTED.

Step 1 uses exactly the child statement that a finite projective A-module inherits Tor vanishing over R; its hypotheses specialize degreewise to Q^n. Step 2 uses exactly the termwise Tor-acyclic derived-tensor child and takes its quasi-isomorphism and cohomology consequence. Step 3 uses the existing localization exactness statement; the remaining associativity and identification of the canonical map are direct tensor calculations. I opened the cited localization node and verified that it states exactness of localization, rather than merely defining localization. The two new statements are self-contained, introduce their rings and modules, use TeX once, and are statement-only as required for unsplit children.

I searched the whole DAG and blueprint for Tor-acyclic finite projectives and termwise derived-tensor comparisons; no duplicate or more general existing node stated either child. Mathlib searches were run for each child with LeanFinder, Loogle, and Mathlib grep; only generic Tor/projective declarations appeared, with no matching theorem. Small cases checked: P=0 and Q^bullet=0 give zero on both sides; B=A with the identity R-algebra gives the ordinary localization comparison; D=E reduces to the derived-to-ordinary comparison.

## Second reading by F1

- Item statement: checked the ring hypotheses, Tor-independence, bounded finite-projective complex, localization, and cohomology map against the Tag 08IB route; verdict: mathematically aligned.
- Item Step 1: checked the finite-projective direct-summand specialization and the child statement; verdict: dependency says exactly the required Tor vanishing.
- Item Step 2: checked the termwise Tor-acyclic derived-to-ordinary comparison; verdict: dependency says the quasi-isomorphism and cohomology consequence.
- Item Step 3: checked localization exactness, tensor associativity, and the identification of the canonical map; verdict: exactness node supplies the non-elementary fact and the remaining calculation is elementary.
- New node `lem-pc-finite-projective-tor-acyclic`: checked B1-B7, including inline definition of finite projective as a direct summand of a finite free module and the Tag 08IB source; verdict: retained as a strict algebraic input.
- New node `lem-pc-termwise-tor-acyclic-derived-tensor`: checked B1-B7, including inline ring-level cochain-complex and derived-tensor meanings and the recorded LeanFinder/Loogle/grep searches; verdict: retained as a strict derived-tensor input.
- Searched the whole DAG and blueprint for duplicate Tor-acyclic-projective or termwise derived-tensor nodes; no duplicate or Mathlib exact match found.
- Changes: repaired all three statements to be self-contained at ring level, removed mismatched scheme/sheaf definition dependencies, and updated the two verbatim citation quotes to match the repaired child statements.
- Edge cases rechecked: zero projective, zero complex, identity algebra base change, and `D=E`; all give the stated isomorphisms.
