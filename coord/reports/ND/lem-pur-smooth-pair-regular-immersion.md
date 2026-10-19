1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-smooth-pair-regular-immersion.json` — existing statement node, repaired proof split; zero new nodes and zero new Mathlib leaves.
- `citations.json` — verbatim statement quotes for all 26 proof citations.

2. Attachments: none. The search under `WeilConjectures/` for the blueprint tag and for smooth regular immersions found no declaration giving the complete item. The item's stage-2 Lean record is preserved.

3. WANTED: none.

4. The returned version hid the successive fibre-Cartier induction, localization identifications and preservation of base flatness in its 2,571-character step 6. The interrupted repair had shortened this into three steps but still carried the localization-flatness argument inline. I retained its valid algebraic fibre-Cartier citation and added the existing nodes that state the other substantial facts. The statement, Lean record, original steps 1–5, and final regular-sequence conclusion remain unchanged. The proposed helper `lem-pur-fibre-regular-sequence-flat-lift` had already been removed in the preserved sandbox; it is unnecessary because the one-equation criterion and the localization facts already exist. Its searches remain in `searches.jsonl` and were read rather than repeated.

5. What I could not finish: none.

## Repair of returned step 6

The replacement steps follow the same Tag 063W iteration of Tag 062Y(3). They cite existing nodes for the hidden arguments, as the return permits:

- The fibre-Cartier lifting is supplied by `lem-pc-algebra-fibre-cartier-local`, the algebraic form of the original scheme criterion.
- Identification of a prefix's fibre uses `lem-weil-pbc-tensor-quotient-base-change`. The remaining tensor reassociation is the ordinary balancing identification, with the maps on pure tensors written in the step.
- Identification of ambient-localized prefix quotients uses `lem-weil-pbc-localization-quotient-commute`. Identification of their fibres after restriction uses `lem-weil-pbc-localization-tensor-over-base`; exact localization preserves the multiplication injections.
- Preservation of flatness over the original base uses `lem-pc-affine-flat-module-localization-preserves-flatness`, with algebra $R\to B_j$, module $B_j$, and the powers of the localizing element. This fact is now cited, rather than proved by an inline tensor-localization argument.
- The presentation of a principal localization uses `lem-weil-pbc-localization-away-polynomial-quotient`. Adding the finitely many prefix equations to a finite polynomial presentation then explicitly proves finite presentation.

The specified-generator argument is the elementary cancellation $v=tf$, $fz=0\Rightarrow vz=0\Rightarrow z=0$. The retained-point argument writes the further denominator as $c/h^n$, so the composite principal open is $D(hc)$ and still contains the prime. Neither needs a duplicate lemma. All ten proof steps are below 2,000 characters; the largest is the unchanged step 4 at 1,537 characters.

## Review by ND

I read the item against Stacks `divisors.tex`, Tag 067U (`lemma-immersion-smooth-into-smooth-regular-immersion`), the affine argument in Tag 063W (`lemma-fibre-quasi-regular`), and the statement and proof of Tag 062Y (`lemma-fibre-Cartier`). I also read `more-morphisms.tex`, Tag 0FUE (`lemma-etale-local-structure`), whose first proof paragraph uses exactly these regular equations. The present blueprint's divisor-class proof presupposes local frames; this input remains on the original regular-equation route and does not use purity or any SGA source. No new node requires an additional source or Mathlib search.

For steps 1–5 I opened each cited node and read its statement. The affine smoothness comparison gives the two smooth ring maps, their definition gives finite presentation, and smooth flatness supplies both base-flat algebras. The two finite-presentation nodes make the immersion ideal finitely generated without a Noetherian base assumption. Smooth-fibre regularity applies separately to the ambient and quotient local rings, and the two regular-local parameter nodes give a regular generating tuple for the fibre ideal. The flat-quotient tensor lemma, exact localization and Nakayama apply to the finite ideal module and give generation near the chosen point. The finite-type field-algebra node supplies Noetherianity only on the fibre, exactly where the principal-neighbourhood regular-sequence lemma needs it.

In step 6, the statements of the quotient-localization and tensor-localization nodes identify the actual localized prefix quotients and their fibres, so exact localization preserves their multiplication injections. The induction starts from steps 1–5; the prime of every prefix exists because every equation vanishes at the retained point. Step 7 uses the quotient base-change node for the fibre identification. I read the full statement of `lem-pc-algebra-fibre-cartier-local` and its project declaration in `WeilConjectures/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:981`: it requires a flat finitely presented algebra, a principal ideal, the correct contracted prime, and the Cartier condition at every fibre prime. The induction supplies flatness and finite presentation; the field is exactly the residue field of that contraction; the next fibre equation is a nonzerodivisor on the entire fibre, so the last hypothesis holds with $g_P=1$. The conclusion supplies both regular principality and quotient flatness; quotient flatness is not assumed.

In step 8 the quotient-localization node says exactly that lifting the localizing element from $B_e$ to $A$ gives the required ambient prefix quotient. The base-flat module localization node applies to every earlier $B_j$ without any Noetherian or finite-module hypothesis. Its use is a generic commutative-algebra tool, not a replacement of the unit route, and is declared in the split report. Step 9 cites the one-variable, one-relation localization presentation and then explicitly adds the finite prefix equations; the product of denominators avoids the chosen prime. Step 10 uses only the affine closed-immersion description and the regular-sequence definition: the final quotient contains $y$, so it is nonzero.

I checked the edge cases $b=0$, $Y=X$, an open-and-closed component, the empty closed subscheme (the assertion is vacuous), and zero sections over non-Noetherian or nonreduced bases. No regularity or Noetherianity of the base is used. The statement and Lean record are unchanged. Every citation in the repaired proof has a verbatim quote from its statement in `citations.json`; all non-elementary lifting and localization facts now have citations. The DAG and blueprint searches found the existing nodes used above, so creating new copies would have violated the duplicate rule.
