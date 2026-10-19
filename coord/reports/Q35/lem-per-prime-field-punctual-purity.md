# Stage 1 report: lem-per-prime-field-punctual-purity

1. Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-prime-field-punctual-purity.json` (statement node, split, no new nodes); `citations.json` (empty because the proof uses no DAG node); this report.
2. Attachments: none.
3. WANTED: none.
4. The imported item was unsplit. I did not change its statement. I checked the source PDF `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Expose XVI, Definitions 3.2.1–3.2.2 and Proposition 3.2.5 (printed pp.244–245), including the displayed Kummer/Gysin formulation and the assertion for a prime field. The source says that a regular scheme which is a scheme over a prime field is punctually pure, with no finite-type or excellence condition. The item adds Noetherianity and the explicit local notation, which only specializes the source statement. I also read the existing node `lem-per-regular-immersion-class-calculus`; it supplies the Kummer fundamental class used in the item's definition, but the proof of Proposition 3.2.5 is the cited source theorem itself, so citing another DAG node would either be circular or prove a different assertion. I searched the whole DAG and blueprint for the proposition and for a distinct prime-field purity theorem; no non-circular existing node states it. The existing Q45 trait-test node depends on this item and therefore cannot be cited here.
5. What I could not finish: nothing.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q35

I read the item source and the two preceding definitions in ILO. Definition 3.2.1 defines punctual purity at a closed point by the fundamental class map, and Definition 3.2.2 globalizes this to all points. Proposition 3.2.5 then states exactly the prime-field implication used by the item. The item uses ordinary finite étale coefficients A=F_ell with ell invertible, and its local scheme W_w, residue field, dimension, and Kummer class are the explicit notation for those definitions. The arbitrary point w is the only quantifier introduced in the proof step; applying the proposition to the local scheme gives the displayed isomorphism, and quantifying over w gives punctual purity. No hypothesis about finite type, excellence, or a chosen presentation is used. I checked the edge cases dim O_{W,w}=0 and W=Spec k: the map is the identity in the zero-codimension case, as required. The proof has no DAG citations, so citations.json is correctly empty.
