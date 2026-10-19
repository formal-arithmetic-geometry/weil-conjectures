# Stage 1 worker report

Files written:

- `dag/nodes/sec-smooth-base-change/lem-sbc-composite-fibre-local-models.json` — existing statement node, now split; no new Mathlib leaf.
- `citations.json` — verbatim statements for every citation in all six proof steps.

Attachments: none. No sorry-free declaration carrying this item was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or the archived upstream source.

WANTED: none.

No new nodes were created. Before retaining the imported proof I searched the whole DAG and blueprint for this statement and for each of its algebraic inputs. The existing nodes already state the composition and base-change facts for locally finite type morphisms, affine finite-type algebra charts, Noetherian finite-type algebras and localizations, affine fibre-product stalk maps, the natural fibre-ring/local-ring quotient isomorphism, local morphisms, pointwise flatness and quotient-flatness, and residue fields. Thus adding a node would duplicate an existing statement or move a clause of this item into a separate node. I changed the item status to `split`, refreshed its split report and Mathlib search records, and left its six-step proof and blueprint ancestry intact.

The item has no finished Lean attachment: the only source declaration found was the unrelated smooth base-change target in the archived master file, and no declaration tagged `(blueprint: lem-sbc-composite-fibre-local-models)` occurs in either source tree.

## Review by Q32

I read the item node, the `sec-smooth-base-change` chapter and `sk-thm-vanishing` unit, and the current `sbc-thm-universal-test-vanishing` blueprint proof. I also opened every DAG file named in the item’s proof dependencies and copied each cited statement verbatim into `citations.json`.

Step 1 uses the composition and base-change statements for locally finite type morphisms and the fibre-product definitions to obtain the three fibre morphisms and their indicated points; I checked that the hypotheses are exactly the two locally-finite-type assumptions and the residue fields of s and x. Step 2 uses the finite-type affine-pair characterization, finite-type-algebra Noetherianity, affine-stalk localization and localization-Noetherianity to produce affine finite-type neighbourhoods and Noetherian local rings; the argument does not assume that S, X, or U is globally Noetherian. Step 3 uses the affine-open basis, affine-spectrum and fibre-product affine-spectrum statements, the spectrum stalk-localization and residue-field identifications, and the existing natural fibre-ring/local-ring isomorphism; I checked that the prime contractions and the kernel p B_q match the actual fibre projection stalk map. Step 4 is the explicit double-quotient calculation using the local-homomorphism definition; it verifies m_R E is contained in m_D E and identifies the quotient with the intermediate fibre stalk. Step 5 applies the pointwise flatness definition and the cited quotient-flatness lemma with I = m_R D, checking that I E = m_R E and that only flatness at u is used. Step 6 reduces residue fields through the same quotient maps and uses the residue-field and composition definitions to verify the tower kappa(s) to kappa(x) to kappa(u). I checked the three fibre choices on affine charts, the closed-fibre edge case, and the map directions in the composite square. The only correction was procedural: the node is now marked split, its search log contains only commands actually run for this delivery, and the report/citations file documents the existing split; no mathematical statement or proof clause was changed.
