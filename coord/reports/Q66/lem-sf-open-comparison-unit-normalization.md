# Stage-1 delivery: lem-sf-open-comparison-unit-normalization

## Files written
- dag/nodes/sec-smooth-purity/lem-sf-open-comparison-unit-normalization.json: statement item, now split in seven steps; site-specific statement is not a Mathlib leaf.
- citations.json: verbatim cited statements, one entry for every step/node pair.
- report.md and searches.jsonl: review and actual logged searches.
No new nodes and no new Mathlib leaves. The inherited searches remain intact, with Q66 searches appended.

## Attachments
None. I searched slopmaster2 WeilConjectures by the exact blueprint id and by extension-by-zero, lowerShriek and comparison terminology, and inspected the pro-etale LowerShriek/Comparison file. Its maps compare lower shriek to lower star on one site, not etale and pro-etale open extension; they do not state this item. The item has no own Lean audit. Upstream master was treated as reference only, never as proof evidence.

## WANTED
None.

## Problems found and changes
The item was statement-only. Its statement, finite discrete constant-ring domain, statement dependencies, creation history and blueprint ancestry are unchanged. The source of the canonical comparison is Stacks 09AF; the unit equation is an agent refinement, not a sentence asserted by that tag. In particular, I did not take the unit formula from the proof of the existing comparison node. I construct the same canonical map through its common right adjoint and calculate its Hom transposes. The additional compatibility with the specified pullback comparison is proved using the direct-image square; it is not inferred from existence of an isomorphism.

## Unfinished work
None for this one-level split. No Lean was written, and no compiler or build tool was run.

## Not duplicates
No new nodes. Blueprint searches for the common right adjoint, comparison pullback, extension zero and adjunction units did not find another blueprint node stating both clauses. Existing lem-cbc-proetale-extension-zero-comparison gives the canonical isomorphism and composition law, but its statement omits both the Hom characterization and the open-unit equation. Existing lem-weil-pbc-conjugate-iso-unit-equation is the generic Mathlib tool and is reused rather than duplicated.

## Review by Q66
I read Stacks proetale.tex Tag 09AF (lemma-jshriek-comparison) including its common-right-adjoint proof, the comparison restriction description (099R), the open localization/extension discussion (09AE), etale-cohomology.tex extension-by-zero (03S2/03S3), and categories.tex 0B65 and 0DV0. I also read the current main-20261015 finite compact-support projection-formula proof and its unit, as well as the stored chapter/unit records and the parent node's reviewed split. This auxiliary normalization realizes the parent's final pro-etale counit computation; it replaces no unit step. Every cited node's statement was read, and citations.json quotes those statements verbatim. There are no new-node sources to audit.

Step 1 uses the etale inverse-image restriction statement, whose naturality permits the scalar-endomorphism argument, and the pro-etale weakly-etale localization statement, whose open-immersion example gives the necessary site-object hypothesis and whose clauses (2)-(3) identify the constant ring and module restriction. The comparison definition explicitly says direct image is restriction along inclusion. Evaluating on W/U gives the sectionwise identity theta, including arrows and coefficient actions. This is elementary substitution, not a conservativity claim.

Step 2 uses exactly the two existing extension-adjunction statements, the comparison adjunction in its definition, the composite-adjunction Hom and unit formulas, and the existing Mathlib conjugation leaf. Both composite left adjoints go from etale modules on U to pro-etale modules on X, and their right adjoints have the reverse type. The conjugation leaf is applied to theta inverse, in the required direction Q2 to Q1. The comparison theorem identifies the canonical open comparison; I reconstruct its normalization from the adjunctions rather than citing a formula absent from that theorem's statement. Step 3 is naturality of these already established Hom bijections: first Psi(c)=identity, then Psi(identity)=c inverse, then Psi(h)=h c inverse. No Yoneda theorem is hidden here.

Step 4 uses the two direct-image definitions to identify RX K with J RU on precisely the same fibre products. The inverse-image definitions specify the associated adjunctions. The etale restriction lemma states the restriction-unit formula, and the pro-etale localization statement identifies s with localization restriction; the unit of restriction followed by its direct image is the same section restriction from the prescribed sheaf adjunction. At W/U the fibre-product projection is an isomorphism because the inclusion is open. The composite with the etale restriction counit is therefore the identity. This establishes the formula for theta, with no base-change theorem or quasi-compactness assumption.

Step 5 uses the composite-unit definition and the conjugation leaf again, now for CU r and s CX. The specified pullback comparison comes from the direct-image identification delta on identical base-change objects. Applying r and the counit lambda gives the mixed equation after naturality and one triangle identity; the formula from step 4 identifies the other side with theta. This is the calculation that ensures a is the prescribed comparison rather than an independently chosen isomorphism. Its only generic mathematical input is already the conjugation leaf. Step 6 explicitly evaluates the Hom chain and substitutes that mixed equation; naturality of the comparison unit at the open unit gives the last equality. Step 7 applies it to h=c and compares with the transpose of identity. Steps 3, 6 and 7 use only results established earlier in this proof, so introduce no external uses.

I checked the domain of every adjunction: ordinary constant-A module sheaves, with A finite as required by the comparison and pro-etale extension definitions. An open immersion is among the localization lemma's examples; no noetherian, qcqs, boundedness, constructibility, or invertible-order condition is used. For j=identity all section identifications and comparison formulas reduce to identities under the canonical unitors. For empty U, F=0 or the zero coefficient ring all relevant maps are the unique zero maps. No statement dispute was found. The seven step texts are all below 2000 characters; each identification is calculated directly, with no new independent lemma hidden in a long step.

I checked delivery-errors B-E point by point. There are no statement-only children to hide proof in, no unintroduced new notions, no new duplicate, no clause relabelled as a child, no invented Mathlib searches, and no SGA citation. Non-elementary adjunction inputs are existing cited nodes. Elementary steps substitute explicit section formulas or use naturality and the triangle identities. Proof dependencies are the union of step uses, and no new cycle is intended. Off-unit inputs are generic site/adjunction tools declared in split_report.tool_uses for maintainer review; the projection-formula route itself is preserved.
