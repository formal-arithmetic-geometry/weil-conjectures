# Stage-1 report: lem-sfb-qlbar-tail-module-colimit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qlbar-tail-module-colimit.json: existing statement, now split; no Mathlib match.
- citations.json: one verbatim statement excerpt for each step/node citation.
- report.md: this report.

There are 0 new nodes and 0 Mathlib leaves. Searches are recorded in searches.jsonl and appended to the inherited mathlib_searches, preserving the earlier recorded searches. The sandbox initially contained no item, split or report.

## Attachments

None. Searched the live lean/WeilConjectures tree for the blueprint id, qlbar, padicSubfield, padicAlgCl and colimit. AlgebraicGeometry.ProEtale.isColimitPadicAlgClRingObjCocone, Compatibility.lean:128, gives the all-finite-subfields colimit in abelian sheaves. It gives neither the restricted indexing category nor the module-sheaf cocone required here, so it is not an exact attachment. The flatness instance following it also does not state this item.

The Mathlib search hits were read: PadicAlgCl and its isAlgebraic instance concern the field; the SheafOfModules colimit instances concern existence; isColimitFreeCofan and Presentation.isColimit concern free presentations. None identifies the actual coefficient cocone. A second LeanFinder phrasing returned field embedding filtrations, also no match. There was no unavailable service.

## WANTED

None.

## Corrections and route

The statement is unchanged. The extracted item really needs two comparisons omitted in the blueprint's first sentence. The split now proves that a cocone on fields containing E extends to every finite subfield H by the actual compositum EH, with the formula t_(EH) a_(H,EH). It checks compatibility, existence and uniqueness rather than referring vaguely to cofinality. It then uses the existing lem-sfb-directed-ring-sheaf-module-colimit. This is a generic same-unit lemma, not a new version of the item.

The chapter and unit were read. This realizes only the first sentence of lem-sfb-qlbar-flat.proof.md and leaves the prescribed coefficient-change route intact. The coefficient universe contains the site skeleton and the entire finite-subfield set. No arbitrary scheme is assumed quasi-compact, and no claim is made that pro-etale section evaluation preserves filtered colimits. No topology on the entire space of continuous Omega-valued functions is substituted for the finite-image-field condensed coefficient definition.

Generic tool uses declared in split_report are det-def-sfb-qlbar-condensed-subextensions (finite composita) and sk-prop-sfb-qlbar-colimit-x (the precise coefficient-ring colimit cited by the blueprint). Neither imports a different proof route.

## Not duplicates

No new nodes. The whole-DAG searches for filtered colimits, underlying module colimits and cofinality located lem-sfb-directed-ring-sheaf-module-colimit; its statement was read and reused. Blueprint searches for colimit and finite subextension found sk-prop-sfb-qlbar-colimit-x, which is a ring-sheaf colimit over all finite subfields, not the tail module statement. No blueprint node states the whole item in another form, so same_as is empty. The ancestor command confirms lem-sfb-qlbar-flat.

## Review by Q15

I read the item's source, the first sentence of the current main-20261015 lem-sfb-qlbar-flat.proof.md, the unit's compatibility statement and steps, the fixed chapter route, and the current blueprint statement sk-prop-sfb-qlbar-colimit-x. For the general module comparison I read the complete existing node lem-sfb-directed-ring-sheaf-module-colimit and Stacks sites-modules.tex, Tag 03DB, label lemma-limits-colimits, including its proof. There is no newly created node requiring another source audit. The proof is marked agent-written because the explicit tail-cocone argument expands the blueprint sentence.

Step 1 takes finite compositum closure from the actual statement of det-def-sfb-qlbar-condensed-subextensions. It does not derive finite compositum closure from a mere definition. The supplied E is itself a finite field, FG contains E when both factors do, and EH contains both E and H. This establishes the directed tail and the ability to extend a tail cocone. Smallness follows from the explicitly given set/universe hypotheses, not from a large category of all extensions.

Step 2 uses the statement of def-sfb-subfield-coefficient-map for the actual inclusion maps, sk-def-sfb-pulled-back-coefficients for functoriality, and the exact equation in lem-sfb-subfield-coefficient-map-comp for q_K a_(H,K)=q_H. Those nodes were opened and read; their statements, not their proofs, supply these facts. The internal/sectionwise equivalence explicitly reconstructs the section rings and keeps the underlying sheaves identical. Applying multiplication to s_F(r)x proves the required R-linearity in two displayed formulas. No exactness or colimit preservation is inferred from this equivalence definition.

Step 3 uses precisely the last clause of sk-prop-sfb-qlbar-colimit-x, whose statement says canonical isomorphisms of ring sheaves and explicitly specifies transitions through the inclusions into Omega. The rings of integers and uniformizers in its setup are the standard ones for finite p-adic extensions; its last clause depends only on the given finite subfields and is valid for every scheme. All scalar inclusions in its diagram are the same ones used in step 2. The tail argument is elementary universal-property bookkeeping: EH is an actual finite compositum, EF=F when E is contained in F, and H contained in K implies EH contained in EK. Writing the extension formula and both uniqueness directions avoids citing an unproved cofinality theorem. The definition of category colimit states exactly the existence/uniqueness property used. This step is under 1000 characters and contains no hidden comparison lemma.

Step 4 invokes the existing directed-ring-sheaf-module comparison, whose statement explicitly requires and returns the same q_i. Every hypothesis has now been checked: essentially coefficient-small site, small nonempty directed index, unital commutative ring maps, compatibility a_(F,G) s_F=s_G and q_F s_F=q_E, and a colimiting ring cocone. Its conclusion is exactly a module-sheaf colimit with these legs. I did not cite a definition for this substantive theorem or substitute an arbitrary isomorphism for the canonical comparison.

I checked delivery-errors B through E: no statement-only node has a proof because no new node is made; no duplicate or clause restatement is introduced; all non-elementary ingredients are actual cited statements; the only off-unit statements are declared generic tools. The cited dependency closures do not contain the item. No source or statement dispute was found. For edge cases E=Q_l the tail is the whole index; F=E gives identity scalar maps; coinciding F and G gives FG=F; l=2 is allowed; and for the empty scheme the same cocone universal properties apply without any geometric nonemptiness assumption. No argument uses E as a terminal finite subfield or Omega as a finite index. Every proof step is shorter than 2000 characters. The theorem, all statement dependencies, inherited import metadata and existing citations have been preserved.

## Unfinished work

None within this one-level stage-1 split. The generic dependencies keep their live statuses; this delivery does not claim to prove them in Lean.
