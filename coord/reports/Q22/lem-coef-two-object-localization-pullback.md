# Stage-1 worker report: lem-coef-two-object-localization-pullback

## Files written

- `dag/nodes/sec-six-functors/lem-coef-two-object-localization-pullback.json`: item, split into six proof steps; original statement retained. Mathlib: no match.
- `dag/nodes/sec-six-functors/lem-coef-cofibrant-homotopy-groupoid-completion.json`: new statement-only node, unsplit; Mathlib: no match. It states the sufficient direction of Dwyer–Kan Proposition 9.5 for arbitrary small fixed object sets.
- `citations.json`: one verbatim statement quotation for every item-step citation.
- `report.md`: this report. The search command also wrote `searches.jsonl` in this sandbox.

## Attachments

None. Searches of both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the read-only master source for the exact blueprint tag and for Bergner, groupoid completion, simplicial groupoid/localization and cofibrant inversion found no declaration of this assertion. No master sorry declaration was treated as a proof.

## Literature wanted

WANTED: J. E. Bergner, *A model category structure on the category of simplicial categories*, arXiv math/0406507v2, Section 4, printed pp.13–14, especially Lemma 4.1, for lem-coef-two-object-localization-pullback. Read online at https://arxiv.org/pdf/math/0406507 on 2026-10-17; no copy is available in the read-only literature tree.

WANTED: W. G. Dwyer and D. M. Kan, *Simplicial localizations of categories*, J. Pure Appl. Algebra 17 (1980), pp.267–284, Proposition 9.5, printed p.280, with 1.4(v), 7.2 and 9.1, for lem-coef-cofibrant-homotopy-groupoid-completion. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf on 2026-10-17. The PDF text explicitly says cofibrant and gives the equivalence with the groupoid condition on pi_0. A screenshot request failed with a cache error; the source text was readable.

These are enriched homotopy-theory results, not Stacks theorems; no Stacks tag is invented. No SGA source is used. Since the external documents are not archived under literature/, the item's proof_origin is marked agent with the current blueprint proof as its document and the external reading identified here and in every step.

## Findings and changes

The imported statement was already correct; there is no STATEMENT-DISPUTED correction. The principal danger in reading Bergner is that immediately before Lemma 4.1 she suppresses the fibration replacement Z and reuses the notation F inverse F for it. Our item correctly keeps Z. The proof now transfers contractibility from the actual walking groupoid J to Z before pulling back. It never assumes the original J-to-B map is a fibration or that Z is a strict simplicial groupoid.

The other required check is that taking the homotopy-equivalence subcategory really makes pi_0 E a groupoid, even when mapping spaces are not Kan. Step 1 establishes this from the realization quotient, not from a strict inverse chosen in E'. Step 2 separately transfers invertibility along the component bijections of the cofibrant replacement.

The single new node is a local comparison for arbitrary cofibrant simplicial homotopy groupoids. It does not state contractibility, introduce F, choose a fibration replacement, or form G, so it does not restate a clause of the item. Its proof field and proof dependencies are empty; the explanatory argument remains in the item and this report.

The chapter and unit records were read and retained. The current blueprint ancestor is `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2: the displayed adjunction calculation and subsequent compatibility of finite units and counits. This split is a technical ingredient of its existing coherent finite-adjunction-diagram / simplicial-interval chain; no unit-level proof step is replaced. The ancestor and via chain in blueprint.from are preserved and extended for the new node. This item is not a statement-realization node of its unit, so no unit record is written.

## Not duplicates

lem-coef-cofibrant-homotopy-groupoid-completion vs lem-coef-cofibrant-simplicial-inversion: the existing statement gives a homotopy pushout for a cofibrant pair and a weak equivalence of derived coherent nerves under total inversion. It does not give a weak equivalence on mapping sets under the pi_0-groupoid hypothesis. This is precisely the distinction between DK 9.2 and 9.5.

lem-coef-cofibrant-homotopy-groupoid-completion vs lem-coef-free-category-groupoid-nerve: the latter concerns nerves of ordinary free categories, not mapping simplicial sets of a cofibrant simplicial category.

lem-coef-cofibrant-homotopy-groupoid-completion vs lem-coef-dk-cofibrant-localization-comparison: the latter compares a resolution-localization with hammocks for an ordinary relative category. It does not state the pi_0-groupoid comparison for an arbitrary cofibrant simplicial category.

lem-coef-cofibrant-homotopy-groupoid-completion vs lem-coef-simplicial-groupoid-models: the latter gives existence of a fibrant strict groupoid model for a space, not the canonical completion comparison for a specified A.

lem-coef-cofibrant-homotopy-groupoid-completion vs lem-coef-enriched-completion-localization: the latter changes discrete object spaces to arbitrary object spaces for enriched algebroids and is not degreewise groupoid completion.

The complete DAG was searched by statements containing groupoid completion and groupoid-completing, and by the source Proposition 9.5, before writing the new node. The whole imported blueprint was searched with blueprint_refs.py for groupoid completion, cofibrant, homotopy equivalences, cofibrant groupoid and contractible mapping. The sole unrelated contractible-mapping hit det-pe-wc-rings-retraction was opened: it concerns faithfully flat ind-etale algebras and ring retractions. No blueprint statement is the new lemma. Both same_as lists are empty.

## Review by Q22

I read Bergner Section 4 from its opening construction through Lemma 4.1, and DK I 9.1–9.6, including the stated Proposition 9.5 and its proof paragraph. The item agrees with Bergner's construction, including distinct labelled objects, no local fibrancy assumption, object-preserving replacements, and the explicit acyclic-cofibration/fibration factorization. The new node agrees with the sufficient direction of DK 9.5; its weak equivalence has exactly the mappingwise meaning defined in DK 1.4(v), rather than nerve equivalence. The sorted-algebra model node supplies the fixed-object model convention through the composition-and-units theory.

Step 1 uses only the actual quotient-topology formula from def-cbc-enhanced-diagrams-cones. A simplex lies in one path component, so the inverse-image of any subset of components is a union of entire simplex summands. Its preimage is open and closed; restricting the quotient to this saturated open subset proves the asserted subspace identification. An inverse and the paths witnessing its equations remain in the selected components. Composition and restriction are elementary from these definitions. This also accounts for vertex representatives of every component; no Kan filling is used.

Step 2 uses the statement of lem-coef-sorted-simplicial-algebra-model for the mappingwise weak-equivalence convention. Surjectivity on components gives an inverse preimage; injectivity proves each inverse equation. Naturality of the stipulated functorial replacements fixes the image of the particular arrow e. The replacement of F is assumed isomorphic to F exactly as in the item; the proof does not need an arbitrary replacement to have this property.

Step 3 uses exactly the conclusion of the new comparison node. Its hypotheses are checked in step 2: cofibrancy of tilde E and invertibility of every pi_0 arrow, with object set {x,y}. It requires neither mappingwise Kan fibrancy nor connectedness. I copied its mappingwise conclusion into citations.json.

Step 4 explicitly reduces words in the single generator and its inverse. There are four singleton hom sets in J, including the reverse hom set which was empty in F. The given weak equivalence J-to-Z gives singleton pi_0 and trivial positive homotopy groups for Z. The cited definition states weak contractibility as equivalence to Delta^0; no claim that Z is literally the walking groupoid is made.

Step 5 uses the exact right-properness sentence of lem-coef-kan-quillen-right-proper. The weak-equivalence leg is tilde E(a,b)-to-B(a,b); the fibration leg is Z(a,b)-to-B(a,b). Hence the projection G(a,b)-to-Z(a,b), not the other projection, is the weak equivalence. Component and homotopy-group bijections then prove contractibility using step 4. Every basepoint is allowed and pi_0 ensures nonemptiness. This is the non-elementary step besides step 3, and its node is cited, rather than merely the name of a proper model structure.

Step 6 is the elementary pullback construction: the two maps agree in B because p i is the functor being factored. Arrow pairs preserve composition and all simplicial operators. The first projection followed by q recovers the original map on g, so the factorization retains the specified equivalence vertex, not just its component. There is no hidden equivalence-lifting or homotopy-pullback assertion here.

For small cases I checked E' the discrete walking isomorphism (the core is unchanged), E' with additional noninvertible components (only those components are discarded), and E' with nontrivial automorphisms (the completion base need not be contractible, but J, Z and G still are mappingwise contractible). For the new node I checked empty O, identity-only categories with several objects and empty off-diagonal mapping sets, and a free simplicial resolution of a one-object group. Empty hom sets remain allowed; they are not asserted contractible by the new node. A noninvertible one-object monoid fails the groupoid hypothesis and cannot be used to infer the comparison. These checks catch both omission of cofibrancy and inadvertent connectedness assumptions.

I checked delivery-errors B–E: self-contained new statement, inline definitions of pi_0, completion and cofibrancy, correctly rendered TeX, no proof in the unsplit child, genuine searches and honest no-match verdicts, no attachment based on a partial or sorried declaration, exact citation statements, and no reliance on another node's proof. The semantic hits concern ordinary free groupoids or model homotopy categories; I read the ordinary FreeGroupoid.of/lift/localization construction in Mathlib/CategoryTheory/Groupoid/FreeGroupoidOfCategory.lean, lines 43–157, and the CofibrantObject.HoCat/toHoCat/weakEquivalence_toHoCat_map_iff section in ModelCategory/CofibrantObjectHomotopy.lean, lines 50–145. Neither provides the enriched local comparison. A second semantic phrasing and a fully qualified Loogle query were run; the first unqualified Loogle query reported an unknown identifier, which is preserved in its results. No search not run is recorded. The dependency added by the child points only to the item's existing foundational statement dependencies; there is no edge back to the item.

I corrected notation and expanded the union-of-components justification during self-review. No statement or source-route correction was needed. All writes are in the assigned sandbox; no Lean, compiler, Lake, live repository edits or manual git commands were used.

## Unfinished work

No part of this one-level split remains unfinished. The one new comparison lemma is deliberately unsplit, for a later item. A fresh second reader must review and deliver; this worker runs only the no-push dry run.

## Second reading by Q22

- Item statement: checked against Bergner, Section 4, Lemma 4.1 and the construction preceding Lemma 4.2 (printed pp. 13–14); the two labelled objects, prescribed equivalence vertex, cofibrant replacements, completion factorization, pullback, labelled factorization, and all four mapping-space conclusions agree hypothesis by hypothesis.
- New node `lem-coef-cofibrant-homotopy-groupoid-completion`: checked against Dwyer–Kan Proposition 9.5 (printed p. 280), together with 1.4(v), 7.2 and 9.1; cofibrancy, fixed object set, invertibility in realized $π_0$, degreewise groupoid completion, and mappingwise weak equivalence are all stated explicitly, including empty and disconnected mapping sets.
- Step 1: checked the realization quotient and component restriction against `def-cbc-enhanced-diagrams-cones`; the selected simplices are closed under operators and composition, and the quotient-subspace argument supplies the claimed realized subspace. Verdict: elementary and correctly cited.
- Step 2: checked the component bijections and functorial replacement argument against `lem-coef-sorted-simplicial-algebra-model`; inverse components and both equations follow by injectivity. Verdict: elementary and correctly cited.
- Step 3: checked that its hypotheses are exactly the new node's cofibrancy and groupoid hypotheses and that its conclusion is mappingwise. Verdict: correctly cited, non-elementary.
- Step 4: checked the four arrows of the walking groupoid in every simplicial degree and the weak-equivalence invariants against `def-cbc-enhanced-diagrams-cones`. Verdict: elementary and complete.
- Step 5: checked the pullback orientation against `lem-coef-kan-quillen-right-proper`; the projection to $Z$ is the pullback of the weak-equivalence leg along the Kan fibration. Verdict: correctly cited, non-elementary.
- Step 6: checked the coordinatewise pullback map, composition, labels, and recovery of the prescribed arrow directly from the definitions. Verdict: elementary.
- Small cases: checked the discrete walking isomorphism, extra non-invertible components, nontrivial automorphisms, empty off-diagonal mapping sets, identity-only multi-object categories, and a one-object free simplicial resolution; no omitted nonemptiness, connectedness, or Kan hypothesis was found.
- New-node form: statement-only, self-contained, TeX escaped once, source and definition dependencies present, blueprint ancestry present, and the recorded grep/LeanSearch/LeanFinder/Loogle searches are genuine no-match searches. No duplicate DAG node or usable Mathlib declaration was found.
- Changes made: none to the mathematical statement or proof route; this second-reading record confirms the worker text and leaves the unsplit comparison lemma for its later item.
