# Stage 1 report: lem-sfb-artin-pointwise-versal-field-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-artin-pointwise-versal-field-extension.json: existing statement, split; no Mathlib match.
- citations.json: verbatim statement excerpts for all three step/node citations.
- report.md and searches.jsonl: report and actual search log.

No new nodes; no Mathlib leaves added. The mathematical statement and statement dependencies are unchanged. All original fields, blueprint provenance, citations and searches were retained. Additional searches were actually executed for this item and read.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, pointwise versality, the word versal, Schlessinger and 07XG. No project declaration states this result. General occurrences of universal properties do not supply it.

## WANTED

None. The source files needed here are present.

## Corrections and observations

The item had an empty proof. Stacks artin.tex Tag 07XG (lemma-versal-change-of-field) reduces to 07WX (lemma-change-of-field) and formal-defos.tex Tag 07WD (lemma-change-of-fields-smooth). I expanded those reductions into the concrete lifting problem already stated by the item. The existing residue-restriction lemma and the existing unrestricted affine pinching pushout lemma supply the two non-elementary prerequisites. No new version of these facts is needed.

The item's square-zero hypothesis is stronger in its range of rings than Stacks' finite-type Artinian (RS) condition. It is therefore legitimate to apply it directly to all intermediate ring pullbacks. I explicitly iterate it along maximal-ideal powers, rather than silently invoking nilpotent gluing. There is no need to establish that all Artinian test algebras are finite type over R for this item, nor to assume separability. The affine pushout lemma imposes no integrality or finiteness requirement on k -> L.

Read the current latest blueprint unit and its direct-images proof. The inherited node is a generic deformation-theory prerequisite beneath the nodal-curve-stack input of the existing direct-image alteration route. The current blueprint does not itself mention 07XG or 07W8. Whole-blueprint searches for versality, 07XG and 07W8 found no imported node stating this input. The ancestor tool gives blueprint.from.node = None, which I preserved along with its inherited precise place and via chain. No chapter or unit record was edited. This is not the unit key node.

## Not duplicates

No new nodes were created. Reused lem-sfb-artinian-finite-residue-restriction and lem-sfb-affine-closed-pinching-pushout instead of duplicating them. The nearby lem-sfb-artin-versal-field-lifting has a stronger global versality hypothesis and a conclusion at every finite-type field point; it was read as context but is not cited as a replacement for this fixed-point argument. The proof here does not depend on it or on the parent lem-sfb-artin-versal-base-change-smooth. Dependency traversal of the three cited nodes found no path back to this item.

## Review by NQ

I read artin.tex definition-versal (07XF), lemma-versal-change-of-field (07XG), and the full change-of-field construction and equivalence in lemma-change-of-field (07WX). I also read formal-defos.tex situation-change-of-fields (07W8), its verification of Artinianness and preservation of surjections, and Tag 07WD (lemma-change-of-fields-smooth). For the scheme pushout I read more-morphisms.tex lemma-basic-example-pushout (0ET0). All sources respect the no-SGA route lock.

Step 1 uses exactly the statement of lem-sfb-artinian-finite-residue-restriction: C and C prime are Artinian local with residue k, and the induced map is a residue-compatible surjection. Its finite-extension hypothesis is the given finite L/k; no separability is required. The R-algebra structures are written coordinatewise, so the application of versality has the right base. The statement of lem-weil-pbc-artinian-local-noetherian-nilpotent supplies nilpotence of the maximal ideals of B and B prime. This is a Mathlib leaf already in the DAG, not a new leaf claimed here.

Step 2 uses the statement, not the proof, of lem-sfb-affine-closed-pinching-pushout. Substituting A=B, D=L, T=k is permitted since B -> L is surjective. The statement gives the pushout against every target scheme U and its uniqueness. Agreement on Spec L is a hypothesis on b. Uniqueness also proves the resulting map is over S. Its restrictions to B and k are precisely the ones needed later.

Step 3 cites no hidden deformation theorem. It proves directly from the item's gluing assumption that the restriction functor over D times_L k is an equivalence for D=B and B prime. The base r=1 is an identity; the induction fibre product is written explicitly and the square of m^r/m^(r+1) vanishes for r>=1. In the iterated groupoid fibre product, the intermediate D_r-object is identified with the restriction of the D_(r+1)-object and is eliminated; objects and compatible arrows are described. These are elementary fibre-product manipulations of the assumed equivalences, so no separate lemma merely renaming (RS) was introduced. The equivalences used later are the actual restriction functors and thus commute with q. Maximal-ideal nilpotence was already obtained in step 1.

Step 4 uses essential surjectivity and full faithfulness of precisely those restriction equivalences, with x_u and the isomorphism theta restricted to L. The compatible components over B and k determine alpha, and its B-component is specified, not left as an unspecified isomorphism. Step 5 checks all hypotheses of the assumed versality over k and writes the final isomorphism as gamma restricted to B prime composed with lambda inverse. Its restriction to B equals theta by an explicit cancellation. Thus no compatibility clause is lost in changing residue fields.

For edge cases I checked L=k, where C=B and C prime=B prime; B prime=B, where no thickening is needed; B=L, where C=k; and a purely inseparable extension such as F_p(s) inside F_p(t), s=t^p. The construction only uses that L/k has finite degree to invoke residue restriction and does not take a separable closure or lift a coefficient-field embedding. All proof steps are below 2000 characters. Every cited node statement was opened, every recorded quote was checked as a verbatim substring, and the proof-dependency list equals the union of step uses. No statement dispute was found.

Searches used LeanFinder twice with different phrasing, LeanSearch, Loogle and the required grep command. The hits are actual smooth ring/scheme morphisms, residue-field finiteness, universal Ore maps and weak limits; none gives the fibred-groupoid deformation lifting conclusion. I read the grep hits' source contexts in WeakLimits/Basic.lean and Extension/Cotangent/Basic.lean. No query that was not executed has been added to this attempt's records.

## Unfinished work

None in the split. The existing unsplit residue-restriction lemma remains a separate queue item, as required by one-level splitting. Server preflight and direct delivery follow this report.
