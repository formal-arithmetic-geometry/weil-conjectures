# Stage-1 report: lem-trf-generic-principal-coordinate-dimension-drop

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-principal-coordinate-dimension-drop.json`: item split into five proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-finite-prime-transcendental-coordinate.json`: statement-only unsplit node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-dimension-neighborhood.json`: statement-only unsplit node; no Mathlib match.
- `citations.json`: verbatim quotations for every cited node at every proof step.

## Attachments

None. I searched `WeilConjectures/` in slopmaster2 and the upstream reference for the item id, its title, and the Tag 0GTG names; no exact sorry-free project declaration exists.

## WANTED

None. The item and both new nodes use sources present in `literature/stacks-project/`.

## Not duplicates

- `lem-trf-finite-prime-transcendental-coordinate` vs `lem-weil-pbc-prime-avoidance`: the new statement chooses one element whose residue-field images are simultaneously transcendental for incomparable primes; the existing Mathlib leaf only chooses an element outside a finite family of ideals.
- `lem-trf-generic-fibre-dimension-neighborhood` vs `lem-weil-pbc-fibre-dimension-neighborhood`: the new Tag 05F7 statement gives equality of all fibre dimensions on a nonempty open of an irreducible base from the generic fibre; the existing node gives a principal source localization bounding all fibres from one local dimension-at-a-point hypothesis.
- `lem-trf-generic-fibre-dimension-neighborhood` vs `lem-sbc-generic-fibre-closed-avoidance`: the former states exact generic-fibre dimension constancy (Tag 05F7), while the latter is the existing disjoint-closed-subset spreading theorem (Tag 054W), whose specialization handles empty generic fibres.

## What was checked and corrected

The item source was read in literature/stacks-project/more-morphisms.tex, Tag 0GTG, lines 8832–8871. I also read the complete source statements and proofs for the two new nodes: Tag 0GTE (lines 8566–8587) and Tag 05F7 (lines 8411–8432), and the existing Tag 054W node. The source route is the generic-point coordinate argument, openness of bounded local fibre dimension (Tag 02FZ), shrinking the complement by generic-fibre dimension, and principal-open prime avoidance.

Step 1 uses finite-type Noetherianity, finiteness of minimal primes, and the 00P1 dimension-at-a-point formula exactly for the finite list of generic fibre components. It records that every minimal component has residue-field transcendence degree below or equal to d, with equality for the selected list, and then applies the simultaneous-transcendence node. The empty selected list case remains explicit.

Step 2 now applies 00P1 to the new fibre at each generic point and cites the transcendence-degree tower node. For a selected component, the transcendental coordinate gives a one-dimensional intermediate field and hence dimension d-1. For an unselected component, the tower equality gives a value no larger than its original value, which is already below d. This removes the returned false assertion that taking a fibre is a closed condition inside the component.

Step 3 is the strict-chain argument for the reduced complement over a generic fibre. Step 4 was repaired componentwise: for each irreducible open W_i obtained by removing the other irreducible components of Spec(R), I apply the Tag 05F7 node or the Tag 054W closed-avoidance node, then take the union of the resulting opens. This gives a dense open without intersecting opens that lie on different closed components.

Step 5 was repaired by considering the top member of every irreducible closed chain in a fibre. If its generic point lies in T, the chain is bounded by the Step 4 fibre bound. If it lies in U, the existing closed-irreducible-dimension/trdeg node identifies the top member dimension with a residue-field transcendence degree, and 00P1 bounds that degree by the local fibre dimension, at most d-1. This avoids the invalid separate-dimension bound for a union of an open and a closed part. Prime avoidance and localization are unchanged.

## Review by N7

I read the target node, the sk-i-curve-zero unit, the sec-trace-formula chapter, the returned review, and every cited node statement. The two new statements remain strictly smaller than the item and are unchanged. I checked the exact hypotheses of the repaired steps: selected minimal primes are pairwise incomparable; all generic points are treated by the 00P1 and tower calculation; each W_i is a nonempty irreducible open with its own generic point; the empty generic-fibre case uses closed avoidance on that component; and every fibre chain is bounded through its top generic point. I corrected the four returned faults, updated proof_deps, added the four exact citation quotes to citations.json, and verified the existing sources and search log before rerunning delivery checks.
