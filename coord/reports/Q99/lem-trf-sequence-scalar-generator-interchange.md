# Q99 stage-1 report

Item: lem-trf-sequence-scalar-generator-interchange

## Files written

- dag/nodes/sec-trace-formula/lem-trf-sequence-scalar-generator-interchange.json: existing statement, now split into eight proof steps; no Mathlib match for the complete item.
- citations.json: nineteen step/node citations, each containing a verbatim portion of the cited statement.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The existing recorded searches are retained; six new searches executed with msearch.py are appended with their actual logged summaries. Searches.jsonl is the search tool's own record.

## Attachments

None. I searched the actual project source under lean/WeilConjectures for the exact blueprint tag, sequence/scalar/interchange names, and whole-system and tensor-generator terminology. The scheme-module theorem in AlgebraicGeometry/PullbackTensorComposition.lean proves tensor compatibility of ordinary scheme pullback composition, not all three equations on the pro-etale quotient sequence site. The relevant lean/Sheaf/Paper/IntegralComparisonSequenceSystems.lean still has sorry in its comparison existence obligations; this is not an attachment. No compiler, Lake, Lean writing, or git command was run.

## WANTED

None. The required Stacks sources and current blueprint are present.

## Problems found and changes

The imported item's proof was empty. Its statement is retained verbatim: its three equations are correctly typed with the indicated source and target functors. I supplied an adjunction equality test, verified the compositor's precise mate normalization, computed the three equations, checked vertical restrictions and actual semilinear quotient transitions, and passed to arbitrary complexes degreewise. No derived comparison, realization, K-flat assertion, or faithfulness of separate derived evaluations is used.

The notation gamma_f(cb tensor x) needs its ordinary meaning: b and c inside gamma_f are coefficient sections at the source test object, transported to the pulled-back test object on the input side. One must not move an arbitrary coefficient section on X back to Y. Step 5 spells this out. Equality for arbitrary target-local sections follows from the successive Hom bijections in Step 1, which test all sections of the original source N. No statement change or added hypothesis is needed.

The source field names Stacks 0D6D as underlying pullback composition and expressly identifies the mixed calculation as agent-formulated. Accordingly proof_origin.by is agent, not document. I read the current blueprint's prop-trf-karoubi-independence.proof.md, especially its final sentence about Frobenius transport; it does not itself prove the mixed equations. The split fills this ordinary calculation below that sentence, within the existing sk-thm-trace-transport route. The chapter and unit records were read and left alone because this item is not their key statement.

## Not duplicates

No new node is proposed. I searched the full DAG for adjunction, tensor universal-property, generator-extensionality, change-of-rings, and the relevant Stacks tags; the existing def-weil-pbc-ringed-tensor-section-calculus already gives scalar extension with its right adjoint and unit formula. The existing def-weil-pbc-composite-adjunction and lem-weil-pbc-conjugate-iso-unit-equation give the composite-unit and specified mate formulas. Blueprint searches for scalar pullback, interchange, tensor-generator, tensor and adjunction gave no imported node stating this item's entire assertion. These existing generic tools are used rather than new variants.

## Review by Q99

I read coord/delivery-errors.md B through E in full and checked the split against each type of failure. There are no unsplit child statements, new definition nodes, or new Mathlib leaves to audit. All eight proof steps are under 2000 characters. The calculations remain steps, not new nodes that would merely restate clauses of the item.

For the item's sources I read sites-cohomology.tex, Tag 0D6D, lemma-derived-pullback-composition and its proof. This confirms only the underlying pullback comparison, not the three mixed equations. I also read sites-modules.tex, lemma-adjointness-tensor-restrict and its proof, Tag 03D7 lemma-adjoint-pullback-pushforward-modules and its proof, and Tag 03EK section-tensor-product including the sheafified tensor universal property. I compared these with the existing tensor section-calculus and sheafification nodes. They apply to arbitrary ring sheaves on the small sequence site; they impose no flatness on the coefficient ring map. No SGA source is used.

Step 1 cites the ringed sequence-site definition for the whole-system category, the actual comparison definition for u and its adjunction, the tensor section-calculus definition for s and its restriction-of-scalars right adjoint and unit, the composite adjunction for the composed Hom bijection, and module sheafification for uniqueness after sheafification. I opened each statement: in particular the section-calculus node explicitly says both that it has the adjunction and that its unit is 1 tensor m. This is not an appeal to a mere tensor definition for an uncited tensor exactness theorem. Equality follows by injectivity of these specified bijections, then equality of all section functions. I rejected the tempting argument that every sheaf section is a global pure tensor.

Step 2 cites the Mathlib-leaf conjugate-isomorphism unit equation and the composite adjunction, with the comparison definition identifying the exact direct-image pasting map. The cited lemma really states the unit equation, not merely existence of some left-adjoint isomorphism. Its hypotheses hold with L1 = u_kh, L2 = u_h u_k and the right adjoints in the opposite order. The pasting isomorphism is retained, so no strict equality of un-identified fiber products or right-adjoint functors is assumed. Unit naturality supplies the stated formula for a module-system morphism a.

Step 3 uses the comparison definition's explicit kappa formula and the unit equation established in Step 2. I followed each of the three left arrows and both right arrows on 1 tensor gamma_kh(x); they have the same target and both give gamma_h gamma_k(1 tensor x). Step 1 then gives equality of the whole maps. No parent mixed-coherence theorem is cited: that theorem depends on this item.

Step 4 uses exactly the definition's multiplication unitor and kappa formula. Both composites give gamma_f(x). The multiplication by 1 is valid over every quotient ring, without faithful scalar extension or division.

Step 5 uses exactly the definition's scalar associator c tensor (b tensor x) maps to c j(b) tensor x, and its kappa formula. I first checked the double-unit generator, which suffices by Step 1. I then checked the displayed coefficient formula for source coefficient sections using semilinearity and unit naturality. This avoids an implicit assertion that arbitrary X sections descend to Y. Equality and the explicit generator value are both obtained.

Step 6 cites the comparison definition's assertion that its specified maps are natural in vertical site restrictions, and the tensor calculus's pure-section restriction compatibility. I wrote the restricted common values for all three equations, using preservation of 1 and multiplication by the coefficient restriction maps. The canonical geometric pasting map is natural in the site object, as specified by its construction; no unrelated site or stronger geometric hypothesis is introduced.

Step 7 cites the sequence-site definition for the actual quotient restrictions and the comparison definition for their naturality, and uses the tensor section calculus on those restrictions. I checked c j(b) before and after every q_mn, the image of 1, and the semilinear identity t(by) = q(b)t(y) for the unitor. A general sequence-site arrow factors into horizontal and vertical parts because the underlying category is the specified product. This proves whole-system compatibility without assuming that a tensor preserves kernels, that quotient maps are flat, or that derived evaluations are faithful.

Step 8 cites the cochain-complex definition for the actual differential square. Natural transformations satisfy that square by naturality with d^i; their degreewise values are equal by the earlier steps. The functors in use preserve zero homomorphisms directly from inverse image and tensor, so they do take complexes to complexes. The proof is termwise and includes all integer degrees, hence requires no boundedness or totalization assumption.

I tested equality E = L = M, identity scheme morphisms, zero systems and zero complexes, the empty scheme, index n = 1, and a ramified coefficient extension with nonflat finite quotient maps. In each case the calculation uses only units, multiplication, and the actual quotient morphisms, and still applies. I checked that none of the additional cited tool nodes depends on the item or on its parent mixed-coherence node. The only cited statement theorem outside the item's unit is the already-Mathlib conjugate-unit lemma; other added tools are definitions, so no replacement of the unit route is proposed.

For Mathlib I ran two semantic phrasings plus LeanSearch, Loogle and source grep through the required msearch.py. I read the hits, including SheafOfModules.pullbackComp and pullback_assoc in PullbackContinuous.lean:167-210 and ModuleCat.extendScalarsId/extendScalarsComp and their unit formulas in ChangeOfRings.lean:954-1030. Those are useful general ingredients; identifying the prescribed maps and proving their mixed whole-sequence equations requires the argument above, so the entire item is not a one-line Mathlib specialization. All searches recorded as new entries actually ran and all services returned results.

## Unfinished work

None in the requested one-level split. The dry run and direct push are the final delivery steps; their outcome is reported by deliver.py.
