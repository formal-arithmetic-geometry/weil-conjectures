## Files written

- dag/nodes/sec-purity-real-sheaves/lem-real-boundary-path-independence.json: statement, split in five steps; no Mathlib match for the complete statement. The statement and inherited searches are preserved.
- dag/nodes/sec-purity-real-sheaves/lem-real-boundary-local-constants.json: one new statement-only node, unsplit; no Mathlib match. It asserts finite residue degree, local residue Galois surjectivity, and compatibility of the decomposition map with the arithmetic projection.
- citations.json: verbatim statement excerpts for every proof citation.
- searches.jsonl: ten actual search results, five for the local arithmetic lemma and five for the item.

No Lean files, builds, live project files, or unit records were changed. The item is not its unit's key node.

## Attachments

None. I searched WeilConjectures by the exact blueprint tag, boundaryStalk, BoundaryDatum, path independence and local residue terminology, and checked dag/lean_names_upstream.json. Boundary.lean:93-121 records an abstract boundary datum; lines 147-178 define its invariant space and prove invariance under changing a Frobenius lift. These do not compare the decomposition maps attached to two etale paths and therefore do not state this item. BoundaryInertia.lean constructs boundary data but does not supply this comparison. Master source is not used as a completed proof.

## WANTED

None: the current blueprint and the Stacks passages needed here are present.

## Corrections and source route

No statement dispute or statement correction. The item initially had no proof and no lean_audit entry. I kept all imported metadata and the existing statement. The issue to avoid is applying rho to the full arithmetic path conjugator: rho need not extend from the Weil subgroup. The source factors that conjugator into a Weil element and a local decomposition element. Step 2 gives exactly this factorization using the finite quotient Gal(k_s/k_0), the finite-quotient version of the source's assertion Z-hat = Z + e_s Z-hat. This keeps the unit's route and avoids introducing a separate profinite-integer lemma.

The new lemma isolates the non-elementary local arithmetic input, rather than moving any clause of path independence into a new node. Its future proof can combine the henselian local specialization diagram of Stacks Tag 0BSW (pione.tex, lemma-identify-inertia, lines 2825-2950) with the first exact sequence of Tag 0BUB (lemma-structure-decomposition-separable-closure, lines 3345-3367). The constants compatibility is the composite of that diagram with the structure map to Spec(k_0). Reduction is compatible with the action on finite constant fields. Closed residue fields of the curve are finite extensions of k_0. No proof sketch has been inserted into the new node's statement or proof fields.

## Searches and existing nodes

I read the chapter sec-purity-real-sheaves, unit sk-d-real-boundary, and the current main-20261015 d-real-boundary.proof.md. Blueprint ancestor is d-real-boundary. Whole-DAG searches covered decomposition, residue homomorphism, constant field, Galois surjectivity, path independence, and Stacks tags 0BSW and 0BUB. blueprint_refs.py searches for path independence, residue homomorphism, constant field, decomposition, henselian, 0BSW, and 0BUB produced no existing node stating the new arithmetic assertion. d-real-boundary and sk-d-real-boundary contain the overall definition and point to this item; neither can be cited here without circularity. The existing decomposition-landing lemma gives subgroup inclusions, not residue surjectivity or the commutative arithmetic square. The existing finite residue normal-action node concerns finite normal field extensions, not this absolute local group and its curve's constant-field projection.

I read all search hits. Mathlib RamificationGroup.lean:27-54 defines decomposition and inertia but does not state residue surjectivity or arithmetic compatibility. The source of Representation.quotientToInvariants and its lift (Invariants.lean:150-177) confirms the existing Mathlib leaf lem-real-boundary-frobenius-invariants. It is reused, not duplicated. The semantic hits for IsArithFrobAt and isConj_arithFrobAt concern ring-theoretic Frobenius at primes, not arbitrary path conjugation for a representation only defined on the Weil group. Isocrystal equivariance hits concern different objects. Every new search is recorded with the actual tool/query and its returned digest; all ten services succeeded. Both new lemma and item were searched with two natural-language phrasings, Loogle, source grep and LeanSearch.

## Not duplicates

lem-real-boundary-local-constants vs lem-exc-dvr-galois: the existing node is a cohomological-dimension and finiteness theorem over a strictly henselian DVR with algebraically closed residue field; the new node concerns the residue Galois quotient and arithmetic constants of a curve over a finite field.

lem-real-boundary-local-constants vs lem-exc-henselian-dvr-tame-sequence: the existing node describes tame inertia for algebraically closed residue field; the new node describes the entire residue Galois quotient for finite residue field and its constant-field compatibility.

lem-real-boundary-local-constants vs lem-exc-tame-root-extension: the existing node constructs finite tame Kummer extensions with algebraically closed residue field; it does not state residue Galois surjectivity or arithmetic constants compatibility.

lem-real-boundary-local-constants vs lem-exc-tame-roots-product: the existing node identifies an inverse limit of roots of unity with a product of adic integer groups; it has no decomposition map or residue Galois assertion.

## Unfinished work

None for this one-level split. The new local arithmetic node is intentionally unsplit. No new Mathlib leaves are delivered; the existing quotient-action leaf is reused.

## Review by NX

I checked the statement against the complete current blueprint proof: the coefficient field, both paths from the same local geometric point, the normal inertia kernel, and the Frobenius-equivariant conclusion are unchanged. I read the unit's full boundary-definition statement and followed its g=wd route. The source does not assume the Weil representation extends to the profinite fundamental group, and neither does this proof.

Step 1 uses the definition of a path as a natural isomorphism, the statement defining pi_1 as Aut of the fibre functor, and the exact displayed theta formula in decomposition-landing. Their statements really do give the composite g and conjugacy; substituting gamma_2=g gamma_1 is elementary. No separate change-of-path theorem is being silently invoked.

Step 2 uses local-constants for finite residue degree and for every element of Gal(k/k_s) to lift into the arithmetic image of theta_1. It uses det-base-field-cd-galois-group for the finite residue extension's cyclic Galois group; geometric Frobenius also generates because it is the inverse generator. The chosen exponent matches h only on k_s, which is all that is needed: F^{-n}h fixes k_s, a local delta lifts it, and p(g theta_1(delta)^{-1})=F^n. The definition of the Weil subgroup then places w in rho's domain. I checked that neither a surjective theta nor an extension of rho is used. The finite-field theorem is declared as a generic off-unit tool in split_report.tool_uses.

Step 3 uses exactly I_s=ker r_s and the landing assertion stated in decomposition-landing. Kernel normality follows by applying r_s to delta i delta^{-1}; conjugation is onto I_s because its inverse is conjugation by delta^{-1}. This is the elementary calculation of the conjugate image subgroup, not a hidden geometric comparison.

Step 4 uses the linear group homomorphism given by fundamental-representation and the explicit fixed-vector definition in representation-operations. I checked both directions, not only the inclusion: rho(w^{-1}) takes the second invariant space back to the first and is the inverse restriction. These are direct three-line representation calculations.

Step 5 uses the profinite cyclic absolute Galois assertion of det-base-field-cd-galois-group for abelianness of G_s, and the full statement of frobenius-invariants for equality of the two coset actions. I checked its hypotheses with G=W(K_s), N=I_s, and alpha=rho composed with theta_1: the kernel lies in that local Weil group, is normal, and both Phi and delta Phi delta^{-1} lie there with equal residue image. The displayed T_2 A calculation gives A T_1 with the correct order of composition. The proof never evaluates rho(delta) or rho(g).

For the new node I read the precise 0BSW diagram and the first 0BUB exact sequence, not the tame-inertia parts alone. The normal local ring in that diagram specializes to a smooth curve's local ring; passage to its henselization is precisely the local field K_s. The finite residue field is perfect, so its separable algebraic closure is its algebraic closure. The commutative square includes the arithmetic structure map; changing the path conjugates its image in an abelian constant-field Galois group and leaves the square unchanged. The finite-field embedding choice gives the same unique finite subfield of k. This statement is smaller than the item: it mentions no representation, invariant space, path comparison or intertwiner. Every notion is introduced or points to its existing definition; proof and proof_deps remain empty.

I tested the arguments with residue degree one and degree greater than one, with the identity path change, delta in inertia, trivial inertia, and the zero representation. Degree one allows any arithmetic residue element to be lifted; higher degree uses only reduction of the exponent modulo that degree. In the zero representation the restricted maps are still inverse linear isomorphisms. An arbitrary full conjugator cannot simply be applied under rho, which is why the factorization is retained. There are no steps over 2000 characters. All B-E checks were made with cited statements open; the citations file copies actual statement substrings and no source tag is used as an uncited black box in a proof step. I corrected the new lemma to state finite positive residue degree explicitly, so Step 2 does not hide that geometric input.


## Returned delivery repair (2026-10-18)

The return names reviewed head 3bffcbb856 and one fault: the statement of def-wf-fundamental-representation changed before landing. I retained that delivery's five-step proof, its local-constants node, the report and all ten logged searches. Comparison with the current unsplit repository item found changes only in proof, proof_deps, proof_origin, mathlib_searches, status and split_report; its statement, source, ancestry, chapter, unit and statement dependencies agree. The sandbox item now carries current repository metadata and the repaired split; deliver.py constructs the replacement commit on current origin/newtargets-dag.

I compared the old full-definition quotation retained in citations.json with the entire current definition. The revised definition uses the lisse adic category of def-pod-lisse-l-adic-sheaves, supplies a specified arithmetic-lift fibre path, defines W as the fibre product with the discrete integer group, and defines the full extension by rho(h s^n)=rho_geom(h) T_s^n. It expressly says this is a continuous representation and that later rho expressions mean this extension. The previous quotation is no longer verbatim. I replaced it with the current concluding passage, which actually supplies the full Weil representation, and made Step 4 explicit about using this homomorphism and its linear inverses.

I re-read all nine proof-dependency statements and the statement-only dependencies against the retained quotations and the five steps. Only the fundamental-representation quotation was stale; every other retained proof quotation is still verbatim in the current statement. Step 1 still has the path formula and the automorphism definition. Step 2 still has finite residue degree, the exact arithmetic image, cyclic finite-field Galois groups and the inverse-image Weil definition. Step 3 still has the kernel and subgroup landing statements. Step 4 has the full representation just checked and the explicit invariant-space formula. Step 5 has abelian residue Galois groups and equality of actions in one inertia coset. None requires an action of g or d on V. The new definition's fibre-product model agrees with the inverse-image model used here: each integral power of geometric Frobenius has a unique integer exponent, so the first projection identifies the two groups, and the representation can be evaluated on w. Its refined coefficient convention does not impose a Frobenius-stable integral lattice, and our proof uses no such lattice.

For this repair I reopened the complete current d-real-boundary.proof.md and its definition, the chapter and unit, and Stacks 0BSW (lemma-identify-inertia) and 0BUB (lemma-structure-decomposition-separable-closure) in pione.tex. The latter still give precisely the local residue surjectivity input; the constant-field compatibility remains part of the new unsplit lemma. No new mathematical assertion or new node was introduced in the repair, so the previously logged searches address unchanged questions and were read and reused. The original B-E review above still applies: the new node is statement-only and smaller than path independence, and the finite-quotient factorization and two inverse restrictions are written out. Rechecking degree one, larger residue degree, identity path change and the zero representation introduces no extra hypothesis under the revised definition. All five steps remain below 2000 characters.
