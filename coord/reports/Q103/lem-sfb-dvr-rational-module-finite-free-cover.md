## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-rational-module-finite-free-cover.json`: statement item, unchanged statement, split in six steps; no Mathlib match for the item.
- `citations.json`: one verbatim statement quotation for every citation in each numbered step.
- `report.md`: this report. Search log retained in `searches.jsonl`; `write_split.py` is sandbox-only preparation material, not a delivered DAG file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the live project `lean/WeilConjectures/` for the exact blueprint tag and finite-free-cover / rational-module / comodule terminology. The general-linear Representation.lean file defines finite-dimensional representations over fields and contains no DVR equivariant finite-free-cover theorem. Ordinary finite module presentations and abstract-group representations do not attach this rational group-scheme statement.

## WANTED

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, Definition 9.2.2 and Remarks 9.2.3--9.2.4(i), printed p.521, for this item; nominal local path `literature/alper-adequate-moduli-spaces.pdf` is absent. Read online at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf.

WANTED: J. S. Milne, Basic Theory of Affine Group Schemes (2012), VIII Examples 4.2(a), Aside 4.7, section 5, and Aside 9.4, printed pp.114,117,125--126, for this item and its existing coalgebra tools; nominal local path `literature/milne-basic-affine-group-schemes.pdf` is absent. Read online at https://www.jmilne.org/math/CourseNotes/AGS.pdf.

## Corrections and scope

No statement correction or dispute. Alper's affine-base resolution-property assertion covers this item, including torsion. Applying the existing finite-free lattice lemma directly to N would be invalid because that lemma assumes torsion freeness. The proof instead constructs a torsion-free comodule W surjecting onto N and applies that lemma to W. An ordinary free cover q:F→N need not carry a compatible coaction, and no such coaction or equivariant section is asserted. The cofree comodule is F tensor C, whose coaction comes only from C.

The inherited blueprint.from.node is null. `blueprint_refs.py ancestor` reports None; the long via chain ultimately passes through a non-node created.item inherited elsewhere. I retained that maintainer-owned provenance and the exact inherited from.place. The current `literature/blueprint/latest/` is the main-20261024 snapshot; I read the current thm-sf-ctf-stability proof and the chapter and unit records. The ancestor's algebraic supporting route remains the one already recorded. Searches of the whole blueprint for resolution property, comodule, coalgebra and comodule kernel returned no blueprint duplicates. No chapter or unit file is changed.

## Search assessment

The item's inherited searches are retained. All additional searches in the node were actually run through msearch.py and recorded in searches.jsonl, including a second semantic phrasing and both natural-language services. Read hits included ordinary module presentations and FDRep / Rep facts for abstract groups, which do not give rational group-scheme covers. A more general search found CategoryTheory.Comonad.forgetCreatesLimit and Module.Flat.iff_preservesFiniteLimits_tensorLeft. I read Monad/Limits.lean:574--588 and Flat/CategoryTheory.lean:73--91: these give a categorical finite-limit tool after constructing the tensor comonad, not the item's finite-free quotient conclusion. The final proof uses the already available flat tensor exactness and stable-core statements instead. No new node is needed for that general pullback/kernel step: the calculation is written explicitly.

## Not duplicates

No new nodes are introduced, so there are no new/existing node pairs to justify. Existing `lem-sfb-dvr-comodule-finite-free-lattice` is for torsion-free ambient comodules and submodules, whereas the item permits torsion and asks for a quotient. Existing `lem-sfb-groupoid-module-limits-colimits` describes sheaf linearizations; I did not cite it for an unproved ring-level dictionary. Existing `lem-sfb-flat-coalgebra-subcomodule-core` supplies exactly the restricted coaction used in step 3. The field-only coordinate-Hopf lemma was not applied over a DVR.

## Review by Q103

I read Alper's actual Definition 9.2.2 and Remarks 9.2.3 and 9.2.4(i): finite type equivariant modules admit finite rank locally free covers over the regular one-dimensional base, with an affine-base finite-free formulation. This confirms the unmodified conclusion and the absence of smoothness or reductivity assumptions. I read Milne VIII Examples 4.2(a) (cofree comodules), Aside 4.7 (stable core and finite generation) and section 5 (category of comodules over a flat coalgebra). The source does not print this particular pullback assembly, so proof_origin.by is agent, explicitly. It follows the existing DVR finite-subcomodule route without importing the resolution property itself as a new restatement. I read Stacks morphisms.tex Tag 01U5 / lemma-flat-characterize and algebra.tex Tags 00HB / definition-flat and 00HD / lemma-flat, and verified tag-label mappings. No SGA source or route is used.

For step 1 I opened the statements of lem-weil-pbc-flat-morphism-affine-criterion, def-sc-discrete-valuation-ring and def-weil-pbc-flat-ring-map. The first applies to the whole source and target because H is affine over the affine base; it supplies exactly flatness of C as an A-module. The DVR definition supplies the domain hypothesis for multiplication by a nonzero scalar on A, and the flatness definition supplies injectivity after tensor, proving C torsion free. I did not substitute the field-only Hopf node: the coalgebra maps and identities are already objects and hypotheses of the item.

For step 2 I opened def-weil-pbc-module-tensor-product and used its bilinear universal property, generation by pure tensors and composition law. The chosen ordinary map q from A^r is surjective because the n_i span. The cofree coaction identities are precisely those of Delta and epsilon; q tensor identity commutes with these, and rho_N is a comodule map to its cofree comodule by the given coassociativity identity. Thus f on N direct-sum (F tensor C) is equivariant. The componentwise direct-sum tensor identification is written by its two inverse formulas, not taken from an uncited categorical equivalence.

For step 3 I opened both lem-weil-pbc-flat-tensor-exact and lem-sfb-flat-coalgebra-subcomodule-core. The former explicitly includes 0→W→T→D without requiring T→D surjective, so it applies to f with W=ker f. Equivariance makes the coaction of W land in ker(f tensor 1), exactly the image of W tensor C. The stable-core node defines W-circle by that membership, proves W-circle contained in W and supplies the full restricted coaction and identities. Hence W-circle=W and its coaction is exactly what is needed, rather than a fact extracted from that node's proof. Projection equivariance follows by composing the defining inclusion equation with projections. This is a short kernel argument, not a new hidden theorem.

For step 4 I checked the pure-tensor lifting formula against the tensor definition: q surjective allows a preimage for each of finitely many tensor coefficients, without flatness of N. The counit identity makes rho_N injective, so projection c has zero kernel. Neither projection is assumed an isomorphism. For step 5 the explicit basis-coordinate isomorphism F tensor C≅C^r and coordinatewise torsion-freeness are elementary consequences of the cited tensor definition and step 1. Injectivity of c transfers torsion-freeness to W; no finite generation of W is needed.

For step 6 I opened the complete statement of lem-sfb-dvr-comodule-finite-free-lattice. Its required inputs are a DVR A, a flat coalgebra C and a torsion-free comodule W, all available, with no smoothness or finite presentation requirement on C. It gives not just a finite free underlying module but its coaction and equivariant inclusion. Its finite subset is a chosen set of lifts of the specified n_i; thus composing inclusion with a gives a map whose image contains every generator of N. Composition of the two displayed coaction equations gives the demanded equation for p. Every citation has an actual verbatim supporting quote in citations.json.

I tested N=0 (empty basis), the trivial coalgebra C=A (W identifies with F via counitality), a torsion trivial module N=A/(uniformizer) (the trivial-group construction again gives W=F), and finite constant groups (cofree module has finitely many regular coordinates). No torsion-freeness of N is smuggled in; flatness of C is used precisely for torsion-freeness and the kernel-tensor calculation. The proof works for disconnected and nonsmooth H, since only its flat coordinate coalgebra is used. All steps are under 2000 characters. I checked delivery-errors B--E: no new standalone statements, no duplicate or clause-restating nodes, no uncited substantive step, no false specialization of a field lemma, no shifted hypotheses and no cycle through the cited existing lattice/core nodes.

## Unfinished work

None in the one-level stage-1 split. Proofs of existing downstream nodes remain their own items. Direct delivery follows the required dry run.
