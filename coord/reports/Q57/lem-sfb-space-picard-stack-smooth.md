# Q57 stage-1 delivery: lem-sfb-space-picard-stack-smooth

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-picard-stack-smooth.json: item, split in seven steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-invertible-open-coherent.json: statement-only input, not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-square-zero-picard-obstruction.json: statement-only input, not in Mathlib.
- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-space-fibre-cohomology-bound.json: statement-only input, not in Mathlib.
- citations.json: verbatim statements for all 21 step/node citations.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, Picard-stack terminology, and Picard smoothness. The curve Picard group/scheme declarations are not declarations about the algebraic-space stack in this item. No exact finished project declaration was found. No Lean was written or compiled.

## WANTED

None. All sources used are present in literature/stacks-project. No SGA source is used.

## Findings and corrections

The sandbox's original item agrees with the current repository, including its statement and inherited blueprint reference. It was unsplit and contained no proof. Retained the saved searches, their exact outputs, and the inherited searches; all additional records come from searches.jsonl and search-*.txt. In particular, successful empty Loogle queries are not outages. Read both semantic phrasings for each proposed input: scheme smoothness, ring Picard groups, cotangent complexes, free loci and affine-limit sections do not supply these algebraic-space moduli/cohomology statements.

The important source gap is in moduli.tex Tag 0DPJ: it invokes spaces-cohomology.tex Tag 0A4T for an arbitrary affine first-order thickening and its arbitrary quasi-coherent ideal. The latter tag assumes a locally Noetherian target and coherent coefficients. Those hypotheses cannot be inferred from an arbitrary square-zero quotient A' -> A. For example, A'=k[x_1,x_2,...,e]/(e^2) and A=A'/(e) are permitted in the lifting test but neither is Noetherian. This does not refute the Picard-stack statement. Our Steps 3--5 supply Noetherian approximation before using the actual coherent vanishing theorem. The proof is marked agent-written because this fills a gap rather than copying the source argument uncritically.

During review I removed a draft assertion that the thickenings T_i -> T'_i form cartesian transition squares. For I_i=I intersect A'_i, extension of I_j need not equal I_i. Only the two separate inverse limits and their compatible closed immersions are used. The line-bundle descent input applies to Z_i, which does have affine transitions and limit Z. No cartesian assertion about successive thickenings is needed.

Avoided the apparently convenient lem-sfb-proper-space-curve-qcoh-bound: its proof uses lem-sfb-curve-etale-scheme-cover, then lem-sfb-curve-smooth-polarization-cover, which already uses this Picard-stack item. The Noetherian coherent higher-image input has no such dependency. Existing generic approximation and finite-type Noetherian lemmas are declared as tool uses in split_report, not as top-level approvals.

## New nodes

lem-sfb-space-invertible-open-coherent states the base-change-universal open rank-one locus inside the algebraic-space coherent stack. Read quot.tex Tag 0D03, lemma-picard-stack-open-in-coh, including its triple description and the universal open U in the proof. This is a genuine input to algebraicity, not algebraicity itself: the ambient coherent stack and open-stack algebraicity theorem are separately used. The proper flat hypotheses ensure that a line module is an eligible relatively flat finitely presented object with proper support. The saved LeanFinder, Loogle, grep and LeanSearch results give no matching theorem; Module.isOpen_freeLocus concerns a module on one affine spectrum, not the universal relative locus in all test families.

lem-sfb-space-square-zero-picard-obstruction states exactness Pic(Z') -> Pic(Z) -> H^2(Z,J) for algebraic spaces. Read spaces-more-morphisms.tex Tag 0DNM, lemma-picard-group-first-order-thickening, including its units sequence and connecting map. The ideal is explicitly square-zero, quasi-coherent, and regarded on Z by the quotient action. Cohomology here is module cohomology on the small etale site; the source's comparison with additive sheaf cohomology is part of the theorem being requested in this input, not an extra silently used theorem in the item. The saved searches return Jacobi-Zariski/cotangent sequences, derivations, ring relative Picard exactness and sheaf kernels; none proves this obstruction theorem.

lem-sfb-noetherian-space-fibre-cohomology-bound states the coherent higher-image bound for proper algebraic spaces over a locally Noetherian scheme. Read spaces-cohomology.tex Tag 0A4T, lemma-higher-direct-images-zero-above-dimension-fibre: it gives vanishing at every geometric stalk, hence the stated vanishing sheaf under the uniform bound. Kept both Noetherian and coherent hypotheses. The empty-fibre case is zero as the proper morphism has no source over the complementary neighbourhood. Saved searches find proper-scheme definitions, finite fibres and sections in affine transition limits, not the coherent higher-image bound for algebraic spaces.

## Not duplicates

lem-sfb-space-invertible-open-coherent vs lem-sfb-invertible-open-in-coherent-stack: the existing 0D03 node assumes X and S are schemes and uses Zariski modules; the new input allows a nonrepresentable algebraic-space X with small-etale modules and its general coherent stack.
lem-sfb-space-invertible-open-coherent vs lem-sfb-flat-proper-picard-algebraic-space: the latter represents the relative Picard sheaf of a scheme family under universal O -> f_*O, not the open inclusion of the unrigidified line-module stack for algebraic spaces.
lem-sfb-space-invertible-open-coherent vs lem-sfb-relative-finite-free-locus-base-change: the latter is a source locus on a scheme Y and does not give the rank-one locus in the test base of a proper algebraic-space family.
lem-sfb-space-invertible-open-coherent vs lem-sfb-relative-module-flat-locus-base-change: the latter concerns scheme module flatness loci, not the algebraic-space moduli open immersion.
lem-sfb-space-square-zero-picard-obstruction vs lem-sfb-square-zero-picard-obstruction: the existing result is for schemes and ordinary Zariski module cohomology; the new result is for algebraic spaces and small-etale module cohomology.
lem-sfb-noetherian-space-fibre-cohomology-bound vs lem-sfb-proper-space-curve-qcoh-bound: the existing node is an arbitrary-base quasi-coherent theorem restricted to flat curve families and depends transitively on the item; the new theorem is the independent Noetherian coherent bound for any dimension and needs no flatness.
lem-sfb-noetherian-space-fibre-cohomology-bound vs lem-sfb-proper-quasicoherent-fibre-dimension-vanishing: the existing theorem has scheme source and target; it cannot be specialized to nonrepresentable algebraic spaces.

Blueprint search by Picard and by the three tags found no imported blueprint node stating any new input. Whole-DAG searches by the same tags and concepts were read, including the scheme Picard-stack geometry node. That node is likewise not the present algebraic-space theorem. blueprint.from.node=None is inherited and confirmed by tools/blueprint_refs.py ancestor; kept the supplied ancestor chain and filled supporting places rather than inventing an imported ancestor. Read the current latest main-20261023-1620 chapter and unit; these lemmas support the inherited stable-curve/local-polarization prerequisite chain, and do not replace its six-functor route.

## Review by Q57

I read the sources and statements rather than accepting a tag match. In Step 1, lem-sfb-space-coherent-stack-general explicitly allows algebraic-space source and has the scheme-base local finite presentation clause; properness gives its required separatedness by lem-sfb-space-flat-proper-fp-locality. The new open-immersion input has exactly this coherent category and the same tensor-pullback arrows, so lem-sfb-open-stack-algebraic-lfp applies without extra reducedness or section hypotheses.

Step 2 uses precisely the affine-thickening lifting test in lem-sfb-stack-infinitesimal-smooth-criterion. The locality/permanence statement preserves properness, flatness and finite presentation under T' -> S. Its geometric fibres are the original fibres after the composite field point, so the object lies in the groupoid of lem-sfb-curve-limit-preservation.

Step 3 uses lemma-nagata-noetherian-inverse-system-affine for the finite-type integer subalgebras. lem-weil-pbc-finite-type-over-noetherian explicitly includes Spec Z and therefore supplies Noetherian stages. The remaining quotient-limit assertion is elementary: every class in A has a representative in some A'_i, and equality is detected in a common later subring. I_i^2=0 follows by intersection. Step 4 uses the full statement of lem-sfb-curve-limit-preservation for a flat proper finitely presented curve family at a stage, and the separate line-module descent statement of lem-sfb-space-invertible-limit-descent. Its hypotheses hold for Z_i: proper over affine implies quasi-compact and quasi-separated, affine transitions are base changes of affine maps, and their limit is Z by fibre-product universal properties. The descended family need not retain a map to S; its line bundle can still be pulled back to the given family over T'.

In Step 5, lem-sfb-space-thickening-base-change gives the thickening, and the ideal on an affine chart is I_i B', hence square-zero. Finite-type affine charts over a Noetherian stage are Noetherian by the same finite-type lemma; lem-trf-noetherian-submodule-finitely-presented explicitly says their ideals are finite. Their generators still generate over B'/I_iB' because the ideal is killed by itself. This is exactly the chartwise coherence convention of the new vanishing input. Quotients of Noetherian rings are Noetherian since their ideals correspond to ideals upstairs, so the target T_i meets that input's hypothesis.

Step 6 applies the new coherent vanishing input with d=1, not the invalid arbitrary-base use in the source. lem-sfb-space-affine-base-higher-image-sections states the needed isomorphism with Gamma of R^2 for a quasi-coherent module and qcqs morphism over an affine base. The obstruction node then gives a line module and restriction isomorphism, rather than an unjustified global unit lift. Step 7 pulls back the local trivializations and composes the restriction isomorphisms; this is a direct tensor calculation. The infinitesimal criterion uses the algebraicity and local finite presentation already obtained, and lem-sfb-stack-chartwise-smooth-etale-calculus explicitly supplies the field-extension interpretation of atlas surjectivity.

For small cases, empty families give the terminal line-module groupoid and cause no rank-one or dimension exception; zero square-zero ideal gives the identity restriction and zero obstruction; dimension-zero fibres still satisfy the H^2 bound. Disconnected and nonreduced proper curve fibres were never excluded. The new obstruction input has neither a properness nor a Noetherian assumption, while the new vanishing input deliberately does. Every new file is statement-only with all objects introduced, no inline proof; none restates an item clause. The seven proof steps are each below 1000 characters, so none hides a long inline lemma under the 2000-character rule. Read delivery-errors B--E in both their original and merged copies and checked sources, hypotheses, object identities, definitions, cycles, searches and citation coverage accordingly.

## Unfinished work

The three new inputs remain unsplit by design. No part of the item's assembly proof is deferred. The maintainer independently reviews this delivery after push.
