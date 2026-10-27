## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-dg-countable-compact-telescope.json: unchanged statement, six-step split of Stacks 0CRM (2) to (1).
- lem-sfb-dg-countable-subalgebra.json: statement-only; no Mathlib match, five actual searches.
- lem-sfb-dg-countable-semi-free-resolution.json: statement-only; no Mathlib match, five actual searches.
- lem-sfb-dg-finite-cell-compact.json: statement-only; no Mathlib match, five actual searches.
- lem-sfb-dg-sequential-colimit-triangle.json: statement-only; no Mathlib match, five actual searches.

Attachments: none. Searches for the item tag and for DG algebras/modules, semi-free modules, countable compact objects and telescopes in lean/WeilConjectures found no declaration giving this item. Ordinary ModuleCat telescopes and supported-perfect generation do not assert the DG-algebra/countable-cohomology statement.

WANTED: none. All newly used mathematical sources are available in literature/stacks-project/dga.tex and derived.tex. Existing general DG scalar-change equivalence is reused, rather than copied into a new node.

The item was unsplit and there was no earlier node/report/search log in this sandbox. Its statement is correct and is not changed. The inherited blueprint ancestry ends in null; tools/blueprint_refs.py ancestor printed None, which is retained. I read the latest blueprint's Six Functors: Basic Constructions chapter, sk-thm-sf-ctf-stability/_section.md and the direct-images proof, paragraph (3). This is the inherited countability input through 0CX8/0CRW/0CRV, not a replacement of that route. The current unit is not realized by this auxiliary node, so its realization record is not edited.

No work is left unfinished in this one-level split. The four new statements are queued as unsplit; their proofs are not smuggled into their statements. No Lean file or build was written or run.

## Review by Q29

I read dga.tex Tag 0CRM (lemma-countable), in full, particularly the entire implication (2) to (1), and compared every clause of the item, including the compatible legs, with derived.tex Tags 090Z (definition-derived-colimit) and 0CRH (remark-uniqueness-derived-colimit). Only the forward construction from countable cohomology is required. For the new subalgebra node I checked the paragraph choosing representatives and then adjoining primitives: one adjoins primitives only for cycles which are boundaries in A, not arbitrary cochains. Differential closure of the generated unital subring keeps it countable; the countable union gives both surjectivity and injectivity on cohomology. This does not require countability of the original underlying algebra.

For the countable semi-free resolution I read the next two countability paragraphs of 0CRM, and the full statements and proofs of 09KN (lemma-good-quotient) and 09KP (lemma-resolve). The countable submodule representative is obtained by starting with countably many cycle representatives, taking their A-span, and adjoining primitives of all cycles that die in N, iterating countably. Over countable A every span remains countable. The explicit good-quotient construction uses at most two generators for each homogeneous element and one for each cycle, so all its generators are countable; kernels and the resulting direct-sum total resolution remain countable. Choosing graded splittings of its free filtration quotients gives the homogeneous basis with a natural-number height. This is the extra assertion not contained in the existing unrestricted semi-free-replacement node. No countability of N as an underlying module is assumed or used.

For finite-cell compactness I read 09R3 (proposition-compact), especially implication (2) to (1). The identity retraction specializes its finite-filtration characterization precisely to the new statement; arbitrary DG algebras are allowed. For the DG telescope node I read 0CRL (lemma-homotopy-colimit) and its proof, and 09QI (lemma-derived-products). The latter explicitly identifies derived coproducts with actual DG direct sums; the former uses the exact sequential-colimit sequence and therefore supplies the actual canonical colimit legs. This is not the ordinary derived category of the abelian category of DG modules, and no identification with that different category is made.

In step 1 the new subalgebra statement supplies exactly a countable quasi-isomorphic inclusion. I opened lem-coef-dg-module-base-change and read its statement: its quasi-equivalence clause gives inverse derived scalar-extension and restriction equivalences for one-object DG categories, including their opposites for right modules. There is no extra local-flatness hypothesis for this clause (the flatness assumption belongs to its separate tensor-with-another-category clause). Exactness of restriction is checked on the explicit unchanged shifts and mapping cones, not claimed from the bare word equivalence. I opened the Mathlib-leaf lem-trf-exact-equivalence-inverse: it supplies exactness of the inverse with the adjunction-induced shift comparisons, precisely the comparisons used here. No new duplicate DG equivalence node is made.

In step 2 the new countable-resolution statement is applied only after A_0 has been made countable. Restriction has the same underlying complex, so all cohomology hypotheses hold. Its statement explicitly supplies the countable basis and the strictly lowering heights needed in step 3; neither conclusion is taken merely from a proof or from the definition of semi-free. Step 3 writes the finite-closure induction out: finitely many supports at strictly smaller heights terminate after finitely many levels. The Leibniz formula proves closure under the differential on arbitrary coefficients. Enumerating the basis by increasing finite subsets rather than claiming a bijection with the naturals covers finite and empty bases. Height quotients have differential induced only by A, so they really are finite sums of DG shifts. This is the elementary combinatorial construction in the item's proof, not a separately assumed exhaustion lemma.

Step 4 uses exactly the finite-filtration compactness statement and the canonical triangle statement of the two new nodes. The nested union P is the module colimit because every element has finite basis support; q and the representative identification are isomorphisms in D(A_0,d). Replacing the third object by their composite transports the second arrow, hence retains every c_m. Step 5 uses the actual inverse equivalence from scalar change and the compactness definition, both read in full; the displayed Hom bijections prove coproduct preservation and compactness without presuming preservation of infinite sums from exactness. All families are small in the prescribed ambient universe.

Step 6 cites lem-kun-functor-preserves-hocolim, whose statement I opened: it concerns exact functors preserving countable sums and explicitly compares the second and connecting arrows of the telescope triangles. Step 1 and step 5 provide its hypotheses, and the new DG colimit node provides existing coproducts in both categories. The counit formula b_m = epsilon_M L(c_m) proves b_(m+1)u_m = b_m. The images of the coprojections identify the first arrow with 1-s and the second with the coproduct of these b_m, so no unproved normalization of the telescope legs is hidden. def-kun-truncations was opened and its final triangulated-category telescope definition, rather than its unrelated sheaf-colimit clauses, is used.

I checked B1-B10: standalone TeX statements spell out DG algebras/modules and derived categories, each new node has only statements, source tags and labels were checked against the tags table and TeX, searches are copied from actual msearch output, and no completed project declaration or one-line Mathlib specialization was found. The scalar-equivalence and ordinary-complex hits do not have the missing cardinal bounds or DG telescope compatibility. The new nodes are smaller than the item: none asserts existence of compact telescope stages. The subalgebra and resolution are algebraic inputs, finite-cell compactness is a general recognition fact, and the colimit triangle applies to any sequence, without constructing the compact sequence.

For C1-C8 and D1-D5 I read every cited statement, created the missing genuinely non-elementary inputs, and placed the finite-support argument in the item. citations.json contains a verbatim statement excerpt for all 12 step/node citations. The proof dependencies are exactly their union. The reused scalar-change equivalence and telescope-transport theorem are declared as generic off-unit tools in split_report.tool_uses; the exact-inverse citation is already a Mathlib leaf. No cited node depends on this item. All steps are shorter than 900 characters; none hides a long comparison or identification.

For E1-E7 I checked zero modules and zero algebras, finite and empty bases, a countable ordinary ring in degree zero, and DG algebras with uncountable cochains but countable cohomology. The first case can use all zero stages, the finite cases may repeat a terminal stage, and the last case is why the subalgebra reduction precedes the countable resolution. Arbitrary integer degrees are allowed and the finite-closure induction is on cell height, not cohomological degree. No noetherianity, boundedness, commutativity or flatness assumption is silently added. No imported statement dispute or source-level false assertion requiring a correction was found. The source's occasional informal left-module notation is written consistently as x_j A for right modules in the new statements.

## Not duplicates

lem-sfb-dg-countable-subalgebra vs lem-sfb-dg-countable-compact-telescope: constructs a countable quasi-isomorphic subalgebra, without any module or telescope conclusion.
lem-sfb-dg-countable-semi-free-resolution vs lem-sfb-dg-countable-compact-telescope: constructs a countable graded-free module resolution over an already countable algebra, without compact stages or a telescope triangle.
lem-sfb-dg-countable-subalgebra vs lem-sfb-dg-countable-semi-free-resolution: the first concerns an algebra inclusion, the second a module resolution over a fixed countable algebra.
lem-sfb-dg-countable-semi-free-resolution vs lem-coef-dg-module-semi-free-replacement: the existing theorem has arbitrary cell index sets and asserts no cardinal bound on its resolution; the new statement supplies a countable basis under countability hypotheses.
lem-sfb-dg-sequential-colimit-triangle vs lem-kun-complex-colimit-hocolim: the existing statement concerns complexes of sheaves of abelian groups or modules over a commutative ring sheaf, not modules over a general graded noncommutative DG algebra.
lem-sfb-dg-finite-cell-compact vs lem-sfb-space-compact-objects-perfect: the existing statement is for quasi-coherent objects on qcqs algebraic spaces, not arbitrary DG algebras.

The following additional pairs cover all existing nodes found anywhere by the new source tags (including tags occurring only in supporting proofs):

lem-sfb-dg-countable-semi-free-resolution vs lem-coef-dg-module-semi-free-replacement: the existing statement gives unrestricted semi-free resolutions, without countability of the basis or total module; the new input is the cardinal-controlled version.

lem-sfb-dg-countable-semi-free-resolution vs lem-coef-dg-module-projective-resolution: the existing statement gives homotopically projective replacements and enhanced mapping complexes, without a countable semi-free basis.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-even-quotient-bijective: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-odd-quotient-bijective: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-cokernel-odd: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-base-derived-extension-coherent-triangle: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-shifted-free-coproduct: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-exhaustive: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-large-filtered-free-resolution: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-free-cover-bicomplex: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-free-cover-columns: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-even-quotient-map: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-even-quotient-surjective: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-zero-differential-free-coproduct: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-stable: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-base-derived-extension-resolution: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-step-retraction: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-odd-quotient-map: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-free-filtration: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-module-free-generation: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-even-quotient-injective: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-free-complex-cover: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-quotients: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-filtered-free-resolution: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-cokernel-odd-core: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-pc-derived-total-filtration-cokernel-even: the existing statement concerns ordinary-ring cochain complexes or their bicomplex filtration; it neither treats a general DG coefficient algebra nor provides a countable homogeneous DG-cell basis from countable cohomology.

lem-sfb-dg-countable-semi-free-resolution vs lem-sfb-dg-countable-compact-telescope: the item asserts a compact telescope; this new input asserts only a countable semi-free module resolution.

lem-sfb-dg-countable-subalgebra vs lem-sfb-dg-countable-compact-telescope: the item asserts a compact telescope; this new input asserts only a countable quasi-isomorphic algebra inclusion.

lem-sfb-dg-countable-semi-free-resolution vs lem-sfb-bundle-endomorphism-derived-adjunction: the existing assertion constructs an adjunction for a vector bundle over an ordinary scheme, and does not supply this DG-algebra input.

lem-sfb-dg-countable-semi-free-resolution vs lem-sfb-space-countable-telescope: the existing statement concerns countable quasi-coherent cohomology on an algebraic space; this is an algebraic input inside its DG-model proof, not another space telescope theorem.

lem-sfb-dg-countable-subalgebra vs lem-sfb-space-countable-telescope: the existing statement concerns countable quasi-coherent cohomology on an algebraic space; this is an algebraic input inside its DG-model proof, not another space telescope theorem.
