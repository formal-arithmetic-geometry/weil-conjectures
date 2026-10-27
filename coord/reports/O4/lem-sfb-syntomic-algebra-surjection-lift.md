## Worker report

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-syntomic-algebra-surjection-lift.json: item split, six steps, arbitrary surjection statement unchanged.
- lem-sfb-syntomic-presentation-conormal-fibre-rank.json: statement, unsplit, no Mathlib match.
- lem-sfb-equation-count-closed-fibre-localization.json: statement, unsplit, no Mathlib match.
- lem-sfb-syntomic-smooth-composition.json: statement, unsplit, no Mathlib match.
- lem-sfb-syntomic-polynomial-fibre-cut.json: statement, unsplit, no Mathlib match.

Also citations.json contains a verbatim statement quote for every step/node citation. Search outputs and the actual msearch log are retained in this sandbox.

Attachments: none. rg for the exact blueprint tag and syntomic/lifting terminology in lean/WeilConjectures found only other syntomic local-presentation and conormal declarations, not the lifting theorem. No Mathlib result is claimed as a project attachment.

WANTED: none.

The item was statement-only; no previous sandbox attempt existed. Its statement agrees with Stacks 07M8(1), including arbitrary kernels, the specified base algebra isomorphism, and the zero algebra. Nothing was weakened. The local source has a typographical slip: its lifts f_i are said to lie in R[y_1,...,y_c] rather than R[y_1,...,y_m]. The proof uses the latter, as required by their reductions. No statement dispute is needed.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md. This item supplies a ring-theoretic prerequisite in the inherited alteration/deformation chain, below the fixed chapter and unit route. blueprint_refs ancestor returns None, matching the item's inherited from.node=null; the new nodes preserve that root and prepend this item to via. Whole-blueprint searches for syntomic, 07BT, 00ST, 00SZ, 07CE, conormal and polynomial found no imported node stating a new prerequisite.

Nothing remains unfinished at this split level. The four prerequisites deliberately have no proofs or proof dependencies and remain stage-1 items.

## Review by O4

I read smoothing.tex Tag 07M8(1), including its entire construction and final local claim. I read algebra.tex Tags 07BT, 00SC, 00ST(1), 00SY, 00SZ(1), 00TA and 00U9 and more-algebra.tex Tags 07M5 and 07M6, and the projective symmetric-conormal statement realizing 07CE. These are the sources of the new conormal, closed-fibre localization, composition and coordinate-cut nodes respectively. The cut node is the final claim of the source, with a pre-existing syntomic D and polynomial reduction as hypotheses; it does not lift an algebra by itself and is strictly a prerequisite to the item's construction.

Step 1 uses the finite-presentation definition to choose finitely many generators and relations, the new conormal statement for finite projectivity, the existing projective symmetric-presentation statement for a FREE conormal presentation, symmetric-projective smoothness, syntomic composition, and the Huber presentation-basis lemma. I opened every cited statement. In particular the existing improve-presentation nodes only cover smooth input, so I did not cite them as if they covered arbitrary syntomic input. The projective conormal statement does cover the chosen Sym(J/J²), and avoids relying on the false general injectivity assertion of 07EV.

Step 2 uses exactly the fibre-rank clause of the new conormal node, not a projectivity assertion alone: the basis has rank c after every base change, hence each point of a nonempty fibre has topological local dimension m-c. This implies the global fibre dimension is m-c; a chain of irreducible closed subsets is detected in the finitely many components, and generic points have neighbourhood dimension the component maximum. Coefficientwise lifts give the displayed quotient directly. The new 00ST(1) node supplies a single element equal to 1 on the ENTIRE reduction, unlike the existing pointwise 00ST(3) node. The existing relative-ci principal-cover gluing statement applies to the one-element cover g=h=1, and gives all three syntomic clauses. No nilpotence or base flatness is imposed.

Step 3 uses the precise arbitrary-ideal projective lifting statement 07M5, with base ring C and ideal IC. Tensoring the chosen split decomposition gives a finite projective C/IC-module, so its hypothesis is verified. That statement gives the reduction isomorphism and lifted Q, not merely an etale neighbourhood with unspecified reduction. Symmetric-projective smoothness applies to Q; the new composition node explicitly includes etale and smooth inputs, so the composite R->D is syntomic.

Step 4 uses symmetric-algebra base change for reduction and the universal property to identify the tensor product of the two symmetric algebras with the symmetric algebra of the direct sum. I wrote the generator argument, the inverse-map check, and the tensor/quotient formulas. These are elementary consequences of the cited universal properties, so no new direct-sum or free-module-polynomial node was created. All identifications preserve R_0 scalars.

Step 5 invokes the cut statement only after step 3 establishes that D is syntomic and step 4 supplies its specified polynomial reduction; A_0=B_0 is syntomic by the original hypothesis. It yields the desired localization after the chosen coordinate lifts are killed. Step 6 writes the forward and inverse fraction maps and checks scalars; it uses no theorem beyond quotient/localization universal properties. The citation manifest quotes the actual statement of every cited node, not its proof or its source tag.

For the cut prerequisite, the source's local argument is worth retaining for its future worker. At each prime above I choose a relative-global-ci neighbourhood of D by 00SY; append polynomial lifts of the t_i to its equations. In the reduced fibre the t_i are polynomial coordinates, so killing them lowers the local fibre dimension by r and the enlarged equation count is exactly expected. Apply 00ST(3) locally. The resulting syntomic neighbourhoods cover V(IA). Their union is an open W; if its closed complement is V(J), then V(J+IA) is empty, hence J+IA=A. Write a+j=1 with a in J and j in IA. The element a is 1 modulo IA and D(a) is contained in W. A finite relative-ci principal cover there gives global syntomicity by 00SO. This argument is not assumed in an elementary step: it is isolated in the cut node.

I tested the item and new statements with I=0, I=R (zero reduction), zero algebras, zero variables/equations and r=0. The zero-reduction localization lemma permits g=0, since 0=1 in the zero quotient. For a non-smooth test, F_p[x]/(x²) over Z->F_p lifts to Z[x]/(x²), so no smoothness or regular special-fibre hypothesis entered. The conormal rank convention gives c=1 and fibre dimension 0 in this example and rank 0/dimension n for polynomial algebras. The composition node covers identities and empty spectra. All steps are below 2000 characters; the nontrivial local cut claim is a separate node. New nodes have statement dependencies for the notions used, no proof sketches in their statements, authentic recorded searches, and no maintainer fields. No SGA source is used. Generic algebra citations outside the unit are declared in split_report.tool_uses for the maintainer's decision.

For Mathlib I ran leanfinder, loogle, grep and leansearch for each new node, then a second semantic phrasing. I read the returned types and source candidates: formally smooth lifting fixes the algebra and assumes nilpotent kernels, smooth composition handles smooth rather than syntomic maps, conormal finite-generation does not prove projectivity/fibre rank, and localization finite-presentation supplies no expected-dimension or flatness assertion. The etale-smooth instance covers only one easy part of the composition node, so the full node is not a leaf. The searches in each JSON are copied from actual searches.jsonl records.

## Not duplicates

lem-sfb-syntomic-smooth-composition vs lem-exc-etale-jacobian-presentation: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs sbc-thm-etale-local-normal-form: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-sbc-etale-regular-divisor-base-change: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-conormal-free-presentation-basis: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-improve-presentation: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-smooth-ring-map-locally-standard-smooth: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-smooth-locally-standard-smooth: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-smooth-retract-relative-global-complete-intersection: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-smooth-ring-map-flat: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-etale-over-normal-ring-normal: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-smooth-composition vs lem-weil-pbc-etale-polynomial-standard-smooth: The new node gives composition for arbitrary syntomic maps and syntomicity of smooth/etale inputs. The existing node concerns smooth charts, smooth flatness, smooth retractions or etale presentations/normality, not arbitrary syntomic composition.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-sfb-syntomic-algebra-surjection-lift: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-sfb-nodal-family-regular-affine-presentations: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-sfb-smooth-affine-quotient-lift: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-fibre-kernel-generators: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-equation-count-comparison: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-principal-localization-fibre-transport: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-fibre-dimension-neighborhood: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-equation-count-localize-relative-global-complete-intersection: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-presentation-local-kernel: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-algebra-localization-away-base-change: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs new-equation-count-localize-presentation: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-local-kernel-intersection: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-codimension-local-kernel-generators: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-equation-count-comparison-dimension: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-equation-count-fibre-dimension-flat: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-equation-count-comparison-core: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-spec-localization-away-basic-open: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-polynomial-fibre-comparison: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-flat-smooth-fibre-smooth-at-prime: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs new-equation-count-localize-rgci: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-fibre-dimension-neighborhood-localized-bound: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-polynomial-fibre-cut vs lem-weil-pbc-syntomic-principal-localization-hypotheses: The new node starts with a GIVEN syntomic D and a specified POLYNOMIAL reduction and proves syntomicity after killing coordinate lifts and shrinking. The existing node either lifts an algebra from scratch, covers only smooth algebras, or provides local charts/conormal/dimension comparisons; none states this coordinate-cut criterion.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-trf-lci-prime-polynomial-local-presentation: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-syntomic-fibre-kernel-generators: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-localized-ideal-conormal-generator-bound: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-lci-field-change: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-syntomic-equation-count-comparison: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-standard-smooth-over-field-dimension-at-points: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-lci-regular-sequence-global-complete-intersection-presentation: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-lci-conormal-generators-global-complete-intersection: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-smooth-over-field-local-complete-intersection: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-principal-localization-conormal-at-prime-base-change: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-smooth-retract-relative-global-complete-intersection: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-syntomic-presentation-local-kernel: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-regular-sequence-dimension-at-point: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-complete-intersection-presentation-stable-conormal: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-global-complete-intersection-equidimensional: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-local-generators-clearing: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-lci-conormal-free-rank-codimension: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-quotient-away-clearing: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-principal-neighborhood-dimension: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-regular-sequence-conormal-free: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-weakly-regular-sequence-localization-prime: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-syntomic-local-kernel-intersection: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-syntomic-codimension-local-kernel-generators: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-relative-ci-closed-fiber-regular-sequence: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-syntomic-presentation-conormal-fibre-rank vs lem-weil-pbc-lci-regular-sequence-global-complete-intersection: The new node gives a globally finite projective conormal for arbitrary syntomic base maps, its comparison for residue BASE change (not merely a field extension), and the fibre rank. The existing node does not assert that combined general result; field-local rank alone is insufficient for step 1.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-fibre-dimension-neighborhood: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-equation-count-localize-relative-global-complete-intersection: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-algebra-localization-away-base-change: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs new-equation-count-localize-presentation: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-equation-count-fibre-dimension-flat: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-spec-localization-away-basic-open: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs new-equation-count-localize-rgci: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

lem-sfb-equation-count-closed-fibre-localization vs lem-weil-pbc-fibre-dimension-neighborhood-localized-bound: The new node is 00ST(1), choosing ONE element congruent to 1 along a whole arbitrary closed fibre. The existing node supplies pointwise dimension/localization, quotient presentation or localization comparison only; it does not guarantee this congruence along the entire closed subset.

