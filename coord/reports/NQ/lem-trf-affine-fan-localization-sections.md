# Stage-1 repair: lem-trf-affine-fan-localization-sections

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-fan-localization-sections.json`: same statement, four assembly steps (2257 characters), existing metadata and all eleven previous Mathlib searches retained.
- `dag/nodes/sec-trace-formula/lem-trf-monoid-principal-open-face.json`: statement, unsplit; no Mathlib match. Principal-face geometry and basic-open localization maps.
- `dag/nodes/sec-trace-formula/lem-trf-monoid-sheafification-trivial-covers.json`: statement, unsplit; no Mathlib match. Monoid/set sheafification comparison, local bijectivity, and evaluation on opens with trivial covers.
- `dag/nodes/sec-trace-formula/lem-trf-monoid-prime-minimal-neighborhood.json`: statement, unsplit; no Mathlib match. Finite-generator face calculation, smallest neighborhood, equality of localizations, and numerator units.
- `citations.json`: verbatim statement excerpts for every dependency in every parent step.

## Attachments

None. The upstream `lean/WeilConjectures/` searches for the blueprint tag, affine fan, monoid spectrum and the relevant neighborhood/sheafification concepts found no closed declaration of this item. The local `Sheaf.AlgebraicGeometry.AffineFanLocalizationSections` theorem `AlgebraicGeometry.FineFan.affineFan_localization_sections`, line 61, ends in `sorry` at line 87 and is not an attachment. No Lean was changed or compiled.

## WANTED

None. I read ILO, Exposé VIII, printed pp.98--99 (PDF pp.104--105), especially 3.1.1--3.1.4, and the local Stacks `sites.tex` at labels proposition-sheafification-adjoint (00WH), lemma-sections-sheafification (00WK), and section-sheaves-algebraic-structures (00YR). No SGA source was used.

## What was wrong and what changed

This repairs the human's 2026-10-21/22 re-split return, which requires at least two comparable new statement-only tasks and a parent proof of at most 3000 characters. There is no change to the item's mathematical statement, hypotheses, canonical maps, or unit/chapter route. The available sandbox contained only dispatcher marker files, not the old nodes or report; I therefore copied the current repository node, whose eight steps have the exact lengths quoted in the return. There was no retained report or searches.jsonl to reuse. All previous searches embedded in the item remain untouched; all new searches ran through the prescribed msearch.py and are in searches.jsonl.

The three new statements have comparable size (1212, 1237, 1195 characters) and independent inputs. None restates the sharp affine model's section or stalk theorem. The principal-open task is monoid geometry, the sheafification task works on any topological space with any monoid presheaf, and the prime task is finite-generation and localization algebra. New nodes have status unsplit, empty proof and proof_deps, and null proof_origin; their work briefs below retain the old arguments without putting proof sketches in statements. This explicit human request to spread the work is why the former elementary multi-step calculations are grouped into independently assignable tasks.

The old generic sheafification dependency is now work for the new sheafification task. The parent no longer takes that theorem directly as a tool. Its existing maintainer-owned tool_uses and review/Lean metadata were left untouched. No statement dispute was found.

## What could not be finished

Nothing in stage 1. The three extracted arguments deliberately remain statement-only, ready for independent workers. Their future proofs can reuse lem-trf-commutative-monoid-sheafification, lem-weil-pbc-large-set-sheafification, def-weil-pbc-sheafification and, optionally, lem-weil-pbc-site-sheafification-sections-local. These are prospective proof inputs, not proof_deps of unsplit nodes.

## Review by NQ

I compared the complete current parent statement with ILO VIII 3.1.3 and 3.1.4(iii). The sheaf is the sheafification of the sectionwise quotient, not an assumed sectionwise quotient sheaf. Basic sections and stalks therefore need separate arguments. I retained the ambient integral group-completion model of localizations; fineness is finite generation plus injectivity into the completion, and neither saturation nor torsion-freeness is added.

For the principal-open node I read ILO VIII 3.1.2--3.1.4(i),(iii). Its explicit face F_a supplies a distinguished prime m_a in D(a); every other prime there is contained in it. A neighborhood of m_a contains D(a), so selecting the member of a cover that contains m_a yields the entire basic open. The same face detects D(c) contained in D(a), and the equation a+d=nc supplies the inverse -a=d-nc in P_c. This is a real topology/localization argument, not a new formulation of the parent section theorem. I checked the n=0 case: it says a is a unit and still gives that inverse. F_0 is the units and D(0) is the whole space, including when P is a group.

For the monoid-sheafification node I read the ILO remark and all three Stacks passages listed above. I opened the statements of lem-trf-commutative-monoid-sheafification, lem-weil-pbc-large-set-sheafification and def-weil-pbc-sheafification. The first explicitly identifies underlying set sheafification with the same unit. The second is a local-bijection criterion, not a direct assertion that the unit is locally bijective; the old universal-property argument proving that sheafification inverts its unit is retained in the work brief. The third is exactly that universal property. Local lifts and local equalities become global on a nonempty open whose every cover contains the whole open. The inverse of a bijective monoid homomorphism preserves addition and zero by injectivity. Naturality of the unit gives the restriction formulas for the inverse components. I chose a common universe containing all opens and coefficients, as required by the small-site statement. Nonempty opens are specified: the empty open admits the empty cover, and for an arbitrary presheaf its sheafification value there need not be its original value.

For the prime-neighborhood node I read ILO VIII 3.1.1--3.1.4. An ideal cannot meet a summand of an element in its complementary face; this verifies the generator-subset claim without assuming a free monoid. The sum b of those generators gives the intersection of all D(f), f in F, and the explicit negative-generator formula gives P_b=P-F. The converse numerator-unit criterion uses integrality to turn a completion equality into p+q=f in P, then the face property. I checked an empty generating tuple (the trivial monoid), empty selected tuple (F consists only of 0), the empty prime (F=P and localization is P^gp), the maximal prime (F=P^times), groups including torsion, and non-saturated fine monoids such as the submonoid generated by 2 and 3 in N. Nothing in these constructions requires saturation or a torsion-free completion.

For parent step 1 I opened def-trf-fine-fan-blowup: it states the sharp sheaf is the sheafification of the quotient presheaf and the unsharp sections on D(a) are P_a. The new principal-open statement gives precisely the cover property, with nonemptiness witnessed by m_a. The new sheafification statement supplies the component isomorphism, so the quotient is the asserted P_a/P_a^times. Restriction sends an inverse equation to an inverse equation, which justifies the quotient presheaf without an extra lemma.

For step 2 I checked the principal-open statement actually gives the localization inclusion and identical group-completion element; the definition node states that these are the unsharp restriction maps. The sheafification node explicitly gives compatibility of component isomorphisms AND their inverses. This proves the sharpened restriction and numerator formulas, not merely an abstract isomorphism.

For step 3 the prime-neighborhood statement explicitly gives the smallest neighborhood and P_b=P-F. The definition node explicitly defines stalks by germs modulo restriction to smaller neighborhoods. Every representative restricts to this least neighborhood, and equality there has no smaller witness, so the stalk identification and its germ map follow in two lines from those precise assertions and the already established restriction formula. I corrected the automatically selected citation excerpt to quote the smallest-neighborhood clause here, and added a second excerpt for P_b=P-F.

For step 4 I checked the definition of quotient by units says exactly that a numerator class is zero iff the numerator is a unit. The new prime statement has the full numerator-unit equivalence including the witness p+q=f, so the zero-germ claim uses its statement and no hidden proof. All cited step dependencies have literal excerpts in citations.json. I checked the four assembly texts are each below 2000 characters and total 2257. The old eight arguments are preserved verbatim below and each is assigned explicitly; none was dropped to obtain the shorter assembly.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 of delivery-errors.md, including their duplicated inherited sections: statement-only new nodes, self-contained hypotheses, definition citations, single TeX escapes, exact source places, actual search logs with unavailable verdicts, blueprint ancestry, no closed attachment, exact statement-level citations, no circular proof inputs, no off-unit replacement route, no clause-only or whole-proof replacement node, the empty/unit/group cases and the explicit restriction and germ formulas. The source itself is consistent here. No new step hides an uncited non-elementary comparison.

## Searches and blueprint comparison

Before creating nodes I searched all DAG statements and source fields for principal faces, divisors of powers, smallest neighborhoods, prime complements, trivial covers, sheafification, and the shared Stacks tags; and searched the whole blueprint with blueprint_refs.py for monoid spectrum, fine monoid, prime monoid, smallest neighborhood, trivial cover, principal face, sheafification trivial and 00WK. No blueprint node states any new statement. The ancestor command returned lem-trf-local-term-locality; all new from.via lists prepend the item to its unchanged historical ancestry, and their places identify ILO 3.1.3--3.1.4 below that ancestor. I read the chapter and sk-i-curve-zero records; this remains the pre-existing historical nearby-duality/alteration branch, not a substitution for the present contracting-correspondence unit proof.

For each new node I ran LeanFinder, Loogle, grep and LeanSearch, with two phrasings in LeanFinder and alternative name/pattern searches. Read hits include ring PrimeSpectrum.basicOpen and its cover lemmas, which require semiring ideals; these are not monoid spectra. For the sheafification task, isIso_toSheafify requires the whole presheaf already be a sheaf, whereas this task permits arbitrary presheaves and selected trivially covered opens. I read Mathlib CategoryTheory/Sites/Sheafification.lean and LocallyBijective.lean: neither directly states all those component/naturality assertions. For the prime task I read Submonoid.LocalizationMap.map_isUnit_iff in GroupTheory/MonoidLocalization/Divisibility.lean; its general divisibility criterion does not supply the finite face generators, the minimal monoid-spectrum open, or equality of the two localizations. Localization.fg likewise only states finite generation of a localization. None is an exact or one-line match. LeanSearch returned rate-limit errors, recorded as unavailable in each new node.

## Not duplicates

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-point-upper-star-tensor: the existing statement concerns $p^*$ preserves tensor products; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-site-inverse-image-multimap-universal: the existing statement concerns Universality of inverse-image units for natural maps with finitely many inputs; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-def-sfb-ring-object-sheaf: the existing statement concerns Sheaves of rings are ring objects of abelian sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-prop-sfb-qlbar-colimit-x-integral-limit: the existing statement concerns $\mathcal O_{E,X}$ is the limit of its finite levels; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pe-ring-sheafification-underlying-sets: the existing statement concerns Ring sheafification commutes with underlying sets on any small site; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-point-upper-star-unit: the existing statement concerns $p^*$ preserves the unit; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-pe-sections-limits-colimits: the existing statement concerns Evaluation on a weakly contractible affine preserves limits and colimits of modules; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pe-two-term-reduction-cohomology: the existing statement concerns Cohomology and quotient maps of a two-term integral coefficient complex; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-point-upper-star-braided: the existing statement concerns $p^*$ is braided; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pe-successive-quotient-flat-complex-sequence: the existing statement concerns The successive coefficient sequence stays exact on flat-term sheaf complexes; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs def-pe-proetale-object-restriction-comparison-data: the existing statement concerns Canonical pro-étale object restriction comparison data; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-regular-scalar-extension-multiplication: the existing statement concerns Normalized scalar extension of regular sheaf modules and multiplication; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-def-sfb-constructible-local-model: the existing statement concerns Finite constant local models; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-def-sfb-sheaf-tensor-structure: the existing statement concerns The symmetric monoidal structure on $\mathcal A$-valued sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-pe-injective-acyclicity-reduction: the existing statement concerns Reduction of the acyclicity to affine étale objects; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pe-constant-left-module-inverse-image: the existing statement concerns Exact geometric inverse image with arbitrary constant left-module coefficients; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-coef-small-flat-subsheaf: the existing statement concerns Uniformly small nonzero flat subsheaves with flat quotient; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-coef-small-flat-subextension: the existing statement concerns Bounded flat subextensions over a prescribed small flat subsheaf; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-a1-etale-atlas-presentation: the existing statement concerns An etale atlas presents an algebraic space as its relation quotient; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-zl-partition-refinement-sheafification: the existing statement concerns Sheafification at an object whose covers refine finite disjoint partitions; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-zl-affine-component-site-projection: the existing statement concerns The component-site projection for an affine scheme; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-comparison-next-degree-image: the existing statement concerns Image of the next-degree cohomology comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-algebraic-space-open-gluing: the existing statement concerns Gluing algebraic spaces along open subfunctors; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-associated-log-universal-stalks: the existing statement concerns Associated log structures: construction, universal property and geometric stalks; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-coherent-object-approximation: the existing statement concerns Coherent objects: finite images and filtered approximation; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-finitary-site-coherent-generators: the existing statement concerns Coherent generators and a morphism criterion for finite-cover sites; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-coherent-epimorphic-quotient: the existing statement concerns Coherence of an epimorphic quotient with quasi-compact kernel pair; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-closed-complement-site-construction: the existing statement concerns Site construction for the closed complement of a subterminal sheaf; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-constant-coefficient-composition: the existing statement concerns Canonical pro-etale constant coefficient maps respect composition; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-affine-fan-localization-sections: the existing item is the sharp affine monoid section/stalk theorem; the new task works on any topological space and any monoid presheaf and asserts no monoid-spectrum localization formula.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-etale-relation-kernel-pair: the existing statement concerns Kernel pair of a quotient by a monomorphic equivalence relation; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-coherent-conservative-reflection: the existing statement concerns Reflection of coherence by a coherent conservative inverse image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs def-trf-abelian-inverse-image-presentation: the existing statement concerns Normalized presentations of abelian inverse image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-etale-relation-restriction-quotient: the existing statement concerns Restriction of an etale relation preserves its quotient; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-fppf-sheaf-coproduct-partition: the existing statement concerns Scheme tests of coproducts of fppf sheaves give clopen partitions; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-commutative-monoid-sheafification: the existing node gives monoid sheafification and its underlying set comparison; the new task additionally establishes the local conditions and the natural component isomorphisms on selected trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-module-pullback-injective-section-acyclic: the existing statement concerns Pulled-back injective modules are acyclic for object sections; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-trf-sheafified-module-differentials-cokernel: the existing statement concerns Sheafified presentation of modules of differentials; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs def-weil-pbc-sheafification: the existing node defines sheafification by its universal property; the new task proves local and component assertions for monoid presheaves.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-constant-realization-reflects-isomorphism-general: the existing statement concerns Constant realization reflects derived isomorphisms and perfectness on a nondegenerate site; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-integral-tensor-quotient-epimorphism: the existing statement concerns tensor quotient epimorphism; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-constant-realization-reflects-isomorphism: the existing statement concerns Constant realization reflects algebraic derived isomorphisms locally; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs det-lem-coefficient-finite-descent-sections: the existing statement concerns Finitely many sections of $\overline{\mathbf Q}_{\ell,X}$ lie in one $E_X$; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-wcontractible-constant-reductions-ml: the existing statement concerns Mittag–Leffler cohomology for constant reductions on a weakly contractible affine; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-internal-action-site-presentation: the existing statement concerns Twisted-arrow site presentation of internal group actions on module sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-geometric-inverse-image-constant-module: the existing statement concerns Geometric inverse image preserves constant module sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-proetale-object-inverse-image-restriction: the existing statement concerns Pro-étale inverse image along a site object is slice restriction; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-constant-realization-detects-zero: the existing statement concerns Nonempty constant sheaf detects a zero module; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sfb-perfect-constant-derived-map-local: the existing statement concerns Derived maps out of a perfect constant complex are locally algebraic; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-per-integral-chart-logification-thickening: the existing statement concerns Integral chart logification on arbitrary schemes and strict first-order restriction; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-finite-type-module-sheaf-stalk-finitely-generated: the existing statement concerns Geometric stalks of a sheaf of modules of finite type are finitely generated; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-cokernel-local-image: the existing statement concerns The kernel of a sheafified quotient is the subsheaf of sections locally in the image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-pullback-abelian-exact: the existing statement concerns The inverse image of abelian sheaves along a morphism of sites is exact; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-ring-sheafification-space-underlying-abelian: the existing statement concerns Sheafification of a presheaf of commutative rings on a space: existence and underlying abelian sheaf; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-affine-closed-inverse-image-left-adjoint: the existing statement concerns Affine pro-etale closed inverse image has an extra left adjoint; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction: the existing statement concerns For a functor of sites preserving sheaves, u_s = (u_p -)^# is left adjoint to u^s (Stacks 00WX); it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-abelian-objects-bijective-surjective: the existing statement concerns Sectionwise reconstruction is surjective on objects; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-abelian-direct-image-internal: the existing statement concerns The internal commutative-group identification commutes with abelian etale direct image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-ring-inverse-image-unit: the existing statement concerns EtaleRingInverseImageUnit; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-abelian-objects-bijective: the existing statement concerns Sectionwise abelian-object functors are bijective on objects; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-finite-ring-derived-local-constancy: the existing statement concerns Finite-ring bounded lisse complexes and finite derived isomorphism sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-algebraic-structures-ring-component: the existing statement concerns SheavesAlgebraicStructuresRing intermediate component; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-stage3-epi-over-functor: the existing statement concerns Restriction to an over-site preserves epimorphisms of module sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs def-weil-pbc-sites-and-cohomology: the existing statement concerns Sites, morphisms of sites and cohomology on an object of a site; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheafification-sets-exact: the existing statement concerns Sheafification of presheaves of sets commutes with finite limits; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-ring-objects-injective: the existing statement concerns Injective component of sectionwise ring-object reconstruction; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-inverse-image-stalk-pair-representatives: the existing statement concerns Two inverse-image stalk elements have unit representatives on one open; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-qcqs-sections-filtered-colimit: the existing statement concerns Sections over a quasi-compact quasi-separated etale object commute with filtered colimits of sheaves of modules; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaves-directed-colimit-sections: the existing statement concerns Sections of a directed colimit of sheaves of sets over a quasi-compact open (Stacks 009F); it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-inverse-image-abelian-lift-ops: the existing statement concerns lem-weil-pbc-etale-inverse-image-abelian-lift-ops; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-localized-sheaves-over-representable: the existing statement concerns Sheaves on a localized site as sheaves over a sheafified representable; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-localization-inverse-image-coherence: the existing statement concerns Coherent localization comparison for exact inverse image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-tensor-ideal-quotient: the existing statement concerns Sheaf tensor with an ideal quotient, normalized on sections and quotient maps; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-constant-morphism-local: the existing statement concerns Constant module sheaf morphisms are locally algebraic; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-underived-exchange-sectionwise: the existing statement concerns Well-definedness of the sectionwise exchange rule; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-filtered-colimit-sections-finite-coverings: the existing statement concerns Filtered colimits of sheaves are computed on sections on a site with finite coverings; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-sheafification-sections-local: the existing node gives local lifts/equalities for set presheaves; the new task identifies monoid sheafification and obtains natural monoid component isomorphisms at trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-algebraic-structures-objects: the existing statement concerns Sheaves of abelian groups and of commutative rings are group and ring objects in sheaves of sets; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-constant-ring-sheaf-sections-locally-constant: the existing statement concerns Sections of the constant sheaf of rings are locally constant; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-pullback-unit-pointed-witness: the existing statement concerns Pointed etale witness for equality of inverse-image unit sections; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-ring-direct-image-comparison: the existing statement concerns The transported right ring-object functor is sectionwise etale direct image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-inverse-image-ring-adjunction: the existing statement concerns Étale ring inverse-image adjunction and forgetful hom-set comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheafification-plus-theorem: the existing statement concerns The plus construction computes sheafification; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-abelian-forward: the existing statement concerns The full sectionwise abelian-object functor; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-algebraic-structures-ring-morphism: the existing statement concerns Ring sheaf morphism criterion; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-algebraic-structures-ring-core: the existing statement concerns Ring sectionwise construction and operation compatibility; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-algebraic-structures-abelian-component: the existing statement concerns SheavesAlgebraicStructuresAbelian intermediate component; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-ring-direct-image-operations: the existing statement concerns Sectionwise ring-operation preservation of the etale direct-image comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-constant-module-sheaf-sections-locally-constant: the existing statement concerns Sections of the constant sheaf of modules are locally constant; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-algebraic-sheaf-iff-underlying-sets: the existing statement concerns A presheaf of abelian groups or commutative rings is a sheaf iff its underlying presheaf of sets is; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-adjunction-ring-operations: the existing statement concerns The counit respects transported constants and product operations; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits: the existing statement concerns Exact colimit-preserving evaluation at an affine weakly contractible object; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-ring-objects-bijective: the existing statement concerns Sectionwise ring-object functors are bijective on objects; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-ringed-topos-equivalence-ring-transport: the existing statement concerns Transport of a single commutative ring sheaf across an equivalence; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-ring-inverse-image-counit: the existing statement concerns EtaleRingInverseImageCounit; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation: the existing statement concerns Sheaf presentation by a covering set of sheafified representables; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-shriek-to-star-injective: the existing statement concerns The map from extension by zero to direct image is injective; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction: the existing statement concerns Sectionwise reconstruction on the identical underlying sheaf; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs new-r2-etale-abelian-kan-comparison-locally-surjective: the existing statement concerns Local surjectivity of the concrete underlying-set Kan comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-abelian-objects-bijective-injective: the existing statement concerns Sectionwise reconstruction is injective on objects; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs aux-site-filtered-colimit-sections-inverse: the existing statement concerns Existence of an inverse to the section comparison map; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-sheaf-ring-objects-surjective: the existing statement concerns Surjective component of sectionwise ring-object reconstruction; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-pullback-abelian-underlying: the existing statement concerns Underlying sets commute with abelian sheaf inverse image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-module-sheafification-lift-injective: the existing statement concerns A locally injective map into a sheaf induces an injective map on the sheafification; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-inverse-image-abelian-lift: the existing statement concerns Étale inverse image: abelian lift and hom-set comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-large-set-sheafification: the existing node characterizes maps inverted by set sheafification; the new task concerns arbitrary commutative-monoid presheaves and their natural component isomorphisms on selected opens.

lem-trf-monoid-sheafification-trivial-covers vs prop-weil-pbc-proetale-constant-exact: the existing statement concerns Exactness of the pro-etale inverse image for constant coefficients; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-inverse-image-abelian-lift-hom: the existing statement concerns lem-weil-pbc-etale-inverse-image-abelian-lift-hom; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-etale-inverse-image-ring-lift: the existing statement concerns Étale inverse image: ring lift and hom-set comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-site-sheafification-iso-locally-bijective: the existing statement concerns A presheaf map sheafifies to an isomorphism iff it is locally injective and locally surjective; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-proetale-sheafification-wcontractible-sections: the existing statement concerns Sheafification preserves sections on a weakly contractible object; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-completed-coefficient-tensor-normalization: the existing statement concerns Normalized completed coefficient tensor presentation and its inverse image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-proetale-constant-ring-composition: the existing statement concerns Composition of canonical constant-ring maps on pro-etale sites; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-proetale-derived-pullback-identity: the existing statement concerns Identity normalization of finite-coefficient pro-etale derived pullback; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-proetale-isomorphism-inverse-image: the existing statement concerns Inverse image along an isomorphism of schemes on the pro-etale site; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-exc-closed-inverse-image-formula: the existing statement concerns A presheaf formula for closed inverse image; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-open-cover-cohomology-detection: the existing statement concerns Open-site cohomology comparisons and Zariski vanishing detection; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-cbc-proetale-functions-quotient-sections: the existing statement concerns Affine values of the functions-modulo-constant-sheaf quotient; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-proetale-inverse-image-tensor-comparison: the existing statement concerns Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-constant-scalar-unit-quasi-isomorphism: the existing statement concerns The normalized regular coefficient scalar unit is a quasi-isomorphism; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-cbc-module-sheafification-underlying-sets: the existing statement concerns Module sheafification commutes with underlying sets on a sieve site; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs def-pur-supported-cup: the existing statement concerns Cup product with closed supports; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sp-finite-ring-action-local-constancy: the existing statement concerns A finite ring action on a finite locally constant sheaf is locally constant; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-proetale-open-unit-evaluation: the existing statement concerns Canonical open pro-etale pullback evaluation and its unit; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs pur713-def-point-site: the existing statement concerns The pro-étale site of a point; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-site-algebraic-composition-unit: the existing statement concerns Algebraic transport of unit-normalized site composition and identity; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs prop-sf-comparison-bound-zero: the existing statement concerns The comparison bound on coefficients of étale origin is $M=0$; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-exc-proetale-proper-open-sheaf-comparison: the existing statement concerns Proper/open comparison for pro-etale module sheaves; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-cbc-finite-constant-map-naturality: the existing statement concerns Naturality in finite coefficients of the constant-section structure map; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-cbc-presheaf-sheafification-epi-local-lifts: the existing statement concerns Local lifting criterion for epic set-presheaf sheafification on a Grothendieck topology; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-proetale-weakly-etale-localization: the existing statement concerns The small pro-etale site of a weakly etale X-scheme is the localization of X_proet; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-lisse-rank-one-aut: the existing statement concerns Automorphisms of a rank-one finite locally constant sheaf; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing statement concerns Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-pur-condensed-zl-reduction-mod-ell-power: the existing statement concerns Reduction of the pulled-back condensed ell-adic integers; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-free-module-sheafification-local-iso: the existing statement concerns Free module sheaves only depend on the sheafification of the presheaf of sets; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sc-sheafify-simply-transitive: the existing statement concerns Simple transitivity passes to sheafification; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-weil-pbc-image-presheaf-sheafification-iso: the existing statement concerns The image presheaf of a map that is surjective after sheafification has the same sheafification; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-sheafification-trivial-covers vs lem-sc-sheafify-add-action: the existing statement concerns Unique extension of natural additive actions through sheafification; it does not assert the natural monoid-sheafification component isomorphisms for arbitrary monoid presheaves on selected nonempty trivially covered opens.

lem-trf-monoid-principal-open-face vs lem-trf-affine-fan-localization-sections: the new task states monoid-spectrum topology and localization algebra only; it does not identify any sharp structure-sheaf sections, stalks, or their germs.

lem-trf-monoid-principal-open-face vs def-trf-fine-fan-blowup: the existing node defines the notions; it does not assert the new face, minimal-neighborhood, or localization criteria.

lem-trf-monoid-prime-minimal-neighborhood vs lem-trf-affine-fan-localization-sections: the new task states monoid-spectrum topology and localization algebra only; it does not identify any sharp structure-sheaf sections, stalks, or their germs.

lem-trf-monoid-prime-minimal-neighborhood vs def-trf-fine-fan-blowup: the existing node defines the notions; it does not assert the new face, minimal-neighborhood, or localization criteria.

lem-trf-monoid-prime-minimal-neighborhood vs lem-trf-fs-face-sharpening: the existing node assumes saturation and proves fineness, saturation, units and freeness for localized sharpenings. The new task needs no saturation and identifies a face from a chosen generating tuple, its smallest basic-open neighborhood, and its principal localization; these assertions are absent from the existing node.

## Retained arguments and distribution of work

The following are the eight returned proof texts, verbatim. They are work briefs for future workers, not proof fields or proof sketches in the new statements. This preserves the entire old proof while leaving the three new nodes statement-only as requested.

### Old step 1 -> lem-trf-monoid-principal-open-face

Use the monoid, prime-ideal, localization and topology definitions in [def-trf-fine-fan-blowup]. For $a\in P$, put $F_a=\{c\in P:\exists d\in P,\ n\in\mathbf N,\ c+d=na\}$. This contains $0,a$, is closed under addition, and has the face property: if $c+e\in F_a$, an equation $c+e+d=na$ puts both $c$ and $e$ in $F_a$. Hence $\mathfrak m_a=P\setminus F_a$ is a proper prime ideal: adding an arbitrary element to a nonmember of $F_a$ cannot enter $F_a$, and its complement is closed under addition. In particular $\mathfrak m_a\in D(a)$. If $\mathfrak q\in D(a)$, then every $c\in F_a$ avoids $\mathfrak q$: otherwise $c+d=na$ belongs to $\mathfrak q$, whereas all multiples of $a$ avoid it. Thus $\mathfrak q\subseteq\mathfrak m_a$.

### Old step 2 -> lem-trf-monoid-principal-open-face

Every basic neighborhood $D(c)$ of $\mathfrak m_a$ has $c\in F_a$, so the previous calculation gives $D(a)\subseteq D(c)$. Since the $D(c)$ form a basis, every open neighborhood of $\mathfrak m_a$ contains $D(a)$. Consequently every open cover $D(a)=\bigcup_i U_i$ has a member equal to $D(a)$: choose a member containing $\mathfrak m_a$. This also treats $a=0$, for which $F_0=P^\times$ and $D(0)=X$.

### Old step 3 -> lem-trf-monoid-sheafification-trivial-covers

Let $Q$ be the presheaf of commutative monoids $Q(U)=\mathcal M_P(U)/\mathcal M_P(U)^\times$. Restriction sends units to units because it sends an equation $u+v=0$ to the same equation, so these quotient restrictions are well defined. By [def-trf-fine-fan-blowup], its monoid sheafification is $\overline{\mathcal M}_P$. Apply [lem-trf-commutative-monoid-sheafification]: the underlying set presheaf $A=|Q|$ has set sheafification $B=|\overline{\mathcal M}_P|$, with the same unit $\eta:A\to B$. Work in one universe large enough for the opens of $X$ and these coefficient sets; its open site is small there.

### Old step 4 -> lem-trf-monoid-sheafification-trivial-covers

The unit $\eta:A\to B=A^\#$ is locally bijective by [lem-weil-pbc-large-set-sheafification], as follows directly from its stated criterion. First, for any sheaf $H$, its sheafification unit $\eta_H:H\to H^\#$ is invertible: the universal property [def-weil-pbc-sheafification] gives $r:H^\#\to H$ with $r\eta_H=1_H$, and uniqueness after precomposition with $\eta_H$ gives $\eta_Hr=1_{H^\#}$. Naturality gives $\eta^\#\eta=\eta_B\eta$; uniqueness after precomposition with $\eta$ then gives $\eta^\#=\eta_B$, which is invertible by the preceding argument. The cited criterion therefore applies to $\eta$. In explicit terms, each section of $B(U)$ lifts to $A$ on an open cover of $U$, and any two sections of $A(U)$ with the same image agree on an open cover of $U$.

### Old step 5 -> lem-trf-monoid-sheafification-trivial-covers

Apply these two local conditions on $U=D(a)$. Every covering family has a member $D(a)$ itself by Step 2. A local lift over that member is a lift over $D(a)$, proving surjectivity of $\eta_{D(a)}$; local equality on that member is equality on $D(a)$, proving injectivity. The monoid unit thus identifies $\overline{\mathcal M}_P(D(a))$ with $Q(D(a))=P_a/P_a^\times$, since $\mathcal M_P(D(a))=P_a$ by [def-trf-fine-fan-blowup]. The bijective monoid homomorphism is a monoid isomorphism: its inverse preserves sums and zero by injectivity.

### Old step 6 -> lem-trf-monoid-prime-minimal-neighborhood

For a prime $\mathfrak p$, its complement $F$ is a face: if $c+d\in F$ then neither $c$ nor $d$ can belong to the ideal $\mathfrak p$. Choose finite monoid generators $e_1,\ldots,e_r$ of $P$, and let $b$ be the sum of those generators lying in $F$, with empty sum $0$. Every expression for $f\in F$ uses only such generators, by the face property. Thus $F$ is generated by them. Primality gives $D(b)=\bigcap_{e_i\in F}D(e_i)=\bigcap_{f\in F}D(f)$, so $D(b)$ is the smallest open neighborhood of $\mathfrak p$. Furthermore $P_b=P-F$: since $b\in F$ the first monoid is contained in the second, while $-e_i=(b-e_i)-b\in P_b$ for each selected generator, so all of $F$ is invertible in $P_b$. Every germ at $\mathfrak p$ therefore has a representative on $D(b)$, and two representatives there have equal germs only if they agree on $D(b)$, since no smaller neighborhood exists. Step 5 now identifies the stalk with $P_b/P_b^\times=(P-F)/(P-F)^\times$.

### Old step 7 -> lem-trf-monoid-principal-open-face (localization algebra) and lem-trf-monoid-sheafification-trivial-covers (unit naturality); parent step 3 handles germs from the smallest neighborhood

The identifications in Step 5 are made by the quotient-presheaf unit, which commutes with every restriction. If $D(c)\subseteq D(a)$, then $\mathfrak m_c\in D(a)$, so $a\in F_c$ by Step 1. An equation $a+d=nc$ shows $-a=d-nc\in P_c$. Hence the restriction $P_a\to P_c$ exists and sends $p-ma$ to the same group-completion element $p-ma$; by [def-trf-fine-fan-blowup] it is precisely the unsharpened restriction. Passing to quotients sends $\operatorname{cl}(p-ma)$ to $\operatorname{cl}(p-ma)$, because units map to units. For $\mathfrak p\in D(a)$, the smallest neighborhood $D(b)$ of Step 6 is contained in $D(a)$; applying this formula to that restriction gives exactly the germ map induced by $P_a\to P-F$. Thus both the restriction and germ identifications are canonical and induced by localization.

### Old step 8 -> lem-trf-monoid-prime-minimal-neighborhood

The germ of the canonical section $p\in P$ is consequently $\operatorname{cl}(p)\in(P-F)/(P-F)^\times$. By the sharpening definition [def-trf-fine-fan-blowup], this class is zero exactly when $p$ is a unit in $P-F$. If $p\in F$, its inverse $-p$ lies in $P-F$. Conversely, if $p+(q-f)=0$ with $q\in P$ and $f\in F$, equality inside $P^{\mathrm{gp}}$ gives $p+q=f$ in $P$, using integrality. The face property of $F$ gives $p\in F$. Thus the zero-germ condition is equivalent to $p\in F$, or $p\notin\mathfrak p$, as required.

## Validation

The prescribed server dry run exited successfully: OK (not pushed) at e936c5c2c09; server preflight passed, including DAG and split review checks. The delivery adds three unsplit statement nodes and zero Mathlib leaves. The parent statement and all metadata outside proof, proof_deps, proof_origin and split_report match the current read clone exactly. Step lengths are 687, 569, 593 and 408 characters (2257 total). All twelve citation excerpts are verbatim parts of the cited statements. No local checker, compiler, Lake, git command or forbidden write was used.
