# Stage-1 report: det-thm-groth-ss

## Files written

- dag/nodes/sec-picard-framework/det-thm-groth-ss.json: the item, split into five proof steps, statement preserved verbatim, no Mathlib match.
- citations.json: verbatim statements backing every node citation in each step.
- searches.jsonl: actual Mathlib searches recorded by msearch.py.
- report.md: this report.

No new nodes and no new Mathlib leaves. No Lean, compiler, Lake, repository writes, or direct git commands.

## Attachments

No attachment of the entire item. CategoryTheory.Functor.exists_grothendieckSpectralSequence (lean/WeilConjectures/CategoryTheory/SpectralSequence/Grothendieck.lean:774) proves the abstract clause, and AlgebraicGeometry.Scheme.Modules.exists_leraySpectralSequence (lean/WeilConjectures/AlgebraicGeometry/Cohomology/Leray.lean:89) gives the scheme module case. I read their full hypotheses and proofs and the general abstract file. Neither declaration states the entire item with its arbitrary-site specialization. The etale lowerStar theorem is specific to schemes and constant module coefficients, so it does not supply that missing scope either. These are partial coverage observations, not an ATTACH claim for the item.

## WANTED

None. The needed Stacks sources are available locally.

## What was wrong or missing

The imported statement is retained. Its proof had no citations for existence of resolutions, the two spectral sequences, their convergence, or derived-functor computations; most steps had elementary=null. The new proof cites existing results for those inputs and uses explicit elementary kernel and scalar computations only where appropriate.

The two degrees in the second filtration needed care: original-complex degree a is horizontal; resolution degree b is vertical. Its page is E_1^(b,a)=H^a(Psi(J^(bullet,b))), then E_2^(b,a)=R^b Psi(H^a(K)). Rename (b,a)=(p,q) only at the end. In particular one does not transpose a spectral sequence with its differential unchanged.

The imported module argument's suggested application of injectivity to j_! I|U -> I does not exhibit a map representing the section to extend. I use the existing, stronger and precise module pushforward acyclicity node, as proved in Stacks 01EX, rather than retain that unsupported parenthetical. The module pullback need not be exact. Properness and coherence are only extra hypotheses on an instance of a construction valid for all module sheaves.

The cited site-relative Leray tag is 0734 (sites-cohomology-lemma-relative-Leray). Tag 0733 is the subsequent degeneration criterion, not the relative spectral-sequence existence theorem. The item's maintainer-owned source metadata is retained, while the proof's source fields identify the actual lemmas used.

The unit's key statement is openness of the perfect locus, not this spectral-sequence tool. I do not modify its realization fields. The unit and chapter routes remain unchanged.

## Not duplicates

No new node is proposed. The whole-DAG and blueprint search found sk-thm-groth-ss, which repeats the item's statement; it is recorded in blueprint.same_as, not made a proof dependency (that would merely relocate the same task). thm-sp-grothendieck and src-grothendieck-spectral-sequence-nat cover the abstract content, but the proof here uses their existing foundational inputs and carries the construction itself. All generic inputs already exist; none needs another node.

## Review by O1

I read the current literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/det-thm-groth-ss.md statement, the imported full proof, the chapter and unit records, and the three blueprint levels in SETUP. The statement agrees with the current blueprint. For the mathematical construction I read derived.tex, definitions and proofs at labels definition-cartan-eilenberg, lemma-cartan-eilenberg (015I), lemma-two-ss-complex-functor (015J), lemma-compose-derived-functors (015M), and lemma-grothendieck-spectral-sequence (015N). For the specializations I read sites-cohomology.tex lemma-Leray (0732) and lemma-relative-Leray (0734), and cohomology.tex lemma-pushforward-injective (01EX), lemma-Leray (01F2), and lemma-relative-Leray (01F6). No SGA route is used.

For step 1, I opened lem-sp-grothendieck-enough-injectives and checked it gives precisely enough injectives in both source and intermediate categories. def-sp-injective-resolutions and def-sp-left-exact-additive specify the resolution and derived-complex conventions; lem-sp-derived-well-defined supplies independence and the degree-zero identification. I wrote out the recursive cokernel construction of the initial resolution, rather than mistake its definition for an existence theorem. lem-sp-cartan-eilenberg-exists states all five needed resolution properties, including injective horizontal cycles and boundaries, for a first-quadrant complex in an abelian category with enough injectives. Phi(I) satisfies that hypothesis. The target category C is only abelian throughout; no Grothendieckness or injectives are required there.

For step 2, thm-sp-double-complex-spectral-sequences actually states the column first page, its horizontal d_1, convergence and the finite filtration; it is not just a definition of spectral sequence. The derived-functor definition computes that page on the column resolutions, and lem-sp-derived-well-defined gives the natural R^0 Psi=Psi comparison. det-def-groth-ss supplies exactly the assumed vanishing on Phi(I). I checked lem-weil-pbc-first-quadrant-row-collapse requires vanishing for every q>0 and a finite decreasing filtration: both are established here. It concerns the bottom row, which is the row present here. The original injective resolution of A computes the derived composite directly; no acyclic-resolution theorem is silently invoked.

For step 3, I re-opened the CE existence statement to check the horizontal cycles and boundaries are injective in each fixed resolution degree. Those are precisely the hypotheses of lem-sp-cart-eilenberg-left-exact-cohomology. That node states the canonical comparison induced on cycles and quotients, which explains its compatibility with vertical maps, rather than supplying an unrelated abstract isomorphism. The CE statement also says the vertical cohomology complexes are injective resolutions of H^a(K). Together with the derived-functor definition and well-definedness this yields the displayed E2 term. The double-complex theorem explicitly gives the finite image filtration; an isomorphism H^n(Tot D) -> R^n(Psi Phi)(A) carries each filtration subobject to its image and carries its successive quotients to the same E-infinity terms. This is the abutment defined by det-def-groth-ss. I also read def-sp-double-complex-total for its total differential d_I+(-1)^a d_II. The second first-page differential has the sign (-1)^a, so I explicitly identify its complex with the unsigned resolution complex by the cochain isomorphism (-1)^(ab) in vertical degree b. The written exponent calculation checks the differential equation. No separate comparison or identification theorem is hidden here.

For step 4, lem-weil-pbc-site-sheaves-enough-injectives says abelian with enough injectives, not Grothendieck. I therefore state explicitly that steps 1--3 use only this weaker input after their initial enough-injectives line, instead of claiming that this node proves Grothendieckness. def-weil-pbc-sites-and-cohomology contains the actual precomposition direct image, adjunction, composition convention and cohomology-as-derived-sections meanings. lem-weil-pbc-site-pullback-abelian-exact gives the exact additive inverse image on arbitrary sites, not merely schemes. lem-sp-right-adjoint-preserves-injectives applies to that exact left adjoint, and lem-weil-pbc-derived-functor-injective-vanishing then gives the needed h_*-acyclicity. I checked their source/intermediate/target types and have not applied a scheme-only etale lemma to arbitrary sites. The structural morphism to the punctual topos identifies direct image with maps from the terminal sheaf, i.e. global sections, even when a particular presentation of the site lacks a terminal object.

For step 5, lem-sc-ringed-space-module-sheaves-enough-injectives applies to the underlying ringed spaces of schemes. def-weil-sheaf-of-modules-category states kernels are sectionwise; def-pc-ringed-spaces-derived-direct-image gives the actual direct image formula and its scalar action. Those statements justify the elementary left-exactness and global-section identities written in this step. I initially considered citing def-pc-module-pullback for the formula, but its statement gives only the pullback and adjunction: I corrected the proof citation to the direct-image definition, which really states it (C4). lem-weil-pbc-module-pushforward-injective-acyclic gives Gamma(V,-)-acyclicity for every open V, in particular V=Y, without flatness, properness or coherence. def-sc-ringed-space-module-cohomology identifies the abutment with derived global sections; restricting scalars leaves kernels, images and quotient groups unchanged, so the coefficient convention introduces no new cohomology comparison. The derived-functor nodes justify using the same chosen resolution. No preservation of injective modules by f_* is claimed.

I checked delivery-errors B--E point by point: no statement-only new node contains a proof, no object is left unintroduced, the statement dependencies describe its notions, citations use exact node statements rather than their internal constructions, sources have verified Stacks tags and labels, and no new search entry is invented. msearch.py ran both semantic phrasings plus LeanSearch, Loogle and grep; their displayed hits concern derived functors or other infrastructure, not this spectral sequence theorem. The item is not a Mathlib leaf. No node used by the proof has a dependency path back to this item, as checked by reading the DAG edges. Every proof step has elementary=false and a source. All five steps are below 2000 characters and each carries a single stage of the construction or specialization.

The edge checks include A=0 (zero resolutions give the zero sequence), Phi or Psi the identity (one surviving row or column yields the expected derived functor), degree zero (R^0=the original functor and the filtration has its single required quotient), and an arbitrary nonflat scheme morphism in the module case (only sections-acyclicity, not preservation of injectives, is used). No new mathematical statement is being asserted as a node, so there are no untested new lemmas.

## Unfinished work

None in this one-level split. Existing cited nodes keep their existing proof status and are not modified by this delivery. The independent maintainer review remains the mathematical acceptance step.

## Validation

The standalone server review_split passed. The first full dry run returned OK (not pushed) at 252095fc692. A final source comparison made the elementary second-page sign correction explicit; the final dry run is run again on that version before delivery.
