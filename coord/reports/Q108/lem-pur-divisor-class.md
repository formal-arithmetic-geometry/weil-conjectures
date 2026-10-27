# Repair delivery: lem-pur-divisor-class

## Worker report

Files written:

- dag/nodes/sec-smooth-purity/lem-pur-divisor-class.json — unchanged statement, five-step assembly, 2007 characters.
- dag/nodes/sec-smooth-purity/lem-pur-cartier-pair-tensor-addition.json — statement, unsplit; Mathlib: no match after semantic, Loogle and source searches.
- dag/nodes/sec-smooth-purity/lem-pur-divisor-normalized-realization.json — statement, unsplit; Mathlib: no match after semantic, Loogle and source searches.
- dag/nodes/sec-smooth-purity/lem-pur-principal-torsor-yoneda-sign.json — statement, unsplit; Mathlib: no match after semantic, Loogle and source searches.
- dag/nodes/sec-smooth-purity/lem-pur-smooth-codimension-one-cartier.json — statement, unsplit; Mathlib: no match after semantic, Loogle and source searches.

Attachments: none. The requested project-source tag and concept searches found no complete declaration under WeilConjectures/. Sheaf/Paper/PurityDivisorClass.lean:205 has divisor_class with sorry, as does existsUnique_generalDivisorEtaleClasses at line 228. Their data definitions do not prove these propositions.

WANTED: none.

The sandbox initially contained only the dispatcher marker files; it contained no node, report, citation record or search log to resume. I copied the current shared item, including its prior statement correction, Lean record and maintainer fields. No git command was run in the shared repository, and no Lean was written or compiled. The delivery tool performs its own required temporary-index delivery.

The return asked for the old 7872-character argument to be spread across at least two comparable tasks, with the same statement and at most 3000 characters of assembly. Four independent tasks are delivered, not a single replacement lemma. Their mathematical work is geometry; integral-to-module and site realization; torsor-extension sign; and integral tensor/Baer addition. Each new node is statement-only, status unsplit, with no proof or proof dependencies. The old argument is preserved below without shortening; its source references and every inference remain available to the workers who will split the four new nodes.

## Source and statement audit

I read main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.md and its complete proof, the chapter sec-smooth-purity record, and both the live sk-prop-a1-kummer unit and the current-source sk-prop-an unit. The old unit binding is retained. The existing item already records the source’s product-equation and sign corrections: a sum has equation f1*f2, not a two-element frame; the specified Yoneda normalization gives minus the rank-one frame boundary, and forgetting support gives the positive Chern class. This repair does not change the statement or reopen that correction.

For the geometric new node I read more-morphisms.tex, lemma-etale-local-structure (0FUE), divisors.tex lemma-immersion-smooth-into-smooth-regular-immersion (067U), and algebra.tex lemma-one-equation (00KW). The new statement assumes both members smooth over the same base and the actual local-ring dimension drop. It does not assume that an arbitrary codimension-one immersion is Cartier.

For the framed-line realization node I read etale-cohomology.tex lemma-kummer-sequence (03PL), lemma-cohomology-with-support-triangle (0A45), and the full existing statements lem-sp-relative-torsor-extension, lem-amb-relative-torsor-cohomology, lem-amb-closed-support-hom, lem-asd-cartier-boundary-existence, lem-asd-ordinary-supported-kummer, lem-asd-supported-kummer-support-hom-naturality and lem-pur-divisor-relative-cone. The new theorem treats an arbitrary line bundle framed on a closed complement, not merely the dual ideal of a Cartier divisor. This is the nontrivial scalar/relative/site comparison from old steps 2–5 and 8; the Cartier-specific existence theorem is reused as a special case rather than re-created under a new name. Its statement specifies the integral extension, the module Ext lift and the supported realization.

For the inverse-section new node I read sites-cohomology.tex lemma-torsors-h1 (03AJ), and the derived Yoneda comparison in the existing lem-per-supported-yoneda-localization statement (source derived.tex, lemma-yoneda-extension, 06XU). That existing theorem computes the splice of an already specified pushout; it does not identify the relative extension of a framed torsor with that pushout. I also read the updated lem-pur-divisor-torsor-boundary-signs statement: it explicitly uses the raw lifting-cocycle class, the negative of the Ext-normalized class. The new node is about the normalized extension and keeps these signs distinct.

For the tensor/Baer new node I read sites-cohomology.tex lemma-torsors-h1 (03AJ), cohomology.tex remark-support-functorial (0G78), and the full statements lem-sc-line-bundle-torsor, lem-sc-torsor-h1, lem-amb-relative-torsor-cohomology, lem-sp-relative-torsor-extension and lem-weil-pbc-complex-ses-long-exact-naturality. The source’s ordinary contracted-product group law is not passed off as a theorem about pairs: the new statement includes the sections, restriction to the common complement, and the equality of integral supported extensions.

These refinements of the blueprint and Stacks are agent-stated. They are not claimed to be verbatim assertions of the cited tags. No prohibited source is used.

## Review by Q108

I reviewed delivery-errors B–E with the item and the four new statements open. B1: the four tasks have empty proof lists and empty proof_deps. B2–B3: each introduces its base, schemes, coefficients, supports and specified sections, with explicit definition dependencies. B4–B7: the statements use single-escaped TeX and exact Stacks labels in source fields, with no tag standing in for a definition. The logged searches are copied as actual results; the rate-limited LeanSearch requests are marked unavailable. No Mathlib hit proves the scheme-theoretic relative assertions. The Ext.comp and Ext.hom hits supply only generic operations, and the Picard and torsor-product hits concern modules or torsor types, not relative sheaf classes with specified open sections.

Step 1 uses exactly lem-pur-smooth-codimension-one-cartier: its hypotheses are the item’s finite-type schemes, both smooth morphisms, closed immersion and local dimension equality. Its conclusion supplies the Cartier condition, even over a nonregular base.

Step 2 uses def-pc-divisor-line-bundle for the dual ideal, then lem-pur-divisor-normalized-realization for existence, uniqueness and the actual roots/site realization. The overlap computation is written explicitly, not hidden in a new definition. Multiplying an equation by a unit changes its dual frame inversely and leaves the global section unchanged. This verifies that the resulting pair is the one specified in the item’s extension predicate, not an arbitrary lift of a Picard class.

Step 3 applies lem-pur-principal-torsor-yoneda-sign with G=G_m, e=1/f and g=f on the complement. It uses the realization node’s restriction and coefficient compatibility to move this equality to the precise pro-etale group. def-pur-frame-class states the positive frame boundary, so the answer is its negative; lem-pur-frame-independence asserts equation-independence. Each cited conclusion appears explicitly in the cited statement, copied in citations.json. In particular no raw-cone connecting formula is substituted for the Yoneda splice.

Step 4 uses the tensor/Baer node’s product ideal, section-preserving tensor identification and equality of integral relative extensions after support enlargement. It then uses the realization node’s additivity in beta and compatibility with enlargement. These conclusions are in those statements, so no extra local-to-global injectivity assertion is being assumed. A product of nonzerodivisors is a nonzerodivisor; the sum may be nonreduced or nonsmooth. No proper-intersection hypothesis is used.

Step 5 is a direct substitution of the realization node’s positive forget-support assertion into the definition of c1 written in the unchanged item. It is marked elementary because it is only this identification; the comparison itself belongs to the new realization theorem.

C1/C3/C4: I read the actual statements of every node in the five uses lists, rather than borrowing a fact from their proofs. citations.json contains verbatim portions for every such use. All removed non-elementary arguments are assigned below; none is silently called elementary. D1/D2: no new node carries all the clauses of the item. The new sign theorem applies to any abelian sheaf torsor with a global frame; the tensor theorem is an integral degree-one statement before Kummer; the realization theorem applies to arbitrary closed supports and framed line bundles; the geometric theorem has no cohomology. They can be worked on independently.

E1–E5 and small cases: the empty divisor has unit ideal and trivial pair, so its supported class is zero. For the geometric node, a nonempty identity immersion fails the dimension-one hypothesis; over a nonreduced base the zero section of A1_B is still Cartier. For realization, Z empty forces the framed pair to be trivial and the Ext class to vanish; Z=T gives the ordinary Kummer class; A=0 gives zero. For the sign node, g=0 (or g extending globally) makes the pushout class zero, and changing the global frame changes g by a global section with zero localization boundary. For tensor addition, D1 empty is the tensor unit, D1=D2 is the square ideal (possibly nonreduced), and on Spec k[x,y] the ideals (x),(y) multiply to (xy), not (x,y). The support maps are the stated (x,y)->(x,y restricted to W) chain maps, so they commute with coefficient connecting maps by long-exact naturality.

The principal correction in this repair is distribution of the eight arguments. I also avoided two duplicate proposals by stating the realization for arbitrary framed line bundles and the local sign for arbitrary abelian torsors; existing Cartier-specific and already-pushout comparison results stay available as prerequisites. The item statement, its Lean interface, coefficient levels and route are unchanged. The assembly is 2007 characters; no non-elementary assembly step approaches 2000 characters.

## Not duplicates

lem-pur-cartier-pair-tensor-addition vs def-sc-torsor-extension-presentation: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Canonical extension presentation of an etale torsor.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-contracted-product-exists-data: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Translation torsor structure on the explicit sheafified orbit quotient.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-contracted-product-exists-universal: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Universal property of the explicit sheafified orbit quotient.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-contracted-product-exists: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Existence of the contracted product of an etale torsor.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-inverse-image-lifting-torsor: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Inverse image of a lifting torsor.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-inverse-image-lifts-fibre: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Underlying lifting-fibre comparison for etale inverse image.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-torsor-h1-functoriality: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Functoriality of the etale torsor classification of H1.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-torsor-inverse-image-extension: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Inverse image of the torsor extension.

lem-pur-cartier-pair-tensor-addition vs lem-sc-etale-torsor-pushout-extension: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Pushout of the etale torsor extension.

lem-pur-cartier-pair-tensor-addition vs lem-sc-extension-presentation-generator-fibre: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Generators identify the fibre.

lem-pur-cartier-pair-tensor-addition vs lem-sc-extension-presentation-short-exact: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Short exactness of extension presentation.

lem-pur-cartier-pair-tensor-addition vs new-etale-torsor-inverse-image-extension-core: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Extension core after inverse-image torsor transport.

lem-pur-cartier-pair-tensor-addition vs new-etale-torsor-inverse-image-torsor: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Inverse-image torsor and equivariance.

lem-pur-cartier-pair-tensor-addition vs lem-weil-pbc-finite-etale-equivalence-h1: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Finite etale pullback equivalence implies finite constant H1 comparison.

lem-pur-cartier-pair-tensor-addition vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: First constant cohomology vanishes on closed subschemes of the spectrum of a normal domain with separably closed fraction field (Stacks 09ZB).

lem-pur-cartier-pair-tensor-addition vs def-amb-relative-etale-cohomology: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Resolution model of relative etale cohomology and its cone maps.

lem-pur-cartier-pair-tensor-addition vs def-amb-torsor-with-section: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Torsors with a specified section and their isomorphism classes.

lem-pur-cartier-pair-tensor-addition vs def-pur-supported-class-operations: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Supported signed-twist Hom groups and their canonical operations.

lem-pur-cartier-pair-tensor-addition vs lem-amb-framed-lifts-classification: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Pointed lifting torsors modulo global translation.

lem-pur-cartier-pair-tensor-addition vs lem-amb-relative-cocycle-coordinates: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Concrete first homology coordinates for the relative restriction cone.

lem-pur-cartier-pair-tensor-addition vs lem-amb-relative-torsor-class-naturality: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Equivariant naturality of framed relative torsor classes.

lem-pur-cartier-pair-tensor-addition vs lem-amb-relative-torsor-cohomology: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Relative first cohomology and torsors with a specified open section.

lem-pur-cartier-pair-tensor-addition vs lem-amb-relative-torsor-forget-normalization: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Ordinary normalization of the framed relative cocycle.

lem-pur-cartier-pair-tensor-addition vs lem-pur-divisor-torsor-boundary-signs: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Relative torsor representatives and the two boundary signs.

lem-pur-cartier-pair-tensor-addition vs lem-pur-supported-cup-functoriality: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Pullback and symmetry of supported Kummer cup products.

lem-pur-cartier-pair-tensor-addition vs lem-sp-etale-torsor-extension-presentation-exists: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Existence of the free extension presentation of an etale torsor.

lem-pur-cartier-pair-tensor-addition vs lem-sp-relative-torsor-extension: The new assertion identifies product Cartier ideals and their specified sections and proves integral relative H1/Baer addition with support restriction; the existing assertion does not give this framed-pair and integral supported-extension tensor identity. Existing scope: Relative extension class of a torsor with a specified section.

lem-pur-divisor-normalized-realization vs lem-sc-artin-schreier-polynomial-cover: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Surjective etale polynomial cover solving an Artin-Schreier equation.

lem-pur-divisor-normalized-realization vs lem-sc-artin-schreier-scheme-section-data: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Construction of sectionwise Artin-Schreier maps.

lem-pur-divisor-normalized-realization vs lem-sc-artin-schreier-scheme-section-exact: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Exactness from specified Artin-Schreier section data.

lem-pur-divisor-normalized-realization vs lem-sc-artin-schreier-sequence-scheme: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Artin-Schreier short exact sequence for arbitrary schemes.

lem-pur-divisor-normalized-realization vs def-per-closed-support-plus-adjunction: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Bounded-below closed-support right adjoint and its fixed adjunction.

lem-pur-divisor-normalized-realization vs def-per-ordinary-kummer-first-chern: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Ordinary derived Kummer first Chern class.

lem-pur-divisor-normalized-realization vs lem-per-codimension-support-filtration: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Codimension support filtration and local graded complexes.

lem-pur-divisor-normalized-realization vs lem-per-ind-etale-closed-support-base-change: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Ind-etale base change for the closed etale support right adjoint.

lem-pur-divisor-normalized-realization vs lem-per-pure-principal-divisor-kummer-residue: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Localization residues of unit Kummer symbols when divisor purity is given.

lem-pur-divisor-normalized-realization vs lem-per-strict-local-divisor-low-kummer: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Low-degree Kummer cohomology of a strict-local regular divisor complement.

lem-pur-divisor-normalized-realization vs lem-sf-etale-generic-exchange-algclosed: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Geometric-generic closed-support and internal-Hom exchange over arbitrary algebraically closed fields.

lem-pur-divisor-normalized-realization vs lem-sf-etale-generic-immersion-projection: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Projection formula for an immersion extension by zero.

lem-pur-divisor-normalized-realization vs lem-sfb-ramified-cartier-supported-purity: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Ramification multiplicity in the supported Cartier purity comparison.

lem-pur-divisor-normalized-realization vs lem-sfb-stable-relative-picard-kummer: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Relative semiabelian Picard object and smooth Kummer comparison.

lem-pur-divisor-normalized-realization vs lem-sfb-unit-binomial-finite-etale: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Finite etale algebra of a root of a unit.

lem-pur-divisor-normalized-realization vs sk-lem-geo-cartier: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: The cycle class of a Cartier divisor.

lem-pur-divisor-normalized-realization vs def-asd-ordinary-finite-p1-arrows: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Canonical arrows and normalized data for ordinary finite projective-line duality.

lem-pur-divisor-normalized-realization vs def-asd-ordinary-finite-p1-data: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Normalized decomposition and adjunction data for ordinary finite projective lines.

lem-pur-divisor-normalized-realization vs def-asd-ordinary-finite-p1-kummer-class: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Scalar Kummer class of O(1) with finite ordinary etale coefficients.

lem-pur-divisor-normalized-realization vs def-asd-ordinary-supported-kummer-boundary: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Relative supported Cartier Kummer boundary specification.

lem-pur-divisor-normalized-realization vs def-asd-ordinary-supported-kummer-system: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Normalized ordinary supported Cartier Kummer map systems.

lem-pur-divisor-normalized-realization vs def-pur-kummer-line-geometry: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Canonical geometry and maps for the Kummer lines.

lem-pur-divisor-normalized-realization vs lem-asd-ordinary-finite-p1-adjunction: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Ordinary etale projective-line adjunction with arbitrary finite invertible-exponent coefficients.

lem-pur-divisor-normalized-realization vs lem-asd-ordinary-supported-chern-normalization: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Ordinary Chern realization of a normalized supported class.

lem-pur-divisor-normalized-realization vs lem-asd-ordinary-supported-kummer: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Supported Cartier Kummer map for ordinary etale arbitrary finite coefficients.

lem-pur-divisor-normalized-realization vs lem-asd-supported-kummer-support-hom-naturality: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Naturality of the supported Hom identification under base change.

lem-pur-divisor-normalized-realization vs lem-pur-kummer-finite-biproducts: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Integral finite-basis cohomology and Kummer exactness.

lem-pur-divisor-normalized-realization vs lem-pur-kummer-finite-free-comparison: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Normalized finite free Kummer cohomology comparison.

lem-pur-divisor-normalized-realization vs lem-pur-kummer-integral-root-comparison: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Integral basis reduction for the Kummer root sheaf.

lem-pur-divisor-normalized-realization vs lem-pur-kummer-root-line-computation: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Roots-of-unity computation on the two lines.

lem-pur-divisor-normalized-realization vs lem-pur-supported-cup-functoriality: The new assertion is the normalized integral-to-A Ext and pro-etale supported realization for an arbitrary framed line bundle on an arbitrary closed support; the existing assertion does not construct this general framed-line realization with its unique module lift and support/forgetting compatibilities. Existing scope: Pullback and symmetry of supported Kummer cup products.

lem-pur-principal-torsor-yoneda-sign vs def-sc-torsor-extension-presentation: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Canonical extension presentation of an etale torsor.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-contracted-product-exists-data: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Translation torsor structure on the explicit sheafified orbit quotient.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-contracted-product-exists-universal: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Universal property of the explicit sheafified orbit quotient.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-contracted-product-exists: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Existence of the contracted product of an etale torsor.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-inverse-image-lifting-torsor: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Inverse image of a lifting torsor.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-inverse-image-lifts-fibre: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Underlying lifting-fibre comparison for etale inverse image.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-torsor-h1-functoriality: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Functoriality of the etale torsor classification of H1.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-torsor-inverse-image-extension: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Inverse image of the torsor extension.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-etale-torsor-pushout-extension: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Pushout of the etale torsor extension.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-ext-epi-effacement: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Individual positive Ext classes are killed by an epimorphism.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-extension-presentation-generator-fibre: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Generators identify the fibre.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-extension-presentation-short-exact: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Short exactness of extension presentation.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-presheaf-free-ext-local-killing-witness: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Yoneda witness for local Ext killing.

lem-pur-principal-torsor-yoneda-sign vs lem-sc-presheaf-free-ext-local-killing: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Positive Ext classes from free abelian sheaves are killed by presheaf covers.

lem-pur-principal-torsor-yoneda-sign vs new-etale-torsor-inverse-image-extension-core: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Extension core after inverse-image torsor transport.

lem-pur-principal-torsor-yoneda-sign vs new-etale-torsor-inverse-image-torsor: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Inverse-image torsor and equivariance.

lem-pur-principal-torsor-yoneda-sign vs lem-per-supported-yoneda-localization: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Yoneda coefficient splice versus the signed localization boundary.

lem-pur-principal-torsor-yoneda-sign vs lem-weil-pbc-ext-one-extension-classification: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Degree-one derived classes classify short exact extensions.

lem-pur-principal-torsor-yoneda-sign vs lem-weil-pbc-finite-etale-equivalence-h1: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Finite etale pullback equivalence implies finite constant H1 comparison.

lem-pur-principal-torsor-yoneda-sign vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: First constant cohomology vanishes on closed subschemes of the spectrum of a normal domain with separably closed fraction field (Stacks 09ZB).

lem-pur-principal-torsor-yoneda-sign vs def-coef-yoneda-extension-data: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Concrete finite Yoneda extensions and their operations.

lem-pur-principal-torsor-yoneda-sign vs def-coef-yoneda-recursive-class: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Cokernel cuts and the concrete signed extension class.

lem-pur-principal-torsor-yoneda-sign vs lem-coef-yoneda-class-classification: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Surjectivity and equality detection of the concrete class.

lem-pur-principal-torsor-yoneda-sign vs lem-coef-yoneda-class-naturality: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Naturality of the concrete extension class.

lem-pur-principal-torsor-yoneda-sign vs lem-coef-yoneda-class-splice: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: The signed splice identity for the concrete class.

lem-pur-principal-torsor-yoneda-sign vs lem-coef-yoneda-derived-ext-comparison: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Yoneda extensions and derived Ext in every positive degree.

lem-pur-principal-torsor-yoneda-sign vs def-amb-relative-etale-cohomology: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Resolution model of relative etale cohomology and its cone maps.

lem-pur-principal-torsor-yoneda-sign vs def-amb-torsor-with-section: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Torsors with a specified section and their isomorphism classes.

lem-pur-principal-torsor-yoneda-sign vs lem-amb-framed-lifts-classification: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Pointed lifting torsors modulo global translation.

lem-pur-principal-torsor-yoneda-sign vs lem-amb-relative-cocycle-coordinates: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Concrete first homology coordinates for the relative restriction cone.

lem-pur-principal-torsor-yoneda-sign vs lem-amb-relative-torsor-class-naturality: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Equivariant naturality of framed relative torsor classes.

lem-pur-principal-torsor-yoneda-sign vs lem-amb-relative-torsor-cohomology: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Relative first cohomology and torsors with a specified open section.

lem-pur-principal-torsor-yoneda-sign vs lem-amb-relative-torsor-forget-normalization: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Ordinary normalization of the framed relative cocycle.

lem-pur-principal-torsor-yoneda-sign vs lem-pur-divisor-torsor-boundary-signs: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Relative torsor representatives and the two boundary signs.

lem-pur-principal-torsor-yoneda-sign vs lem-sp-etale-torsor-extension-presentation-exists: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Existence of the free extension presentation of an etale torsor.

lem-pur-principal-torsor-yoneda-sign vs lem-sp-relative-torsor-extension: The new assertion identifies the specified-section torsor extension itself with the inverse-section localization pushout and then computes its splice; the existing assertion does not make this identification for an arbitrary globally framed relative torsor. Existing scope: Relative extension class of a torsor with a specified section.

lem-pur-smooth-codimension-one-cartier vs lem-sc-effective-cartier-affine-dimension-drop: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Dimension drop for a principal Cartier subscheme of an affine variety.

lem-pur-smooth-codimension-one-cartier vs lem-sc-principal-quotient-dimension-full-height: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Principal quotient dimension at a prime of full height.

lem-pur-smooth-codimension-one-cartier vs lem-sc-tsen: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Tsen's theorem.

lem-pur-smooth-codimension-one-cartier vs lem-zl-bertini-finite-cover-irreducible-system: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: General divisors irreducible simultaneously on a finite etale cover.

lem-pur-smooth-codimension-one-cartier vs lem-weil-pbc-dimension-quotient-nonzerodivisor: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Dimension drops by one modulo a nonzerodivisor of the maximal ideal.

lem-pur-smooth-codimension-one-cartier vs lem-weil-pbc-global-complete-intersection-equidimensional: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: A global complete intersection has the expected dimension at every point.

lem-pur-smooth-codimension-one-cartier vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: The equations of a global complete intersection form a regular sequence at every prime.

lem-pur-smooth-codimension-one-cartier vs lem-weil-pbc-noetherian-height-quotient-bound: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Height drops by at most the number of equations (Krull).

lem-pur-smooth-codimension-one-cartier vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Dimension lower bound for a polynomial quotient over a field.

lem-pur-smooth-codimension-one-cartier vs lem-weil-pbc-regular-sequence-dimension-at-point: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Dimension at a point cut out by a local regular sequence.

lem-pur-smooth-codimension-one-cartier vs lem-sbc-depth-two-punctured-principal-slice-connected: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Connected depth-two puncture with nonempty principal slice.

lem-pur-smooth-codimension-one-cartier vs lem-pur-etale-near-regular-coordinate-fibre: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Etaleness near a regular coordinate fibre.

lem-pur-smooth-codimension-one-cartier vs lem-pur-relative-support-bottom-descent: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Descent in the bottom supported degree of a smooth pair.

lem-pur-smooth-codimension-one-cartier vs lem-pur-relative-support-coordinate-model: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Geometric normal-slice comparison for supported cohomology.

lem-pur-smooth-codimension-one-cartier vs lem-pur-relative-support-vanishing: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Lower supported-degree vanishing for a smooth pair.

lem-pur-smooth-codimension-one-cartier vs lem-pur-smooth-closed-coordinate-lift: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Lifting coordinates from a smooth closed subscheme.

lem-pur-smooth-codimension-one-cartier vs lem-pur-smooth-pair-local-coordinates: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Local coordinates for a closed immersion of smooth schemes.

lem-pur-smooth-codimension-one-cartier vs lem-pur-smooth-pair-regular-immersion: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Local regular equations for a closed immersion of smooth schemes.

lem-pur-smooth-codimension-one-cartier vs def-trf-etale-coordinate-flag: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Simultaneous etale coordinate flags with a labelled boundary.

lem-pur-smooth-codimension-one-cartier vs lem-trf-marked-controlled-blowup-charts: The new conclusion is a one-generator nonzerodivisor ideal for a smooth pair with local dimension drop one; the existing statement supplies a coordinate/regular-sequence or algebraic dimension input, not that combined Cartier conclusion. Existing scope: Controlled transforms in smooth marked blowup charts.

lem-pur-divisor-normalized-realization vs lem-amb-cartier-kummer-map: The existing map is attached to a Cartier divisor; the new theorem includes arbitrary closed support and arbitrary framed line bundles, plus the unique Ext-normalized scalar realization.

lem-pur-divisor-normalized-realization vs lem-asd-cartier-boundary-existence: The existing unique supported-boundary class is for an effective Cartier immersion and its dual ideal. The new comparison is for every framed line bundle and explicitly includes site, coefficient and enlargement maps.

lem-pur-divisor-normalized-realization vs lem-pur-divisor-relative-cone: The existing theorem identifies derived support and relative cones for abelian sheaves. It does not construct the framed torsor extension, its uniquely scalar-realized Kummer class or its Chern normalization.

lem-pur-principal-torsor-yoneda-sign vs lem-per-supported-yoneda-localization: The existing statement starts with e_h already defined as a pushout and computes its positive splice. The new statement identifies beta(P,s) as e_{-g}; this is the relative framed-torsor comparison the item needs.

lem-pur-cartier-pair-tensor-addition vs lem-per-noetherian-supported-product-calculus: The existing theorem treats finite Z/ell^n supported Chern classes on Noetherian schemes. The new theorem is integral degree-one relative/Baer addition, on every scheme, with section-preserving product-ideal data.

lem-pur-cartier-pair-tensor-addition vs lem-pur-kummer-additivity: The existing theorem proves ordinary c1 addition after Kummer. The new theorem is about framed relative pairs and integral H1/Ext1 classes before Kummer and before forgetting support.

lem-pur-cartier-pair-tensor-addition vs lem-sc-line-bundle-torsor: The existing equivalence carries unframed tensor products to contracted products. The new result includes Cartier canonical sections, the common complementary open and the relative integral/Baer equality.

## Preservation of all returned arguments

This is the task allocation, not an additional proof list in any unsplit node. Steps 1, 2–5, 6 and 7 have comparable independent proof burdens (1291; 2752; 1223; 1914 characters of the returned argument respectively); step 8 is the 692-character forgetting comparison appended to the realization task.

- Old step 1 -> lem-pur-smooth-codimension-one-cartier. Keep the finite-type Noetherianity check, coordinate regular sequence, Noetherian successive quotients and all dimension-drop/codimension cancellation arguments.
- Old steps 2–5 -> lem-pur-divisor-normalized-realization. Keep the canonical Cartier section construction, torsor-with-section classification and equation independence, normalized relative extension, Kummer splice, scalar adjunction and exact site/coefficient comparison. The general framed-line statement specializes to this construction.
- Old step 6 -> lem-pur-principal-torsor-yoneda-sign. Keep F(tau)=0, tau=g*e, F(e)=-a(g), the inverse-unit pushout, the Yoneda splice and signed-cone comparison. The smooth frame equality is then the definition of the frame class.
- Old step 7 -> lem-pur-cartier-pair-tensor-addition. Keep the nonzerodivisor product, ideal/tensor multiplication, section-preserving frame-torsor contraction, finite-product classification, coefficient multiplication, cone restriction maps and connecting-map naturality. Application of the additive realization is assembly.
- Old step 8 -> the forget-support conclusion of lem-pur-divisor-normalized-realization; identify its ordinary class with the statement’s c1 in assembly.

### Exact text of the returned eight steps

Old step 1 (1291 characters):

Apply [lem-pur-smooth-pair-local-coordinates] to $D\hookrightarrow T$ over $B$. The ambient finite-type setting is explicitly that of [sk-def-purity-conv]. Thus $T$ and $D$ are finite type over $k$, hence locally Noetherian by [lem-weil-pbc-finite-type-over-noetherian] applied to $\operatorname{Spec}k$ (a field has just the two ideals $0,k$, so its spectrum is Noetherian). At a point $y\in D$, the coordinate chart gives a regular sequence $f_1,\ldots,f_b$ in $R=\mathcal O_{T,y}$ defining $\mathcal O_{D,y}$. Each $f_j$ lies in the maximal ideal of its successive quotient and is a nonzerodivisor there. The successive quotients remain Noetherian, since their ideals correspond to ideals of $R$ containing the quotient ideal, and the images of generators generate. Apply [lem-weil-pbc-dimension-quotient-nonzerodivisor] successively to obtain $\dim R=\dim\mathcal O_{D,y}+b$. The pure-codimension convention in [def-pur-frame-class] says the difference is one, so $b=1$. Thus locally $\mathcal I_D=(f)$ with $f$ a nonzerodivisor; off $D$ the ideal is the unit ideal. This proves that $D$ is Cartier and that one-function frames exist, without presuming regularity of the base. We will construct the global class rather than infer a global cohomology class from equality of local classes.

Cited nodes: lem-pur-smooth-pair-local-coordinates, def-pur-conventions, sk-def-purity-conv, def-pur-frame-class, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-dimension-quotient-nonzerodivisor.

Source: literature/stacks-project/more-morphisms.tex; Tag 0FUE, lemma-etale-local-structure, applied to the first sentence of the blueprint proof.

Old step 2 (550 characters):

For any effective Cartier divisor $E$ put $L_E=\mathcal I_E^\vee$ as in [def-pc-divisor-line-bundle]. On a chart $\mathcal I_E=(f_a)$ write $e_a=f_a^{-1}$ for the dual basis, and put $s_E=f_ae_a$. On overlaps $e_b=(f_a/f_b)e_a$, so $f_be_b=f_ae_a$: these sections glue. On $W=T\setminus E$ this section is nowhere zero and gives a specified trivialization $\tau_E:\mathcal O_W\simeq L_E|_W$. By [lem-sc-line-bundle-torsor], $P_E=\underline{\operatorname{Isom}}(\mathcal O_T,L_E)$ is a $\mathbf G_m$-torsor, with the specified section $\tau_E$ on $W$.

Cited nodes: def-pc-divisor-line-bundle, lem-sc-line-bundle-torsor.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md; First sentence and final paragraph; canonical section on the complement.

Old step 3 (616 characters):

Use [lem-amb-relative-torsor-cohomology] for $G=\mathbf G_m$ to obtain $\alpha_E=[(P_E,\tau_E)]\in H^1(T,W;\mathbf G_m)$. Its forgotten-support image is $[P_E]$. This is a specified class, not an arbitrary lift of a Picard class. Replacing $f_a$ by $u_af_a$ changes $e_a$ to $u_a^{-1}e_a$ and leaves $s_E$ unchanged. Thus the pair and its relative class are independent of all local equations. In the Yoneda realization use the relative extension specified in [def-asd-ordinary-supported-kummer-boundary], with lifting torsor $P_E$ over one and with $\tau_E$ sent to zero; this fixes the sign of its extension class.

Cited nodes: lem-amb-relative-torsor-cohomology, def-asd-ordinary-supported-kummer-boundary.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md; First sentence: global well-definedness via a torsor with its specified section.

Old step 4 (872 characters):

Put $m=\ell^n$, invertible on $T$ and killing $A$ by [def-pur-frame-class]. The pair of step 3 gives the extension $0\to\mathbf G_m\to\mathcal E\to i_*\mathbf Z_E\to0$ specified in [def-asd-ordinary-supported-kummer-boundary]. Its Yoneda product with the Kummer extension of [lem-amb-kummer-any-base], followed by the roots coefficient map, is the relative Kummer construction in the recorded extension convention. Scalar adjunction gives its unique $A$-linear supported class. Pulling the extension back along $\mathbf Z_T\to i_*\mathbf Z_E$ gives the ordinary extension whose lifting torsor is $P_E$. The torsor classification [lem-sc-line-bundle-torsor] therefore gives ordinary class $\delta_T([P_E])$ with positive sign. This agrees with the forget-support requirement of [lem-amb-relative-torsor-cohomology]. No tensor over $\mathbf Z/m$ is imposed on $\mathbf G_m$.

Cited nodes: def-pur-frame-class, lem-amb-kummer-any-base, lem-amb-relative-torsor-cohomology, def-asd-ordinary-supported-kummer-boundary, lem-sc-line-bundle-torsor.

Source: literature/stacks-project/etale-cohomology.tex; Tag 03PL, lemma-kummer-sequence; relative connecting construction from the blueprint final paragraph.

Old step 5 (714 characters):

Use [lem-pur-divisor-relative-cone] and [def-pur-support-cohomology] to identify relative and supported cohomology and their etale/pro-etale comparisons. Realize the class of step 4 in the supported Ext presentation of [def-asd-ordinary-supported-kummer-boundary], retaining its Yoneda normalization. Apply the coefficient map $\sigma_T\rho_T:\nu_T^{-1}\mu_m^{\mathrm{et}}\to A(1)_T$ of [def-pur-frame-class] and canonical site comparison to obtain $\operatorname{cl}(E)$. These are additive and commute with etale restriction, forgetting support and support enlargement. The cone model must not be substituted for this extension normalization without checking the connecting-map sign; step 6 computes it directly.

Cited nodes: lem-pur-divisor-relative-cone, def-pur-frame-class, def-pur-support-cohomology, def-asd-ordinary-supported-kummer-boundary.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md; Support boundary and final paragraph; comparison performed on both terms of the relative cone.

Old step 6 (1223 characters):

Etale pullback takes the Cartier ideal, its dual and canonical section to the corresponding data for $E_U$, so naturality in [lem-amb-relative-torsor-cohomology] identifies the restricted pair. Write $e=f^{-1}$ for the dual frame on $U$, and $g=f|_{U_f}$. The action in [lem-sc-line-bundle-torsor] gives $\tau=g\cdot e$. For the equivariant torsor map $F$ into the extension of [def-asd-ordinary-supported-kummer-boundary], $0=F(\tau)=a(g)+F(e)$, hence $F(e)=-a(g)$. Thus this extension is the pushout of $0\to j_!\mathbf Z_{U_f}\to\mathbf Z_U\to i_*\mathbf Z_{E_U}\to0$ along $1\mapsto g^{-1}$. Yoneda composition with the Kummer extension gives $\partial\delta(g^{-1})=-\partial\delta(g)$. The coefficient and comparison maps of step 5 give $\operatorname{cl}(E)|_U=-\partial\kappa(f)$. The cone formula of [lem-pur-divisor-torsor-boundary-signs] instead uses $D(a,b)=(da,\operatorname{res}a-db)$, with localization $b\mapsto(0,-b)$ and relativeConnecting anticommutes with localization. Its positive cone calculation is not the Yoneda extension normalization. For smooth $E=D$, the resulting class is minus the rank-one frame class of [def-pur-frame-class], independently of the equation by [lem-pur-frame-independence].

Cited nodes: lem-pur-divisor-torsor-boundary-signs, lem-amb-relative-torsor-cohomology, def-pur-frame-class, lem-pur-frame-independence, def-asd-ordinary-supported-kummer-boundary, lem-sc-line-bundle-torsor.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md; Clause (a), with explicit relative-cone boundary calculation.

Old step 7 (1914 characters):

For $E=D_1+D_2$ let $\mathcal I_E=\mathcal I_{D_1}\mathcal I_{D_2}$. On simultaneous Cartier charts $f_1f_2$ is a nonzerodivisor because both factors are, so $E$ is Cartier even when it is not smooth; its complement is $W=T\setminus(|D_1|\cup|D_2|)$. Multiplication identifies the ideal tensor product with the product ideal on these bases, hence $L_E\simeq L_{D_1}\otimes L_{D_2}$, carrying $s_E$ to $s_{D_1}\otimes s_{D_2}$. The frame torsor is therefore the contracted product by [lem-sc-line-bundle-torsor], including its specified section over $W$. To see addition in relative $H^1$ from precisely the stated naturality of [lem-amb-relative-torsor-cohomology], take the product torsor for $\mathbf G_m\times\mathbf G_m$ and its pair of sections. The two projections give $(\alpha_{D_1},\alpha_{D_2})$ in relative cohomology, since the two-term restriction cone commutes with finite products. Push out along multiplication $\mathbf G_m\times\mathbf G_m\to\mathbf G_m$: on these additive cohomology groups it is addition, and on torsors it is their contracted product. Thus $\alpha_E=\alpha_{D_1}+\alpha_{D_2}$ in $H^1(T,W;\mathbf G_m)$. For $W\subseteq W_i=T\setminus|D_i|$ the restriction square gives the chain map $(a,b)\mapsto(a,b|_W)$ of signed cones; by the representative $(a,h(s))$ of [lem-pur-divisor-torsor-boundary-signs] it sends $\alpha_{D_i}$ to the class of $(P_{D_i},\tau_{D_i}|_W)$, which is this enlargement of support. On the split cone sequences of the Kummer resolutions it is a morphism of short exact sequences, so it commutes with the relative connecting maps by [lem-weil-pbc-complex-ses-long-exact-naturality], and with the comparison and coefficient maps by step 5. The connecting and coefficient maps of steps 4-5 are homomorphisms, so their images give the required equality in $H^2_Z(T,A(1))$. This proves global additivity without a local-to-global injectivity claim for $H^2_Z$.

Cited nodes: def-pc-divisor-line-bundle, lem-sc-line-bundle-torsor, lem-amb-relative-torsor-cohomology, lem-pur-divisor-torsor-boundary-signs, lem-weil-pbc-complex-ses-long-exact-naturality.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md; Clause (b), addition; correcting the source two-function frame to the product equation.

Old step 8 (692 characters):

Finally, step 4 gives $\operatorname{forget}(\beta_D)=\delta_T([P_D])$. Step 5 commutes with forgetting support, so $\operatorname{forget}(\operatorname{cl}(D))$ is the ordinary Kummer boundary of the frame-torsor class of $L_D=\mathcal O_T(D)$, followed by exactly the same roots coefficient morphism. This is $c_1(\mathcal O_T(D))$ by the definition in the statement. The torsor interpretation of the line bundle is [lem-sc-line-bundle-torsor], and the compatibility of the relative connecting map with forgetting is the explicit last assertion of [lem-amb-relative-torsor-cohomology]. The equality holds globally; it is not deduced from restriction of ordinary $H^2$ to trivializing opens.

Cited nodes: lem-sc-line-bundle-torsor, lem-amb-relative-torsor-cohomology, def-pur-frame-class.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md; Final paragraph: forget-support comparison with the ordinary Kummer connecting class.

## General framed-line proof obligations retained for subsequent workers

The realization theorem is obtained by the relative extension of the framed torsor, then the Kummer Yoneda product, then roots scalar change. For the uniqueness assertion, i_*Z_Z is flat as a sheaf of abelian groups (its geometric stalks are Z or zero), so A tensor-derived i_*Z_Z is i_*A_Z. Derived scalar adjunction therefore gives the actual unique module Ext lift; no divisibility or flatness of A over Z/m is assumed. The closed-support Hom/relative comparison and the canonical site pullbacks are applied to both terms of restriction. The extension-normalized choice, not the raw lifting cocycle, fixes the sign; pulling back along Z_T->i_*Z_Z recovers the ordinary torsor extension. Additivity is the additivity of Yoneda composition and roots maps. This generalized argument uses existing generic ingredients lem-sp-relative-torsor-extension, lem-amb-closed-support-hom, lem-pur-divisor-relative-cone, lem-asd-supported-kummer-support-hom-naturality and the ordinary Kummer sequence, not the item as a prerequisite.

The principal-torsor theorem compares two explicitly given extensions, via the global frame lift and the universal property of the localization pushout; its splice then uses lem-per-supported-yoneda-localization with h=-g. It is a relative-extension comparison, not a claim that equality after forgetting support suffices.

The tensor theorem first compares the actual paired Cartier line bundles; for relative H1, form the product G_m x G_m torsor with its pair of open sections. Projection gives the two component relative classes. Pushout by multiplication gives their sum and the contracted-product pair. The corresponding extension addition is Baer addition: on the fibre product of extensions, add the two frame maps; the tensor section maps to zero. Naturality for W contained in W_a uses the displayed chain map and the functorial short-exact-sequence connecting map.

## Checks

Required dry run and push are recorded by the delivery command. The statement of the item remains byte-for-byte equal as a string to the current item copied at startup. All new nodes have three kinds of genuinely logged searches, with second semantic phrasings, and no proof steps. No files outside this sandbox were written.
