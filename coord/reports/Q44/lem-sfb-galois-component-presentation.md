## Worker report

This repairs the human re-split return of 2026-10-22 for Q44. Only stage 1 is delivered.
The sandbox initially contained only dispatcher brief markers, with no delivered node,
report or search log. I copied the current repository item, which carries the complete
returned ten-step argument and stage-2 metadata; I read the available NL report too.
The required initial dry run of that copied split exited with the expected diagnostic
that report.md / Review by Q44 was absent. No prior local work was discarded. The
current repository statement, statement dependencies and Lean record are retained.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-galois-component-presentation.json: existing item, split; unchanged statement, three-step assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-galois-geometrically-integral-splitting.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-galois-clopen-component-cover.json: new statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-open-faithful-cartier.json: new statement, unsplit; no Mathlib match.
- report.md and citations.json: report and verbatim per-step citation quotes.

## Attachments

None. I searched lean/WeilConjectures by the exact blueprint tag and Galois/component
notions, and searched lean/Sheaf as well. AlgebraicGeometry.exists_galois_component_presentation
in lean/Sheaf/AlgebraicGeometry/GaloisComponentPresentation.lean:99 has `by sorry`
at the end of its proof. It is no attachment. The normal-component and generic-splitting
modules cover ingredients, not any of the three new complete statements. I wrote no
Lean and ran no compiler, Lake or build command.

## WANTED

None. The sources needed here are present.

## Return repaired

1. The returned 7813-character proof is distributed into THREE independent work items,
   not moved into one node: geometric splitting takes old steps 1--4 (2834 characters),
   component covers and geometric fibres take steps 6--8 (2982), and semilinear action
   with stable boundary takes steps 5,9,10 (1997). All three are statement-only,
   status unsplit, with empty proof and proof_deps and null proof_origin. Their
   arguments are preserved verbatim below for their future workers. Each introduces
   all its own objects and can be claimed separately without proving the parent.
2. The parent keeps its exact statement and is now a short assembly of those three
   nodes. It has 1113 characters of proof text, below the 3000-character cap.
   It verifies the hypotheses, selects X, identifies the exact stabilizer, and uses
   etale implies flat before applying the third node. No original argument was
   shortened into an unsupported assertion or dropped.
3. The work items have comparable proof assignments. The first does not require
   properness except in its explicitly conditional properness clause, and gives
   all components rather than one; it contains no group-orbit or Cartier conclusion.
   The second assumes a fixed Galois extension and an existing clopen decomposition;
   it constructs neither the splitting field nor geometrically integral components,
   and makes no normality, properness, faithfulness or boundary assertion. It also
   exposes the full scalar-extension fibre and its simply transitive action, which
   is the intermediate calculation used to deduce stabilizer orbits. The third
   applies to any field extension and any nonempty stable open with flat projection;
   it constructs the semilinear action, proves faithfulness and preserves the Cartier
   ideal. It chooses no extension, component or cover and asserts no fibre orbits.
   Thus none is the original statement or a relabelled copy of its full content.

## Sources and the unit route

I read GOAL.md, the three fixed/conditional/free levels of SETUP.md, the worker
brief, stages/1-dag.md, and delivery-errors B--E whole, as well as the chapter and
sk-thm-sf-ctf-stability unit record. The inherited route is
`det-thm-sf-ctf-stability-direct-images`, proof (3), through the alteration chain.
I read ILO, Travaux de Gabber, Expose X, 2.3 Steps 1--2, printed p.150 (PDF p.156).
Step 1 gives the normal, proper, integral, geometrically reduced reduction; Step 2
chooses the finite Galois field, component and decomposition subgroup, applies 2.2
to the component and pulled-back boundary, and states the component transitivity.
The repair stays on that route, without SGA sources.

For the first new node I read Stacks varieties.tex Tag 054R,
lemma-finite-extension-geometrically-irreducible-components (lines 1848--1867):
locally finite type and finitely many components give a finite separable splitting
field. I read algebra.tex Tag 033C, lemma-normal-goes-up (46563ff): smooth maps
preserve normality; the existing normal-component node supplies its etale-scheme
form. Noetherianity is supplied by the existing finite-type-over-Noetherian node.
I checked the statements of the Galois-envelope, separable residue-extension,
finite/separable spectrum, finite base-change and etale-cover base-change nodes
used by the retained argument. The field tower L -> e_0 -> E preserves the
geometric irreducibility; geometric reducedness supplies reducedness of every
B_E. The clopen pieces are therefore integral, and their disjointness identifies
them with the components. The conditional properness conclusion uses precisely
proper base change and closed-immersion-proper clause (c), whose statements I read.
No perfection, geometric normality or projectivity assumption is substituted.

For the second new node I read ILO's transitivity sentence and Stacks pione.tex
Tag 03SF, section-finite-etale-under-galois, especially 1354--1365, which explains
transitivity on the geometric fibre of connected Galois covers. Here the full
scalar extension can be disconnected, so I retain the explicit tensor computation
of old step 7 rather than apply that connected-cover criterion to Y. I opened
lem-exc-finite-galois-tensor-decomposition and used only its clause (1), not the
sheaf-sections clause (2). I also read the affine-spectra fibre-product statement,
the algebraic-extension embedding statement and surjective base change. The
formula is c tensor b |-> (c i(a(b)))_a; tensor extension of a finite product is
verified by its orthogonal idempotents, and a prime chooses exactly one coordinate.
For each component, its finite etale image is a nonempty clopen of integral B,
so it is surjective. Every component meets any fixed geometric fibre. An element
carrying one point to another carries their components to each other because the
components are disjoint. Restricting this argument to a fixed component gives
its stabilizer orbit, retaining field embeddings rather than just points of Y.
For independent future work on this node, p is finite etale surjective directly
from the finite separable field extension and the same base-change tools as old
step 3; it need not use the first new node.

For the third new node I read ILO's application of 2.2 to (Y_0/S_0,Z_0 intersect Y_0)
and Stacks divisors.tex Tag 02OO, lemma-pullback-effective-Cartier-defined,
case (6), including its proof at 2630--2631. I read the actual fibre-product
universal property and the flat-Cartier-pullback node: the latter states that the
pulled-back ideal is locally generated by the image of the same nonzerodivisor.
The universal property gives alpha_h alpha_k = alpha_(hk) with inverse scalars,
and permits restriction to an invariant open. Nonemptiness supplies a residue
field into which L injects, so an identity scheme action forces the scalar
automorphism to be the identity. Flatness is precisely what makes the pulled-back
equations nonzerodivisors. The equality u r_h = u then gives equality of the
Cartier ideals, including their multiplicities. It is not a claim of faithfulness
on the underlying topological space (Spec L would refute that).

## Searches and blueprint alignment

For each new node I searched the whole DAG by source tags and by the relevant
concepts before creating it, and read the matching statements. I ran
`tools/blueprint_refs.py search` for Galois component, geometrically integral,
054R, 033C, 03SF, Galois clopen, semilinear faithful and 02OO. No imported blueprint
node states one of these complete results. The existing generic component splitter,
normal etale component lemma, field torsor classification, affine fixed-puncture
descent results and flat Cartier pullback lemma have the distinctions listed below.
`tools/blueprint_refs.py ancestor lem-sfb-galois-component-presentation` prints None
for this inherited broken creation chain. I retained the item's null ancestor and
explicit source place/via, and gave each child that computed ancestor and the
item followed by the inherited via list. Each child has same_as = [], explicit
source-place assignment, chapter and unit inherited from the item.

All Mathlib searches used msearch.py; their exact queries and returned summaries
are in each node and searches.jsonl. Each node has LeanFinder in two phrasings,
Loogle, source grep and LeanSearch. The component-cover LeanSearch hit the service
rate limit and is recorded unavailable, with no claim of no-match for that call.
The working LeanFinder and Loogle searches cover it. The first node also has a
second source grep. I read the signatures returned by both semantic searches.
For the geometric splitter, the normalization instances do not construct any
splitting field; GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
(Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean:74) and
Scheme.Hom.irreducibleComponentsEquiv (Geometrically/Irreducible.lean:89) do not
split components or establish their geometric integrality. For the cover node,
Ideal.isPretransitive_of_isGaloisGroup and exists_smul_eq_of_isGaloisGroup
(Mathlib/NumberTheory/RamificationInertia/Galois.lean:127,132) concern prime ideals
of a ring extension; the scheme construction, canonical action, scalar-extension
fibre identification and clopen-component restriction are further arguments.
Algebra.Etale.iff_exists_algEquiv_prod only classifies etale field algebras. None
is a one-line specialization giving the whole new statement. For the third node,
Module.FaithfullyFlat.faithfulSMul is faithfulness of a scalar module action,
not a semilinear subgroup acting on a scheme, and Scheme.SpecToEquivOfField only
classifies field-valued points. IsSMulRegular.of_flat_of_isBaseChange is a useful
algebra ingredient, not the faithful action and invariant Cartier ideal assertion.
Consequently all three remain unsplit, with mathlib_match null and no Mathlib leaves.

## Review by Q44

I reopened the parent, the three new statements, their sources and every statement
the three assembly steps cite. This is my author's self-review; independent review
belongs to the maintainer. The source/hypothesis checks are detailed above.

Assembly step 1 cites lem-sfb-galois-geometrically-integral-splitting. Its statement
expressly gives Noetherian B_F (hence B), a finite Galois e_0/e, all clopen normal
geometrically integral components and the conditional properness of those components.
All its assumptions are present in the parent; B is proper, so its final condition
is met. Choosing one component uses the asserted finite nonempty decomposition.
Nothing is borrowed from a proof of that new node, which has no proof yet.

Assembly step 2 cites lem-sfb-galois-clopen-component-cover. Its exact hypotheses
are a finite Galois extension, a nonempty integral base scheme and a finite disjoint
clopen component covering of the scalar extension. Step 1 supplies those. Its
statement defines the same canonical inverse-scalar action and exact stabilizer,
and expressly gives component transitivity, finite etale surjectivity and the
nonempty stabilizer geometric-fibre orbit. It does not assume a torsor property
that the parent is supposed to prove.

Assembly step 3 cites def-weil-etale-morphism and
lem-sfb-semilinear-open-faithful-cartier. I checked that the definition actually
includes flatness (not merely a slogan about unramified maps). X is a nonempty
open and is H-stable by the exact stabilizer in step 2. These and u flat are all
the third node needs; it supplies the restricted action, both projection laws,
faithfulness on X and the field, invariance of u, and the ideal-level stable
Cartier pullback with the correct inverse-image support. The parent makes no
additional assertion about an arbitrary alteration. citations.json quotes a
verbatim part of each of the four cited statements (the whole statement), one
entry for every step/node pair. proof_deps is exactly the union of uses. All
three assembly steps are non-elementary invocations, not hidden long proofs.

B1--B10: every child is genuinely unsplit with no proof or proof_deps; its statement
introduces its fields, scheme, map and group, defines normality/Noetherianity or
faithfulness inline when used, and cites its geometric, flat, Cartier and morphism
notions. I caught that def-pc-field-tower does not itself define normal field
extensions: the two Galois children now spell out finite-dimensional, separable
(with its definition node), and normal (with the polynomial-splitting meaning).
The TeX has a single semantic backslash layer. Sources use ILO and actual Stacks
tags/labels, without section-number-only references or forbidden SGA material.
No search was invented, and the unavailable service is explicitly unavailable.
No closed project declaration states any child, and no node is a special case
of a previously existing statement. The shared-tag comparisons follow below.

C1--C8 and D1--D5: the parent's only proof citations are its three new work items
and the etale definition. Each cited statement explicitly contains the fact taken
from it. No proof internals are cited, no lemma is proved and cited in the same
step, and no child refers back to the parent. The existing component-splitting,
normal-component, tensor and Cartier facts remain reusable ingredients in the
preserved future-work arguments below. They have not been copied into new nodes.
The route stays within the inherited unit, and no new maintainer tool_uses field
is added; inherited maintainer-owned metadata is left to the delivery overlay.

E1--E7: I tested (a) e_0=e and geometrically integral B, yielding X=B and trivial
stabilizer; (b) B=Spec K with K/e finite separable and e_0 a Galois closure,
where the components are Spec e_0 and H=Aut_K(e_0), with the expected field-valued
fibre orbits; (c) B geometrically integral but an arbitrary finite Galois e_0,
where H=A and the action remains faithful as a scheme action; (d) imperfect base
fields, where geometric reducedness is essential and only a separable splitting
extension is used; (e) X=Spec L for the third node, whose one-point topology does
not make its scheme automorphisms trivial; (f) empty Cartier divisor, with unit
ideal and empty support; (g) B empty, correctly excluded from the first two and
incompatible with the nonempty-open hypothesis of the third. The third node
also works without normality, properness, integrality or algebraicity, because
only nonemptiness and field injection prove faithfulness and only flatness is
needed for the Cartier argument. All hypotheses apply to the actual base-change
projection and component, not a different fibre product. No statement dispute,
source error or target change was found.

The repair addresses the one numbered return in full: three new queue items,
all original arguments retained, short parent assembly, honest logged searches,
verbatim citations, complete review, followed by the required server dry run and
push. No mathematical task remains unfinished in this stage-1 split; the three
children intentionally await their own independent stage-1 workers.

## Not duplicates

- lem-sfb-galois-geometrically-integral-splitting vs lem-fin-etale-normal-components: it supplies normal integral clopen components but neither a Galois splitting field nor geometric integrality or conditional properness.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sbc-components-finite-separable-descent: it descends components only from a fixed separable closure and explicitly asserts no arbitrary-extension geometric irreducibility.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sbc-dvr-generic-galois-normalization: the existing statement concerns Finite normal relative normalization of a generic Galois cover over a DVR; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sbc-generic-components-split: it gives a finite etale field with geometrically irreducible topological components, not a Galois field with normal integral clopen components and properness.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sbc-stalk-normalization-boundary-dimension-two: the existing statement concerns Boundary dimension of the finite localized relative normalization; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sbc-stalk-normalization-normal-part: the existing statement concerns Normality part of localized relative normalization; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sbc-trait-etale-extension: the existing statement concerns Existence of a normal finite etale extension on a smooth trait; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing statement concerns Arithmetic nodal charts and their singular-point blowups; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-sfb-galois-component-presentation: the parent requires proper B and additionally concludes a faithful decomposition action, fibre orbits and stable Cartier pullback; this child proves only the splitting construction for finite-type B, with properness conditional.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-directed-subalgebra-ring-colimit: the existing statement concerns A directed union of integer subalgebras is a categorical ring colimit; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-directed-subalgebra-tensor-colimit: the existing statement concerns Tensor base changes of a directed union form a filtered ring colimit; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-etale-colimit-normal-local-domain: the existing statement concerns A local filtered colimit of etale algebras over a normal domain is a normal domain; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-etale-over-normal-ring-normal: it asserts ascent of normality for an etale ring map, not geometric integrality or a splitting extension.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-finite-type-z-domain-normalization-finite: the existing statement concerns The normalization of a domain of finite type over Z is finite; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-normal-finite-type-subalgebra-extension: the existing statement concerns A finite-type subalgebra of a normal domain has a normal finite-type extension inside it; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-smooth-normal-domain-approximation: the existing statement concerns Smooth algebras over normal domains admit Noetherian normal base models in a filtered colimit; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-geometrically-integral-splitting vs lem-weil-pbc-smooth-over-normal-ring-normal: it asserts ascent of normality for a smooth ring map, not any splitting field or geometric component construction.
- lem-sfb-galois-geometrically-integral-splitting vs new-lem-sbc-closed-component-descent-topology: it identifies topological components under a continuous surjection; it constructs no field extension or scheme properties.
- lem-sfb-galois-geometrically-integral-splitting vs new-lem-sbc-finite-field-closed-component-descent: it descends a closed subset over one separable closure, not geometrically integral clopen components over a finite Galois field.
- lem-sfb-galois-geometrically-integral-splitting vs new-stalk-normalization-boundary-dimension-two-transfer: the existing statement concerns Finite normalization transfers boundary dimension; it constructs no finite Galois field splitting all components of a normal geometrically reduced variety.
- lem-sfb-galois-clopen-component-cover vs def-sbc-affine-torsor-equivariant-algebra: the existing statement concerns Equivariant algebra on the split components; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-exc-etale-field-gsets: it is the classification of etale schemes over a field by discrete Galois sets; it does not identify component covers over an arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-exc-etale-open-subgroup-fixed-field: the existing statement concerns Open subgroups of an absolute Galois group; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-exc-finite-galois-algebra-tensor-decomposition: it realizes a given field tensor isomorphism by spectra, not transitivity or surjectivity of component maps over an integral scheme.
- lem-sfb-galois-clopen-component-cover vs lem-exc-finite-galois-sheaf-sections-coproduct: the existing statement concerns Sections on a finite open-and-closed coproduct in a small etale site; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-exc-finite-galois-tensor-decomposition: it gives the field tensor isomorphism and a sheaf-sections formula; no component restriction over an arbitrary integral scheme is asserted.
- lem-sfb-galois-clopen-component-cover vs lem-per-galois-descent-monodromy-tensor: the existing statement concerns Monodromy and tensor of modules descended along a finite Galois cover; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-per-noetherian-constructible-galois-partition: the existing statement concerns Simultaneous Galois partitions for Noetherian constructible module sheaves; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-invariant-basic-open-descent: the existing statement concerns Unique descent of an invariant affine basic-open morphism; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-component-image-orbit: the existing statement concerns Image of one stabilizer component is its label orbit; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-component-image-orbit-backward: the existing statement concerns Backward implication of the affine torsor component image orbit criterion; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-component-image-orbit-forward: the existing statement concerns Forward implication of the affine torsor component image orbit criterion; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-equivariant-descent: the existing statement concerns Descent to the whole equivariant function algebra; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-equivariant-descent-algebra: the existing statement concerns Algebraic reconstruction from orbit data; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-equivariant-orbit-product: the existing statement concerns Equivariant algebra as product of stabilizer fixed rings; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-fixed-orbit-data-of-action: the existing statement concerns Canonical orbit data of a finite action; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-fixed-puncture-compatibility: the existing statement concerns Fixed-orbit projection compatibility; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-fixed-puncture-descent: the existing statement concerns Descent along a connected affine torsor to fixed-ring punctures; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-fixed-puncture-descent-core: the existing statement concerns Fixed-orbit affine torsor descent step; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-fixed-puncture-geometric: the existing statement concerns Geometric fixed-orbit construction; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-fixed-puncture-orbit-data: the existing statement concerns Finite orbit representative data; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-invariant-puncture-etale: the existing statement concerns Etaleness of the invariant principal open of an affine torsor; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-orbit-component-descent: the existing statement concerns Descent of individual fixed-orbit components; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-representative-component-cover: the existing statement concerns Coverage and disjointness of representative components; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-single-stabilizer-component: the existing statement concerns Descent of one stabilizer component; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-single-stabilizer-component-open: the existing statement concerns Existence of the open stabilizer component; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-single-stabilizer-component-section: the existing statement concerns Section equation for the stabilizer component; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-split-label-laws: the existing statement concerns Cocycle laws for labels in a pulled-back splitting; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-split-point-lifting: the existing statement concerns Point lifting to explicit split sections; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-stabilizer-section-mono: the existing statement concerns Monomorphy of a descended section with exact stabilizer; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-affine-torsor-stabilizer-section-open: the existing statement concerns Openness criterion for a descended stabilizer section; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-cartier-stalk-normalization-product: the existing statement concerns Integral-closure product model of a Cartier torsor normalization over the actual DVR stalk; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-equivariant-orbit-model: the existing statement concerns Equivariant orbit model; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-field-torsor-component-galois-group: it computes the automorphism group of a specified field torsor component, not the scalar-extension component covers over a scheme.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-field-torsor-galois-components: it classifies finite etale torsors over a field by field factors; it does not prove geometric-fibre orbits of components over an arbitrary integral scheme.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-fixed-orbit-product-equiv: the existing statement concerns Fixed orbit product comparison; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-sbc-fixed-orbit-product-equiv-compatible-model: the existing statement concerns Compatible finite orbit model; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-weil-pbc-connected-torsor-subgroup-quotient: the existing statement concerns Connected subgroup quotients of a finite etale torsor with geometric fibre cardinality; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-weil-pbc-finite-monodromy-trivializing-torsor: the existing statement concerns A connected finite monodromy torsor trivializing a finite locally constant module sheaf; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-weil-pbc-finite-set-monodromy-torsor: the existing statement concerns Connected monodromy torsor trivializing a finite locally constant sheaf of sets; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-galois-clopen-component-cover vs lem-weil-pbc-representable-pullback-constant-evaluation: the existing statement concerns Representable pullback is constant from exhaustive evaluation; it does not construct the geometric fibre and component-stabilizer cover for the canonical field base change over arbitrary integral B.
- lem-sfb-semilinear-open-faithful-cartier vs lem-pc-divisor-line-bundle-flat-pullback: it identifies the dual line bundle of a pulled-back Cartier ideal; it gives no restricted semilinear action or faithfulness.
- lem-sfb-semilinear-open-faithful-cartier vs lem-pc-flat-pullback-effective-cartier-ideal: it gives the flat Cartier pullback only; it has no semilinear action, faithful restriction or ideal invariance conclusion.
- lem-sfb-semilinear-open-faithful-cartier vs lem-sbc-flat-dvr-special-fiber-cartier: it makes a flat DVR special fibre Cartier; there is no scalar automorphism action or stable ideal conclusion.

Additional concept comparisons (not only shared tags):

- The geometric splitter differs from lem-trf-finite-etale-generic-component-splitting:
  the latter splits geometric generic fibres after shrinking an integral base; it
  asserts neither normal integral clopen components nor a Galois splitting field.
- The semilinear-open lemma differs from lem-sfb-common-field-semilinear-induction:
  the latter induces schemes along cosets and extends fields/groups, and assumes
  semilinear actions; it proves neither their faithfulness nor a Cartier pullback.
- The semilinear-open lemma differs from lem-sfb-semilinear-galois-alteration-domination
  and lem-sfb-finite-quotient-normal-proper: those concern equivariant alterations
  and quotient properties under additional normal/proper/finite assumptions,
  rather than the invariant open and its faithful scalar restriction.
- lem-sfb-equivariant-smooth-galois-model is the upstream consumer of the parent,
  constructs a further smooth projective alteration, and cannot be used here.

## Original arguments retained verbatim and assigned

This is the exact returned proof text read from the current item before editing.
These are future-work arguments in the report, not proof steps in any new unsplit
node. The references in them are the existing ingredient nodes, not new copies.
The two component lemmas overlap only in the elementary setup p after finite
separable field base change; the covering lemma can establish that setup directly.

### Returned step 1 → lem-sfb-galois-geometrically-integral-splitting

For any field extension $F/e$, the scheme $B_F$ is of finite type over $F$ by [lem-sfb-finite-type-composition-base-change](2). A field is Noetherian: its only ideals are $(0)$ and $(1)$. Its spectrum is quasi-compact, so [lem-weil-pbc-finite-type-over-noetherian] shows that $B_F$ is Noetherian. Taking $F=e$ proves the assertion for $B$, and this also supplies Noetherianity for each scalar extension used below.

Ingredient nodes: lem-sfb-finite-type-composition-base-change, lem-weil-pbc-finite-type-over-noetherian.

Source: literature/stacks-project/morphisms.tex, Tags 01T4 (lemma-base-change-finite-type), 01T6 (lemma-finite-type-noetherian).

### Returned step 2 → lem-sfb-galois-geometrically-integral-splitting

Apply [lem-sbc-generic-components-split] to the finite-type morphism $B\to\operatorname{Spec}e$. It gives a finite field extension $L/e$, with etale spectrum map, for which every component of $B_L$ is geometrically irreducible. At the unique point of $\operatorname{Spec}L$, [lem-weil-pbc-etale-residue-field-extension-separable] says that $L/e$ is separable algebraic. Apply [lem-weil-pbc-finite-galois-receiving-separable-extensions] with the one extension $L/e$: choose a finite Galois extension $e_0/e$ and an $e$-embedding $L\hookrightarrow e_0$. Regard this embedding as the intermediate field structure.

Ingredient nodes: lem-sbc-generic-components-split, lem-weil-pbc-etale-residue-field-extension-separable, lem-weil-pbc-finite-galois-receiving-separable-extensions.

Source: literature/stacks-project/varieties.tex, Tag 054R (lemma-finite-extension-geometrically-irreducible-components); fields.tex Tags 09DT (lemma-normal-closure), 0EXM (lemma-normal-closure-galois); morphisms.tex Tag 02G8.

### Returned step 3 → lem-sfb-galois-geometrically-integral-splitting

For $F=L,e_0$, write $p_F:B_F\to B$. The spectrum map of $F/e$ is finite by [lem-weil-pbc-spec-finite-ring-map-finite], etale by [lem-weil-pbc-finite-separable-extension-etale], and surjective by [lem-pc-field-extension-surjective]. Its base change $p_F$ is finite by [lem-trf-finite-radicial-basechange] and is etale surjective by the singleton-cover case of [lem-weil-pbc-etale-covering-base-change]. Step 1 gives $B_F$ Noetherian, while $B$ is normal integral by hypothesis. Thus [lem-fin-etale-normal-components] applies to $p_F$: both $B_L$ and $B_{e_0}$ are finite disjoint unions of nonempty clopen normal integral components. They are nonempty because $p_F$ is surjective and $B$ is nonempty.

Ingredient nodes: lem-weil-pbc-spec-finite-ring-map-finite, lem-weil-pbc-finite-separable-extension-etale, lem-pc-field-extension-surjective, lem-trf-finite-radicial-basechange, lem-weil-pbc-etale-covering-base-change, lem-fin-etale-normal-components.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, printed p.150; component normality: Stacks algebra.tex Tag 033C (lemma-normal-goes-up); morphisms.tex Tags 01WL, 02GO.

### Returned step 4 → lem-sfb-galois-geometrically-integral-splitting

For each clopen component $Z$ of $B_L$, take its inverse-image open subscheme $Z_{e_0}$ in $B_{e_0}$. For every extension $E/e_0$ its inverse image $Z_E$ is nonempty and irreducible by the geometric irreducibility supplied in step 2 (use the field tower $L\subseteq e_0\subseteq E$). Moreover $Z_E$ is open in $B_E$, which is reduced by the hypothesis on $B$ and [def-pc-geometrically-irreducible]. Reducedness restricts to an open subscheme because its local rings are the same local rings. Hence $Z_E$ is integral by [def-pc-integral-scheme]. In particular the $Z_{e_0}$ form a disjoint clopen irreducible covering, so they are precisely the components of $B_{e_0}$: an irreducible subset cannot meet both a clopen and its complement, and maximality then identifies each component. Thus every component is geometrically integral. Choose one and call it $X$. It is normal by step 3. The scheme $B_{e_0}$ is proper over $e_0$ by [lem-weil-pbc-proper-base-change]; its clopen subscheme $X$ is closed with the restricted scheme structure, so [lem-weil-pbc-closed-immersion-proper](c) makes $X$ proper over $e_0$.

Ingredient nodes: def-pc-geometrically-irreducible, def-pc-integral-scheme, lem-weil-pbc-proper-base-change, lem-weil-pbc-closed-immersion-proper.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, printed p.150, choice of the component Y_0; geometric integrality follows from geometric reducedness and the components split in Tag 054R.

### Returned step 5 → lem-sfb-semilinear-open-faithful-cartier

Put $A=\operatorname{Aut}_e(e_0)$. Define its left action on $B_{e_0}$ by $a\mapsto\operatorname{id}_B\times\operatorname{Spec}(a^{-1})$; the inverse compensates for the contravariance of $\operatorname{Spec}$. The fibre-product universal property [def-pc-fibre-product] gives the action law, $p_{e_0}a=p_{e_0}$, and compatibility with the same action on $\operatorname{Spec}e_0$. Each action map is an isomorphism, and therefore permutes irreducible components. Let $H=\{a\in A:aX=X\}$. Restricting the action to $H$ defines a semilinear action on $X$; the restriction $u=p_{e_0}|_X$ satisfies $uh=u$ for every $h\in H$.

Ingredient nodes: def-pc-fibre-product.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, printed p.150, Galois action and decomposition subgroup H.

### Returned step 6 → lem-sfb-galois-clopen-component-cover

Let $(X_i)$ be all the clopen components of $B_{e_0}$, including $X$, and put $u_i=p_{e_0}|_{X_i}$. Their inclusions form an etale covering by [lem-weil-pbc-open-immersion-etale]. Composing this covering with the singleton etale covering $p_{e_0}$ of step 3, [lem-weil-pbc-etale-covering-composition] says that every $u_i$ is etale. The inclusions are also closed immersions, hence finite by [lem-weil-pbc-closed-immersion-finite]; [lem-weil-pbc-finite-composition] makes every $u_i$ finite. Each $u_i$ is proper by [lem-weil-pbc-finite-proper], so its image is closed by the definition of properness [def-weil-proper-morphism]. Its image is open by [lem-weil-pbc-etale-morphism-open-map] and nonempty since $X_i$ is nonempty. The integral space $B$ is irreducible, hence has no nonempty proper clopen subset. Consequently every $u_i$, and in particular $u$, is surjective.

Ingredient nodes: lem-weil-pbc-open-immersion-etale, lem-weil-pbc-etale-covering-composition, lem-weil-pbc-closed-immersion-finite, lem-weil-pbc-finite-composition, lem-weil-pbc-finite-proper, def-weil-proper-morphism, lem-weil-pbc-etale-morphism-open-map, def-pc-integral-scheme.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, printed p.150, component restriction; Stacks morphisms.tex Tags 02GP, 035C, 01WK and 01WG.

### Returned step 7 → lem-sfb-galois-clopen-component-cover

Fix any geometric point $\bar b:\operatorname{Spec}\Omega\to B$ with $\Omega$ algebraically closed. By [def-weil-geometric-fibre] and [lem-weil-pbc-fibre-product-affine-spectra], the full fibre of $p_{e_0}$ is $\operatorname{Spec}(\Omega\otimes_e e_0)$. Choose an $e$-embedding $i:e_0\hookrightarrow\Omega$ using [lem-weil-pbc-algebraic-extension-embeds-algebraically-closed]. The isomorphism in [lem-exc-finite-galois-tensor-decomposition](1), applied to $e_0/e$ and tensored along $i$ on the first factor, gives
$$\Omega\otimes_e e_0\simeq\prod_{a\in A}\Omega,\qquad c\otimes b\longmapsto(c\,i(a(b)))_a.$$
Here tensoring an isomorphism preserves its inverse; extension of scalars on a finite product is identified componentwise, with inverse obtained by summing the finitely many orthogonal coordinate idempotents. This verifies the displayed map directly. A prime of the finite product of fields selects exactly one coordinate: exactly one coordinate idempotent is outside the prime. The fibre is therefore a finite disjoint union of copies of $\operatorname{Spec}\Omega$, with geometric points indexed by the embeddings $i\circ a$. The action in step 5 permutes these indices by composition with automorphisms of $e_0$, hence simply transitively. This is a statement about geometric fibre points, including their residue-field embeddings.

Ingredient nodes: def-weil-geometric-fibre, lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, lem-exc-finite-galois-tensor-decomposition.

Source: literature/stacks-project/pione.tex, Tag 03SF (section-finite-etale-under-galois), Galois-cover geometric fibres; explicit scalar-extension calculation from the tensor decomposition.

### Returned step 8 → lem-sfb-galois-clopen-component-cover

Each $u_i$ is surjective, so its base change to $\bar b$ is nonempty by [lem-weil-pbc-surjective-base-change]. It is the clopen part of the full fibre lying in $X_i$. By step 7 each such nonempty part contains a geometric point. For components $X_i,X_j$, choose points $x_i,x_j$ above the same $\bar b$. An element $a\in A$ takes $x_i$ to $x_j$ by step 7. Then $aX_i$ and $X_j$ meet at $x_j$; the components in step 3 are disjoint, so $aX_i=X_j$. Thus $A$ is transitive on components. For two points $x,y$ of the geometric fibre of $u$, step 7 gives $a\in A$ with $ax=y$. Now $aX$ meets $X$, so $aX=X$ and $a\in H$. The fibre is nonempty by surjectivity and consists of one $H$-orbit. Since $\bar b$ was arbitrary, this proves the assertion for every geometric fibre.

Ingredient nodes: lem-weil-pbc-surjective-base-change.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, printed p.150, transitivity on components and the contracted product; explicit stabilizer-fibre argument.

### Returned step 9 → lem-sfb-semilinear-open-faithful-cartier

The action of $H$ on $e_0$ is faithful because $H$ is a subgroup of $\operatorname{Aut}_e(e_0)$ (using inverses on the spectrum does not change its kernel). To check faithfulness on $X$, suppose $h\in H$ induces the identity of $X$. Choose a point $x\in X$, possible since $X$ is nonempty. On the residue field at $x$, semilinearity and the identity action imply $j(h^{-1}(c))=j(c)$ for all $c\in e_0$, where $j:e_0\to\kappa(x)$ is the structural field homomorphism. A unital homomorphism from a field into a field is injective, since its kernel is a proper ideal of the field. Thus $h^{-1}(c)=c$ for every $c$, and $h=1$. This proves faithfulness and retains the compatibility with the structure map established in step 5.

Ingredient nodes: none; elementary residue-field injection argument.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, X 2.3 Step 2, printed p.150, application of 2.2 to the decomposition subgroup; explicit check of the faithful-action hypothesis.

### Returned step 10 → lem-sfb-semilinear-open-faithful-cartier

Choose an effective Cartier divisor $D\subseteq B$ with support $C$. Since $u$ is etale it is flat by [def-weil-etale-morphism]. Apply [lem-pc-flat-pullback-effective-cartier-ideal] to obtain the effective Cartier divisor $D_X=D\times_B X$ on $X$. Locally if $D$ has equation $t$, then $D_X$ has equation $u^*t$, a nonzerodivisor, and its zero set is exactly $u^{-1}C$. For every $h\in H$, the equality $uh=u$ implies that pullback by $h$ preserves the ideal generated by these equations: $h^*(u^*\mathcal I_D)\mathcal O_X=u^*\mathcal I_D\mathcal O_X$. Consequently $D_X$ itself is $H$-stable, not only its support. This also includes the empty divisor.

Ingredient nodes: def-weil-etale-morphism, lem-pc-flat-pullback-effective-cartier-ideal.

Source: literature/stacks-project/divisors.tex, Tag 02OO (lemma-pullback-effective-Cartier-defined), case (6); ILO X 2.3 Step 2, printed p.150, Z_0 intersected with Y_0.

