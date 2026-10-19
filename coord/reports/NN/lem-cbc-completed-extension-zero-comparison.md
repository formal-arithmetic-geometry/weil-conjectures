## Worker report

Repair by NN, 2026-10-17, of `lem-cbc-completed-extension-zero-comparison`.
The return requires extracting the hidden arguments in returned Steps 5 and 7,
retaining the statement, Lean record, and original proof route. This is stage 1;
no Lean was written and no compiler, Lake or build command was run.

Files written:

- `dag/nodes/sec-smooth-purity/lem-cbc-completed-extension-zero-comparison.json`:
  unchanged statement and Lean record; eleven proof steps, status split.
- `dag/nodes/sec-smooth-purity/lem-cbc-exact-product-functor-strict-limit.json`:
  statement-only canonical comparison for an exact product-preserving module
  functor and total strict derived inverse limit; unsplit, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-cbc-finite-open-exchange-scalars.json`:
  statement-only compatibility of finite open exchange, its inverse mate, and
  coefficient restriction/strict transitions; unsplit, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-cbc-adic-pullback-presentation-transport.json`:
  statement-only transport of coefficient maps, universal derived pairs, strict
  reduction diagrams, and completion units; unsplit, no Mathlib match.
- `citations.json`: full verbatim statement quotations for all 43 step citations.
- `report.md`: this report. `searches.jsonl` was appended by msearch.py only.

The sandbox initially held only `searches.jsonl`, without a node or report.
I read its recorded hits before reusing them. No delivery invocation was active.
I copied the returned proof from the current shared node, which still contains
4689-character Step 5 and 4044-character Step 7. No shared git command was run.
The last merged NY report is preserved as `scratchpad/report-inherited-NY.md`,
and the three affected original arguments are preserved verbatim in
`scratchpad/returned-arguments.md`. These scratchpad files are not deliveries.
The earlier report's obsolete stage-2 binding/blocker claims are historical:
the current base has the Lean record `Sheaf.Paper.CompletedOpenExchangeTransport`,
which is retained exactly. This repair makes no stage-2 assertion.

Attachments: none. The whole slopmaster2 WeilConjectures tree has no item tag or
completed-open-exchange declaration. Concept searches found ordinary open
extension, adic open restriction and homotopy-limit objects, with different
coefficient categories or only part of the conclusion. In particular,
`SixFunctors/ProEtale/Adic/BaseChange.lean` concerns open restriction of direct
image over its specific adic coefficient category, not the item or new tools.
Mathlib's derived-functor comparison declarations are ingredients, not an exact
match for a new node's whole statement.

WANTED: none. The blueprint and all cited Stacks sources are present locally.

## Return repaired

1. Returned Step 5: retained the levelwise tower-product argument in Step 5.
   Extracted the natural resolution/ordinary-limit comparison, both Roos equations,
   and strict-augmentation compatibility into
   `lem-cbc-exact-product-functor-strict-limit`. Step 6 now applies that statement
   after checking its hypotheses. The existing `lem-weil-strict-roos-comparison`
   already supplies functorial cone descent, a natural comparison with total
   Rlim, resolution independence and augmentation normalization. It is reused
   as a statement dependency of the new comparison node, rather than duplicated.
2. Returned Step 7: extracted coefficient restriction and inverse-adjoint-mate
   compatibility into `lem-cbc-finite-open-exchange-scalars`, used in Step 8.
   Extracted coefficient-map equality, derived-pair counit normalization and the
   strict-tower presentation comparison into
   `lem-cbc-adic-pullback-presentation-transport`, used in Step 9. The latter
   includes the completion-unit assertion previously used inline in Step 8;
   Steps 10-11 assemble the original completed exchange and its normalization.
3. The statement, statement dependencies and Lean record equal the current base
   exactly. Original Steps 1-4 and 6 are retained verbatim (the last is now Step 7).
   The route is still tensor/reduction, quasi-compact product kernel, canonical
   strict Rlim comparison, intrinsic completeness, finite exchange and total
   derived limit. No conclusion is moved wholesale into a child node.
4. All non-elementary proof steps are below 2000 characters. Their maximum is
   1752, in the unchanged tensor/K-flat argument. The final 2732-character
   assembly step was also shortened: its normalization now cites the extracted
   transport and strict-limit statements. No long step was merely relabelled
   elementary.

## Sources and arguments retained for the new frontier

The current blueprint is
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`.
I read it and its statement, plus the imported chapter and `sk-prop-sf-cbc` unit.
All three children have this item as their nearest blueprint ancestor, no
intermediate created ancestor, exact proof-sentence locations and `same_as: []`.
The source proof is agent-written. The child statements make precise hidden
arguments of the returned proof; they do not pretend that Stacks explicitly
states the full additional normalization.

For `lem-cbc-exact-product-functor-strict-limit`, I read Stacks Tag 0940,
`sites-cohomology.tex`, `section-derived-limits`, including
`lemma-derived-limit-is-ok`. It computes total Rlim on a K-injective strict tower
and includes its kernel map into the two-product complex. Tag 07KC,
`derived.tex`, `lemma-products`, justifies using termwise products under exactness.
The signed model is the original H(M), with differential (dx,(1-s)x-dy).
The normalized existing Roos comparison gives theta. Product preservation gives
kappa on both summands. Define lambda by theta^{-1} kappa F(theta). To compare
with ordinary limits, resolve M to I and FI to J; both paths from F lim I into
H(J) take a compatible family x to ((v_n x_n)_n,0). The first-coordinate
projection and shifted second-coordinate inclusion give both Roos equations.
A strict augmentation enters the same zero shifted coordinate. This is the
preserved argument for the future splitter; the new node itself has no proof.
It requires exact products on both sites and exactness/product preservation of
F, rather than assuming arbitrary triangulated cone maps are canonical.

For `lem-cbc-finite-open-exchange-scalars`, I read Stacks Tag 03DI,
`sites-modules.tex`, `lemma-extension-by-zero`, and Tag 03DJ,
`lemma-extension-by-zero-exact`, together with the existing finite open exchange,
finite exact pullback and site-composition statements. The direct-sum presheaf,
its abelian sheafification, inverse image, unit and counit have identical
underlying abelian maps after composing a scalar action with B->C. The inverse
exchange is the adjunct of inverse image of the open unit and the normalized
composition map. These maps therefore commute with restriction of scalars;
their inverses do as well. Naturality then applies to every semilinear strict
tower transition and every composite quotient. This is more than the existing
finite-exchange isomorphism at one coefficient ring. There is no requirement
that the scalar map be flat, that the open be quasi-compact, or that a complex
be constructible. The conclusion concerns restriction of scalars, not exactness
of arbitrary scalar extension.

For `lem-cbc-adic-pullback-presentation-transport`, I read the full completed
pullback, coefficient datum, strict-diagram K-flat replacement, resolving-class
universal-pair and constant-completion comparison statements. I read Stacks
Tag 05S7, `derived.tex`, `section-derived-functors`, with the left-derived
part of `definition-right-derived-functor-defined`, and Tag 099N,
`proetale.tex`, `lemma-pushforward-Noetherian-case`, clauses (2) and (5).
The former supplies context for localization/derived pairs; the latter supplies
the completion route, without asserting the new concrete presentation comparison.
I also read Mathlib `CategoryTheory/Functor/Derived/LeftDerived.lean`, lines
90-137: leftDerived_ext, leftDerivedNatTrans_fac, leftDerivedNatIso and
leftDerivedUnique give the universal comparison ingredient.

The retained argument is: the finite components determine c_g by the limit
universal property; constant-section naturality gives all q_{b,a} squares.
After this identification alpha is identity on balanced tensors and is natural
in every module map. The two universal pairs give inverse comparisons with
the stated counit equations; strict diagram replacements give the same
comparison before evaluating. On a K-flat representative the strict quotient
augmentation is x->x tensor 1, so alpha preserves it and each transition.
Applying Rlim and its constant-tower unit gives E u_1=u_2 e. Keeping the
actual units/counits also keeps inverse open mates. Neither the generic Mathlib
uniqueness lemma alone nor equality of finite evaluations supplies all these
strict quotient-augmentation assertions. This is a genuine extracted tool for
a scheme map; it asserts neither completed open base change nor preservation
of derived completeness by extension by zero.

## Search audit

Before creating each child I searched the whole DAG by concept, Stacks tag and
expected declaration, and the whole imported blueprint using blueprint_refs.py.
The ancestor command identifies the item itself. Searches included Roos, mapping
fiber, strict Roos, restriction of scalars, scalar restriction, finite exchange,
coefficient change, tower comparison, universal pair, counit-normalized, derived
comparison and completion unit. Broad searches were followed by reading actual
statements, including the close candidates listed below. The existing normalized
strict Roos comparison is used. The finite-exchange node does not state coefficient
compatibility; the exact-functor Rlim node explicitly disclaims canonical choice;
the strict ordinary constant-coefficient proper/open calculus does not give the
completed-coefficient presentation comparison.

Every new child's mathlib_searches contains only exact msearch.py queries in
searches.jsonl. I read all new returned signatures and the retained logged hit
names. Each child has semantic, Loogle and source-grep searches and a second
phrasing. All of the searches assigned to these new nodes succeeded; none is
recorded as unavailable or falsely recorded as absent. The original search log
is retained, including earlier unrelated successful queries.

For the strict-limit child, searches returned exact-functor infrastructure and
mappingCone.mapHomologicalComplexIso, mapTriangleIso and map_delta; the latter
compare a single cone under an additive functor, not total Rlim, its resolution
comparison and augmentation normalization. For finite exchange, the hits are
Zariski module restriction/pullback, sheafification and ringed pullback, not
finite pro-etale exchange natural under scalar restriction. For the adic
transport, leftDerivedUnique/leftDerivedNatIso supply only the universal-pair
part; the completed coefficient map, quotient diagram and completion unit are
additional. No child is a Mathlib leaf. No Mathlib statement was recreated just
because its name differs from Stacks.

## Source error

STATEMENT-DISPUTED (inherited correction only): the blueprint's arbitrary-open
parenthetical incorrectly treats sheaf extension by zero as sectionwise zero
and infers product preservation. Stacks Tag 09BP, `proetale.tex`,
`lemma-j-shriek-limits`, assumes a quasi-compact open immersion and uses the
kernel sequence with closed complement and Tag 09AA, `lemma-closed-immersion`.
The existing item statement already has the necessary quasi-compactness; this
repair changes no statement.

The retained counterexample is X=Spec(product of countably many F_2), U the union
of its isolated principal points, A=Z_l, I=(l). U is discrete and not
quasi-compact. A global section of j!A_U has finite support. The compatible
sections (l^m mod l^n)_m have finite support at each n and infinite support in
the limit; they are absent from j!A_U. Thus completion need not be preserved
without the existing quasi-compactness condition. Nothing about g is added.
No SGA source is used.

## Review by NN

I checked the return against the actual files, keeping the statement and Lean
record untouched. The children contain statements only, introduce their own
objects and hypotheses, cite their notions, have empty proof/proof_deps and
proof_origin null, and have no Lean declaration claimed. Source locations and
blueprint ancestry describe the exact inherited argument each extracts.

Step 1 uses the adic datum, open square, slice localization, sectionwise limits,
and quasi-compact base change. The quoted statements identify every finite
coefficient restriction and give quasi-compact j' for arbitrary g. Compatible
families then identify the completed sheaves and all projections. Step 2 uses
the ringed slice exact adjunction and exact-functor derived theorem, with finite
extension only at P_n. The extension, scalar-restriction and sheafification
statements justify the same underlying sheaf and natural module actions.

Step 3 uses K-flat resolution, ringed slice tensor, left-adjoint colimit
preservation, total tensor and flatness/K-flatness definitions, and the datum.
I read 06YS (`sites-cohomology.tex`, `lemma-K-flat-resolution`) and 0E8I
(`sites-modules.tex`, `lemma-j-shriek-and-tensor`). Exact restriction, K-flat
tensor and exact extension prove K-flatness of e!P; the flat-term version gives
flat terms. The displayed tensor generator verifies the actual quotient arrows.
Step 4 uses the closed-subscheme existence, inverse-image formula, slice
localization, quasi-compact ringed recollement, sectionwise limits and immersion
limit theorem. I read 09AA and 09BP: e! is the kernel on e_*F; closed inverse
image has coefficient i^{-1}R, so products of the two kernels agree. This
retains the existing elementary kernel assembly, including the empty product.

Step 5 uses the exact-countable-products and derived-products statements, and
the levelwise abelian tower statement. Module products are exact for both A_T
and A_W. The explicit levelwise product has its limiting property by projection;
exactness is levelwise. This verifies the exact/product-preserving hypotheses
of the new tool without silently assuming existence of a derived-tower limit.
Step 6 uses exactly the new strict-limit comparison's statement: natural lambda,
its formula, resolution comparison, Roos equations and strict-augmentation
compatibility. The old 4689-character hidden proof is no longer inline. The
normalized Roos lemma is a statement dependency of that new tool, not an
unmentioned proof artifact of a merely existential Rlim node.

Step 7 is the original Step 6. It uses intrinsic Koszul completion, slice tensor
and completed-pullback reduction. I read 0A0E (`algebraization.tex`,
`lemma-derived-completion-koszul`). Restriction preserves the finite free Koszul
complex and its multiplication maps; Steps 3-4 preserve its completion fiber
and unit c->((c tensor 1)_m,0). This proves j!K complete before the completed
pullback definition is invoked. The reduction theorem applies to complete K
for g_U, then to complete j!K for g; j' is quasi-compact by Step 1. Thus both
endpoints are complete with no boundedness or finite-type condition on g.

Step 8 uses finiteness from the datum, exact finite pullback, the new
coefficient-compatible exchange, constant-completion equivalence and the
completed-pullback definition. The new node explicitly says that beta and its
inverse mate commute with all semilinear quotient arrows. The constant-completion
statement explicitly says its finite-reduction identifications commute with
quotient transitions. These quotations together give an isomorphism in the
actual derived strict-tower category. Equality of unrelated evaluated derived
maps is never used to construct a tower map.

Step 9 uses the new presentation-transport statement and completed-pullback
definition. The latter specifies the finite projections of c_g; the new node's
hypothesis is therefore met for the specified presentations. It supplies the
module comparison, universal ordinary and strict-tower counit equations and
quotient compatibility. This extracts the second hidden argument of old Step 7
without assuming c_g invertible. Step 10 uses functorial Rlim and completed
pullback, assembling Step 8 with inverse lambda from Step 6. Naturality is
composition of the supplied natural transformations, and Step 7 supplies every
complete-domain requirement. Step 11 uses the new transport's unit equation,
the definition of the actual units, and the strict-limit comparison's
augmentation normalization. Both statements actually assert the exact
normalizations used; this is no longer an uncited identification in a long
final step.

For the new strict-limit statement I checked F=identity, F=zero, M=zero and a
constant identity-transition tower. The signed fiber model has kernel
augmentation (x,0); product comparison is identity for F=identity and zero
objects for F=zero. Exactness of countable products on both sides is explicit.
For finite exchange I checked empty open, identity open, identity g, zero ring,
B=C and two composable quotient maps. Extension is zero or identity as
appropriate; scalar restriction never requires flatness. For adic transport I
checked I=0, the zero complex/ring, identity g and identical universal pairs.
Its maps reduce to identity after the fixed counit normalization; quotient
augmentation remains x->x tensor 1. Positive indexing avoids an unintended n=0.
The empty generator tuple in intrinsic completeness causes no exception.

The B-E review found no new theorem disguised as a definition, no proof inside
an unsplit child, no clause restating the completed open theorem, no new
hypothesis on g, and no identification of completed and constant ambient
coefficient categories. I read every statement quoted by a parent step; full
verbatim quotations in citations.json make the exact interface reviewable.
The off-unit generic tools retained by the parent are declared in split_report
as before. No maintainer-owned accepted tool_uses field was changed.

## Not duplicates
lem-cbc-adic-pullback-presentation-transport vs lem-weil-pbc-right-derived-plus-injective: the existing node gives bounded-below right-derived injective resolutions and their universal comparison; the new node identifies unbounded left-derived pullback, actual adic towers and ordinary-to-completed units.

lem-cbc-exact-product-functor-strict-limit vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: the existing node defines total Rlim and its Roos triangle for one category, not a canonical comparison under an exact product-preserving functor or strict augmentations.

lem-cbc-exact-product-functor-strict-limit vs lem-weil-ringed-tower-pushforward-limit-comparison: the existing node concerns derived direct image along a ringed-topos morphism; the new tool concerns an arbitrary exact product-preserving module functor, in particular open extension, without assuming it is a direct image.

lem-cbc-exact-product-functor-strict-limit vs sk-lem-sp-tower: the existing node reconstructs a normalized bounded constructible finite-Tor varying-coefficient tower; the new tool compares an arbitrary strict tower under a fixed exact functor.

lem-cbc-exact-product-functor-strict-limit vs lem-weil-compact-support-reduction-tower-functor: the existing node constructs compact-support reduction towers for finite-type schemes and valuation coefficients; it does not give the canonical exact-functor/Rlim comparison.

lem-cbc-finite-open-exchange-scalars vs lem-pc-open-inverse-image-injectives: the existing node preserves injectives under Zariski open inverse image; the new node concerns scalar compatibility of finite pro-etale open exchange.

lem-cbc-finite-open-exchange-scalars vs lem-sc-module-extension-by-zero-unit-epi: the existing node only asserts a ringed-space open unit is epi; the new node asserts coefficient and strict-transition compatibility of a base-change mate.

lem-cbc-finite-open-exchange-scalars vs lem-pc-open-restriction-ext-bijective: the existing node gives Ext restriction bijections for Zariski structure-module base change and explicitly no scalar compatibility; the new node is finite pro-etale coefficient-compatible exchange.

lem-cbc-finite-open-exchange-scalars vs lem-pc-open-extension-derived-unit-isiso: the existing node only makes the derived Zariski open unit invertible; the new node compares finite coefficient ring changes of the exchange and its inverse mate.

lem-cbc-finite-open-exchange-scalars vs lem-sc-module-extension-by-zero-unit-isiso: the existing node only makes the ringed-space open unit invertible; the new node compares coefficient changes and strict quotient transitions of open base change.

lem-cbc-finite-open-exchange-scalars vs lem-pc-scheme-module-free-yoneda-iso: the existing node identifies a free structure-module sheaf with an extension of the unit; it states no finite-ring base-change compatibility.

lem-cbc-finite-open-exchange-scalars vs lem-pc-open-restriction-data: the existing node fixes degree-zero Zariski structure-module base-change sheaf data; it states no pro-etale finite coefficient open-extension exchange across ring homomorphisms.

lem-cbc-finite-open-exchange-scalars vs new-open-embedding-sheaf-pullback-adjunction: the existing node constructs a left adjoint for topological open pullback; it gives no coefficient-change equality for an open base-change mate.

lem-cbc-finite-open-exchange-scalars vs new-open-embedding-sheaf-pullback-preserves-monomorphisms: the existing node preserves monomorphisms under topological pullback; it gives no finite coefficient or strict-tower compatibility.

lem-cbc-finite-open-exchange-scalars vs lem-sc-module-extension-by-zero-unit-mono: the existing node only says a ringed-space open unit is mono; it gives no base-change/scalar-restriction equation.

lem-cbc-finite-open-exchange-scalars vs lem-pc-open-embedding-sheaf-pullback-injectives: the existing node preserves injectives under topological open pullback; it gives no finite-ring pro-etale exchange comparison.

lem-cbc-finite-open-exchange-scalars vs lem-pc-open-free-restriction-hom: the existing node is a Zariski free-sheaf Hom restriction bijection, not finite pro-etale scalar-compatible exchange.

lem-cbc-finite-open-exchange-scalars vs lem-pc-inverse-image-open-free-sheaf: the existing node pulls back a represented Zariski open free abelian sheaf; it states no coefficient changes or complex-level inverse mate compatibility.

lem-cbc-finite-open-exchange-scalars vs lem-sfb-locally-closed-extension-coherence: the existing node gives factorization/composition coherence of locally closed extension over a fixed ring on a Noetherian scheme; it does not compare finite-ring coefficient changes of the base-change mate for arbitrary schemes.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-ringed-slice-extension-preserves-exact: the existing node proves exactness of ringed slice extension; it states no coefficient-compatible base-change transformation.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-sheaf-free-separator: the existing node constructs free sheaf separators and their Hom formula, not coefficient-compatible open base change.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-free-etale-module-shriek-comparison: the existing node identifies an etale free sheaf with etale extension of a unit, not finite pro-etale base change under coefficient restriction.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-proetale-ringed-open-closed: the existing node gives recollement and exactness for a quasi-compact open and closed complement over one ring sheaf; it does not compare base-change mates along finite ring homomorphisms.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-affine-free-finite-stalk-generation: the existing node gives finite stalk generation by etale free sheaves, not a coefficient-change equation for an exchange.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-etale-graph-section-extension-map-linear: the existing node gives linearity of etale graph-section extension to finite direct image, not an open pro-etale base-change mate compatible with varying finite coefficients.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-free-yoneda-presheaf-module: the existing node gives a free presheaf Yoneda bijection; it does not give finite coefficient/base-change/tower compatibility.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-zariski-extension-by-zero-adjunction: the existing node constructs Zariski abelian extension and its adjunction; it gives no finite pro-etale coefficient change of an open exchange.

lem-cbc-finite-open-exchange-scalars vs def-weil-pbc-local-coefficient-localization: the existing node defines localization by a local section and its multiplication transformation, not finite-ring scalar-compatible open base change.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-free-sheaf-derived-sections: the existing node computes etale derived sections as Hom from a free rank-one module; it gives no open-exchange coefficient equation.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-extension-by-zero-adjunction: the existing node constructs the small-etale extension adjunction, not finite pro-etale coefficient-compatible exchange.

lem-cbc-finite-open-exchange-scalars vs def-weil-pbc-extension-by-zero: the existing node defines small-etale extension by zero for one coefficient ring; it does not assert coefficient or base-change compatibility.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-free-sheaf-flat: the existing node gives flatness of a free sheaf extension; it gives no comparison of base-change mates across ring homomorphisms.

lem-cbc-finite-open-exchange-scalars vs def-weil-extension-by-zero-presheaf: the existing node defines the direct-sum presheaf used by the new node; it does not assert the sheaf-level coefficient-compatible base-change mate.

lem-cbc-finite-open-exchange-scalars vs new-over-pullback-preserves-injectives: the existing node preserves injectives under slice abelian restriction; it gives no finite coefficient open-exchange equality.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-site-restriction-injectives: the existing node gives exact slice restriction/extension and adjunction; it gives no coefficient-change/base-change compatibility.

lem-cbc-finite-open-exchange-scalars vs lem-weil-pbc-site-extension-by-zero-presheaf-adjoint: the existing node constructs abelian sheafified slice extension and its adjunction; it does not state finite coefficient compatibility of the open base-change mate.

lem-cbc-finite-open-exchange-scalars vs new-over-pullback-adjunction-mono: the existing node constructs a mono-preserving left adjoint to abelian slice restriction; it gives no coefficient-change/base-change mate equation.

lem-cbc-finite-open-exchange-scalars vs new-lem-sc-nested-slice-extension-stalks: the existing node gives a stalk isomorphism between nested-open extension presheaves on a topological space; it gives no finite pro-etale coefficient-compatible exchange.

lem-cbc-exact-product-functor-strict-limit vs lem-cbc-exact-functor-rlim: the old node explicitly disclaims a canonical choice from bare triangulated data; the new node specifies the natural resolution/Roos comparison and its augmentation normalization for an exact module functor.

lem-cbc-exact-product-functor-strict-limit vs lem-weil-strict-roos-comparison: the old node already gives the normalized Roos functor and is reused; the new node compares that functor under F and proves agreement with the ordinary-limit/resolution comparison and both Roos equations.

lem-cbc-exact-product-functor-strict-limit vs lem-sf-strict-roos-derived-limit-comparison: the old node gives a comparison for a tower and one resolution, not transport under an arbitrary exact product-preserving functor with augmentation normalization.

lem-cbc-finite-open-exchange-scalars vs lem-cbc-proetale-extension-zero-base-change: the old node gives the canonical isomorphism for one finite ring and naturality in its complexes; the new node fixes its inverse mate and proves compatibility between different finite rings and all semilinear strict transitions.

lem-cbc-finite-open-exchange-scalars vs lem-cbc-proetale-extension-zero: the old node gives extension/exactness and scalar restriction of extension, not coefficient restriction of the inverse-image/open-exchange mate.

lem-cbc-finite-open-exchange-scalars vs lem-sf-open-tensor-normalization: the old node fixes the ordinary and diagram ringed exchange and tensor maps; the new node compares different finite coefficient rings and their strict semilinear quotient arrows.

lem-cbc-finite-open-exchange-scalars vs lem-cbc-strict-tower-proper-open-calculus: the old node uses one constant ambient ring B and proper/open composition calculus; it does not assert the finite-ring scalar compatibility for a varying system acting through the completed ring sheaf.

lem-cbc-adic-pullback-presentation-transport vs lem-weil-pbc-constant-completion-equivalence: the old node compares constant and completed coefficient categories and finite reductions; the new node compares two derived presentations of the same completed ring-map pullback with their actual counits and ordinary-to-completed units.

lem-cbc-adic-pullback-presentation-transport vs lem-pur-left-derived-from-kflat-class: the old node supplies a universal left-derived pair from a resolving class; the new statement includes completed coefficient projection equations, strict reduction diagrams, and completion-unit compatibility.

lem-cbc-adic-pullback-presentation-transport vs lem-sfb-multivariable-derived-calculus: the old node gives abstract derived comparison/naturality, with derivability-structure hypotheses; it does not state the completed coefficient map, strict quotient augmentation, or constant-tower completion-unit identity.

lem-cbc-adic-pullback-presentation-transport vs lem-sp-completion-mate-comparison: the old node compares completed proper-style direct-image mates with a constant-ring tower exchange; the new node compares actual ordinary/strict-tower left-derived presentations over completed coefficient sheaves, and their quotient units.

lem-cbc-adic-pullback-presentation-transport vs lem-cbc-completed-extension-zero-comparison: the new node concerns presentations of pullback for one scheme map; it states neither completeness of j!K nor the completed open exchange isomorphism.
