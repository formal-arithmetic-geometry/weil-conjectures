# Stage-1 report: lem-trf-relative-dualizing-pair-rigidity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-relative-dualizing-pair-rigidity.json`: item, split; original statement retained, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-affine-relative-dualizing-comparison.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-algebraic-relative-dualizing-isomorphism.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: one exact statement quotation for every step/node citation. `searches.jsonl` records the search command's actual answers.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the item tag, relative-dualizing-pair terminology, relative dualizing complex, and rigidity found no project declaration for this coherent duality assertion. The hits concern etale/pro-etale exceptional dualizing objects with constant coefficients, not coherent complexes of structure-sheaf modules. The read-only upstream master is not used as evidence of a finished proof.

## Wanted literature

None. All sources used are present in the local Stacks checkout.

## Findings and changes

The item was unsplit and had no `lean_audit` declaration. Its statement agrees with Stacks `duality.tex`, Definition 0E2T and Lemmas 0E2V/0E2W, specialized to separated morphisms over a locally Noetherian base; the statement is unchanged. Neither the item's scalar assertion nor its unique class-preserving isomorphism assertion is delegated wholesale to a new node. In particular, the new algebraic isomorphism node supplies only unnormalized existence over one affine ring map; it supplies neither scalar endomorphisms nor uniqueness nor class preservation nor descent. Those are derived in the item's steps.

The scalar calculation uses the existing algebraic polynomial model and shriek calculus, not the scheme-level polynomial-chart existence theorem: the latter depends on this item and would cause a cycle. The comparison object C is used only as an affine algebraic calculation for the already given K. No global existence of coherent relative dualizing pairs is asserted or invoked.

The recorded unit and chapter were read, including `sk-i-curve-zero` and the historical blueprint ancestry below `lem-trf-local-term-locality`. The split retains the coherent-duality auxiliary route of the semistable-modification branch and does not replace a unit step. The generic Picard-framework and derived-Hom tools are declared in `split_report.tool_uses`. Neither new node coincides with a blueprint statement: `blueprint_refs.py` searches for relative dualizing, relative dualizing complex algebra, uniqueness relative dualizing, affine relative dualizing, 0E2D, and 0E2U gave no matching coherent-duality theorem. The unrelated blueprint hits define etale/pro-etale dualizing objects.

## Mathlib and duplication searches

Before writing the nodes I searched the entire DAG for 0E2C/0E2D/0E2U, the labels of the Stacks lemmas, relative dualizing, uniqueness, and affine comparison, and searched the two named source checkouts by these notions. The existing affine derived equivalence, affine pseudo-coherent RHom comparison, scalar-endomorphism theorem for polynomial dualizing models, and BBD descent were reused. The new affine node packages the actual diagonal class comparison, including the relative Tor-amplitude translation, which none of those individual existing statements provides.

For the algebraic node, LeanFinder's flat finitely presented ring phrasing returned only flatness and finite-presentation facts; the second LeanSearch phrasing returned derived localization, ordinary duality, and flatness. Loogle `DerivedCategory, CategoryTheory.Iso` returned basic single-functor and localization isomorphisms. The source grep for relative dualizing/dualizing complex/semidualizing in AlgebraicGeometry found nothing. None states the derived algebraic theorem.

For the affine node, LeanSearch's coherent affine relative dualizing phrasing returned ordinary Scheme.Modules adjunctions and ordinary dual modules; LeanFinder's diagonal sheaf/derived module phrasing returned ordinary sheaf-module pullback-pushforward adjunctions. Loogle `AlgebraicGeometry.Scheme.Modules, DerivedCategory` and the source grep for affine pseudo-coherence, relative dualizing, and diagonal RHom returned no hits. These lack both relative-perfection and derived diagonal-class comparisons. All four queries are recorded exactly, with their actual results and digests.

For the item, the second pair of searches returned rigid-category exact-pairing results and flat scheme isomorphisms. `CategoryTheory.rightDualIso` concerns actual exact pairings of monoidal objects; the coherent diagonal class here is not such a pairing and does not give that theorem as a one-line specialization. The Algebra grep's single hit is a comment in HomotopyFiber about dualizing a chain-complex construction, not a dualizing-complex theorem. Existing recorded searches were preserved, and new logged searches were appended. All services used returned successfully; no unavailable result is described as absence.

## Not duplicates

lem-trf-affine-relative-dualizing-comparison vs lem-trf-relative-duality-polynomial-chart: both mention 0E2U, but the new node translates an already supplied pair and its actual class into affine modules; the existing node constructs and glues pairs from polynomial charts and requires the present rigidity item. It cannot supply this comparison as a cited statement, and citing it would be circular.

lem-trf-affine-relative-dualizing-comparison vs lem-pc-affine-qcoh-derived-equivalence: the latter is the underlying category equivalence only; it does not translate relative Tor amplitude, diagonal pushforward, or the class multiplication isomorphism.

lem-trf-affine-relative-dualizing-comparison vs lem-sc-affine-pseudo-coherent-rhom-qcoherent: the latter is a generic internal-Hom comparison and has no relative dualizing pair, relative Tor-amplitude translation, or diagonal class.

lem-trf-algebraic-relative-dualizing-isomorphism vs lem-trf-algebraic-shriek-relative-perfect: the latter proves properties and scalar endomorphisms for the particular polynomial shriek model; it does not compare arbitrary objects satisfying the diagonal condition. There was no existing node carrying 0E2D or 0E2C.

## Review by Q109

I read `duality.tex` at Definition relative-dualizing-complex (0E2T), affine comparison (0E2U), scalar RHom (0E2V), and uniqueness (0E2W). I also read `dualizing.tex` at Definition relative-dualizing-complex (0E2C), uniqueness (0E2D), relative-dualizing-noetherian (0E2E), and relative-dualizing-algebraic (0BZW), and `cohomology.tex` at the negative-Ext gluing discussion (0D66 and its subsequent descent setup). The existing BBD node's complete statement was read: its uniqueness is for solutions with the specified local identifications, not an unqualified claim that arbitrary derived morphisms are a sheaf.

The new affine node agrees with 0E2U: f is flat and locally finitely presented, the supplied object is relatively perfect (pseudo-coherent plus local relative Tor bounds), and the class has the required multiplication property. Separatedness allows W to be the whole product. On an affine U the local relative bounds give common finite bounds by a finite refinement; the comparison uses quasi-coherent affine derived categories and the pseudo-coherent, bounded-below internal-Hom regime. R is chosen Noetherian and A is finitely presented, so A and the product algebra are Noetherian. I included the class and scalar compatibility, rather than only claiming an abstract object correspondence.

The new algebraic node is precisely the Noetherian special case of 0E2D with the meaning of relative dualizing object written out from 0E2C. It asks for A-pseudo-coherence and finite Tor amplitude over R, not finite Tor amplitude over A; it does not impose Gorenstein, complete-intersection, regularity, or constant-dimension assumptions. Its conclusion is existence of an A-linear derived isomorphism, with no uniqueness or generator normalization. Both new nodes have complete standalone statements, definition citations, no proof or proof sketch in their statements, empty proof lists and proof dependencies, exact source tag/label, inherited chapter/unit, and filled blueprint ancestry and same_as fields.

Step 1 uses the new affine comparison statement for the algebraic object and its actual diagonal class. Its multiplication isomorphism makes the Hom group a free rank-one A-module, by degree zero; this is the precise statement needed in normalization, rather than an unsupported assertion about local generators.

Step 2 uses the existing `lem-trf-algebraic-shriek-relative-perfect` statement for pseudo-coherence, relative Tor bounds, and the scalar map of C; its statement explicitly includes all three. The existing `lem-trf-algebraic-shriek-calculus` explicitly gives polynomial models, flat base change, composition, and the surjection/coinduction identification; all are used with bounded-below input R[0] or A[0]. The first coprojection pullback is identified with p2 upper shriek, and delta composed with p2 is the identity. The Noetherian finite-type algebra node supplies the hypotheses for P, A and B; no finite Tor amplitude over A is smuggled in.

Step 3 applies the new algebraic isomorphism statement to M and C after both diagonal conditions have been established. Conjugation preserves the scalar map because the chosen isomorphism is A-linear. The exact statement of `lem-sc-affine-pseudo-coherent-rhom-qcoherent` permits a bounded-above finite-projective source and a target bounded below. Here M is pseudo-coherent, and taking R itself as tensor test gives the lower cohomological bound. The open-restriction internal-Hom node explicitly identifies this with the restriction of the global scalar map. Vanishing of the cone is checked on a covering through cohomology sheaves, not by a false locality assertion for derived morphisms.

Step 4 reuses the algebraic existence input for the two supplied objects, and the affine derived equivalence transfers that isomorphism to sheaves. The affine comparison identifies the two actual classes. The unit u exists because both classes are bases of the same free rank-one module; u inverse normalizes beta. The scalar-endomorphism argument of step 3, using exactly the cited polynomial scalar theorem and affine RHom comparison, identifies automorphisms with units and forces any class-preserving scalar to be 1. Negative Ext on the affine basis vanishes because its derived endomorphism complex is A in degree zero.

Step 5 uses only the existing BBD descent statement. I checked every hypothesis: a basis is a set of opens covering X; intersections are unions of basis elements; the K restrictions have canonical transitive restriction maps; the negative self-extension groups vanish by step 4; the alpha_U inverses give compatible identifications for L, because an inclusion W subset U yields two normalized isomorphisms on W. K and L are then two solutions to the same descent system. This proves the global isomorphism without claiming that arbitrary complexes or morphisms glue naively.

Step 6 uses the full statement of `lem-pur-rhom-global-sections`, which applies to any small ringed site and identifies Hom in the derived category with zeroth hypercohomology of internal Hom. The pair's multiplication isomorphism identifies the latter with degree-zero global sections of delta_* O_X. A sheaf in degree zero has H0 equal to its ordinary sections, so the class difference is one global scalar v, and the ordinary sheaf axiom detects v=1. Uniqueness of the global isomorphism uses BBD's compatible-solution uniqueness again. Thus local equality of the diagonal classes has a justified global test.

Step 7 is a routine restriction argument: the cited pullback node explicitly has an open-restriction clause, and the internal-Hom restriction node is for arbitrary ringed spaces and arbitrary derived objects. For the closed diagonal, taking inverse images of an open computes its direct image sectionwise. Pseudo-coherence and the local relative bounds are local by their definitions. Restricting the affine charts retains the geometric hypotheses. I checked that this handles all opens, not only an affine open, and that empty U is harmless. There is no non-elementary comparison hidden in this step.

For small cases, I checked the identity morphism X=S: the multiplication condition is a trivialization of K by O_X, so the resulting normalized isomorphism is unique. Over a field, a singular flat finite-type algebra is allowed and the proof uses no line-bundle or finite A-Tor hypothesis; it still works for a non-Gorenstein algebra using its polynomial shriek complex. The zero algebra/empty affine scheme and empty X give zero derived categories and the expected unique maps. On a non-quasi-compact X the proof uses a set-sized affine basis and BBD, so it does not introduce a finite-cover assumption. Local bounds are taken only on a single affine chart before using algebraic theorems. Every proof step is shorter than 2000 characters.

I corrected the draft's potential circular shortcut by using the algebraic comparison object rather than citing scheme-level polynomial-chart existence. I also made the BBD application use the two supplied objects as solutions to one descent system and explicitly justified global equality of the diagonal class by its scalar section. The item statement and maintainer-owned metadata were left unchanged. No Lean file, compiler, Lake command, live-project file or launcher file was written or run.

## Unfinished work

No part of this one-level split is left unfinished. The two new statement-only nodes are deliberately unsplit for later stage-1 work. Server validation and push are performed through the required delivery command.
