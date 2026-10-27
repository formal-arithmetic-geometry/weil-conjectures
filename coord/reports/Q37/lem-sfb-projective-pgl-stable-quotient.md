# Stage-1 delivery: lem-sfb-projective-pgl-stable-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-pgl-stable-quotient.json: split statement, ten proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-pgl-geometric-reductivity.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-pgl-finite-stabilizer-quotient.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-polarization-section-algebra.json: statement only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-graded-proj-projective.json: statement only, unsplit; no Mathlib match.
- citations.json contains verbatim statements supporting every uses entry. search-results.json preserves the full search outputs; searches.jsonl is the search command's own log.

## Attachments

None. Searches by the exact blueprint tag, PGL, geometric quotient, and geometric reductivity in lean/WeilConjectures found no project declaration proving this item. The degreewise-filtered stable-quotient declarations concern complexes, not GIT. The existing project section-ring fraction declarations cover only pieces of the required projective-polarization theorem, not this item or the whole new input. Nothing was compiled.

## Literature wanted

WANTED: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 1 Theorem 1.10, Appendix 1.C and Appendix 2.A, for lem-sfb-projective-pgl-stable-quotient. The file named in the inherited item source is absent locally. No download or repository change was made.

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Sections 8--9, for lem-sfb-pgl-geometric-reductivity and lem-sfb-affine-pgl-finite-stabilizer-quotient. I read the primary-source PDF online at https://arxiv.org/pdf/1005.2398, especially Theorems 9.1.4, 9.7.6, 8.3.2, 8.1.1, 5.3.1 and 7.2.1. The local filename is a wanted citation, not a claim that this PDF is already obtained. Milne's locally obtained Algebraic Groups, Aside 12.58, printed p.250, corroborates the arbitrary-characteristic finite-generation input. The assembly is explicitly agent-written.

## What changed and what was wrong

The inherited item had no proof. Its invariant-Proj assertion needs an argument that the closure introduces no new semistable points; taking invariants of a restriction surjection is not exact in positive characteristic. The proof now lifts a POWER of an invariant using symmetric algebras and multiplies back to actual sections. This preserves every original hypothesis and conclusion.

The phrase “geometric quotient” alone does not establish universality for all algebraic spaces. In Alper's Theorem 7.2.1 the general adequate-moduli universality theorem has target restrictions. Our affine input uses the additional zero-dimensional stabilizers: the quotient stack has quasi-finite separated diagonal; Theorem 8.3.2 supplies finite inertia and the Keel--Mori coarse space. Comparing adequate spaces using 7.2.1 with the separated coarse space and the affine invariant target identifies the targets, and Keel--Mori gives universality for ALL algebraic spaces. Thus no separation restriction is silently dropped. This argument belongs to the future split of the affine supporting node; the item cites its full precise statement.

The original mathematical statement is unchanged. I added direct definition citations for invertible modules, section-ring multiplication and Proj, and replaced the indirect algebraic-space citation through the stable-curve moduli definition with def-trf-algebraic-space, which that definition itself uses. These are citation clarifications, not a disputed statement or a weakening. No target statement, chapter, unit, or maintainer field was edited. The current blueprint ancestor command returns None because the inherited detailed route is a native chain with a null blueprint root; the new nodes retain that root and prepend this item to the exact inherited via chain, with explicit affine-chart places.

## Incomplete work

None within the authorized one-level split. The four new inputs are intentionally unsplit statement-only nodes, ready for later stage-1 workers. There are no claimed Mathlib leaves. Validation and direct delivery are performed with the provided delivery command only.

## Review by Q37

I read the stage-1 brief, stages/1-dag.md, the three-level rules in SETUP.md, GOAL.md, the item, its chapter and unit records, and both copies of delivery-errors sections B--E. I checked the actual statements of all proof citations, including the flat-density node, the Proj definition, the algebraic-space definition, and all four new inputs. The current unit's direct-image/alteration chain is retained; none of this GIT subargument substitutes for a unit-level alteration step.

For the item I used the inherited MFK Theorem 1.10 route, checking its affine and arbitrary-characteristic mechanisms against Alper online and the local Stacks project. The missing book and missing local Alper PDF are reported above, so proof_origin.by is agent. For each new node I read these sources: (a) Milne Aside 12.58 and Alper 9.2 and 9.7.6 for PGL power lifting and finite generation; (b) Alper 9.1.4, 5.3.1, 8.3.2, Section 8.1 and 7.2.1 for the affine closed-orbit finite-stabilizer quotient; (c) coherent.tex, lemma-coherent-proper-ample, Tag 0B5T (1), (3), (4), and morphisms.tex, lemma-proper-ample-is-proj, Tag 0C6J, and lemma-proper-ample-delete-affine, Tag 0EKE, for section algebra, finite-dimensional spaces, high-degree restriction and affine fraction charts; (d) algebra.tex, lemma-uple-generated-degree-1, Tag 0EGH, constructions.tex, lemma-d-uple, Tag 0B5J, and the projective-presentation/composition argument for the graded-Proj projectivity node. No SGA source was used.

Step 1 cites exactly schematic density under flat pullback and the finite-projective-space definition. The density input's qcqs hypothesis holds because J is open in its Noetherian closure, and the projection is flat over a field. Pulling back the closure ideal and using its vanishing on the schematically dense G times J proves the action descends scheme-theoretically; this is not merely an assertion that the support is invariant. I corrected an initial uncited flat-density inference by citing the existing general node and declaring it as a tool.

Step 2 uses the section-algebra node's finite generation, finite-dimensional pieces and eventual restriction surjectivity; both Z and its closed subscheme X have the required positive-power closed embedding. Step 3 uses the same actual surjection in a sufficiently large degree and the power-lifting node, on the symmetric algebras of finite-dimensional representations. Their algebras are finitely generated, and the induced map is surjective. A homogeneous invariant polynomial is sent by section multiplication to a genuine invariant section on Z; thus semistability on the closure is exactly intersection with the ambient semistable open. The scheme equality with J is the kernel calculation in step 1. The closed-orbit and stabilizer hypotheses are inherited from the assumed containment in Z^s, without any tameness hypothesis.

Step 4 uses precisely finite generation of S^G and the graded-Proj node. R_0 is a subspace of finite-dimensional S_0, rather than presumed to equal k. The graded-Proj statement gives finite-projective-space projectivity over k, not just properness over Spec R_0. Step 5 uses exactly the section-algebra node's affine finite-type fraction charts for every positive homogeneous section. Those opens cover because of the proved semistability equality.

Step 6 is a written-out elementary coaction calculation, not an extra node. Localization annihilates the defect by a single power of s; multiplying the numerator by that power makes it invariant. This works with s-torsion and nilpotents, so no domain or reducedness hypothesis was inserted. Step 7 uses exactly the affine quotient node's categorical and orbit conclusions, with all hypotheses checked on the invariant affine open; the last identification with D_+(s) is part of the cited Proj definition. Closed orbits remain closed in that invariant open and their stabilizers are unchanged.

Step 8 writes out both localization compatibility and the inverse-image identity, using s^e/t^d on the t-chart. The latter is necessary for the global point argument; it is not assumed from an unquoted quotient theorem. Step 9 uses the affine categorical property on s, t and st, together with the sheaf condition in the cited algebraic-space definition, to glue and prove uniqueness. This is ordinary Zariski gluing, not descent through an unproved flatness assumption on q. Step 10 uses the affine node's orbit bijections over each algebraically closed extension and the inverse-image identity already proved, establishing both surjectivity and injectivity of the global orbit bijection.

For delivery-errors B I checked self-contained statements, inline definitions of group actions/invariants and gradings, complete hypotheses, single-escaped TeX, exact Stacks labels and tags, and empty proofs/dependency lists on new nodes. For C I opened every cited statement and generated citations.json from those statements; I separated the affine coarse-space claim from unrestricted adequate quotients and declared the one off-unit density tool. For D the proof actually constructs and glues affine maps, proves semistability equality and checks inverse images: no new node restates the projective item, its closure-specific clause, or the whole projective quotient construction. The four inputs apply to arbitrary affine algebras or non-equivariant polarizations, independent of J. For E I tested empty J, r=1 (trivial group), nilpotent homogeneous sections, nonreduced schemes and stabilizers, characteristic dividing a stabilizer order, and disconnected X with S_0 larger than k. In the empty case the closure and its section ring have empty Proj; all quotient claims have their unique empty-source interpretations. In the trivial-group case a closed subscheme of projective Z is recovered by its section-ring Proj. The fraction defect proof handles nilpotents; all invariant arguments use scheme coactions rather than only k-valued group elements. None of the ten steps exceeds 2000 characters.

All search command hits were read, including the additional restriction-surjectivity and graded-algebra searches. The finite/profinite group invariant lemmas are not Haboush for PGL; representation invariants do not construct algebraic-space quotients; and Mathlib Proj properness does not prove the Veronese finite-projective-space assertion. Every new-node search record copies a query that actually ran and preserves its output. Blueprint searches for quotient, reductivity, power lifting, section ring and graded algebras found no equivalent blueprint statement; existing special-purpose fraction and curve-reconstruction nodes do not supply this general input.

## Not duplicates

lem-sfb-projective-polarization-section-algebra vs lem-zl-bertini-prescribed-point-smooth-system: the existing statement concerns Prescribed-point high-degree systems with smooth hypersurfaces; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-zl-prescribed-point-bertini-open: the existing statement concerns Bertini open with nonzero first-order values at finite base points; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-zl-effective-cartier-pure-dimension: the existing statement concerns Pure dimension of a Cartier divisor on an integral finite-type scheme; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-zl-prescribed-point-eventual-jet-system: the existing statement concerns Eventual kernel basis, complement immersion and simultaneous jets; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-zl-prescribed-point-smooth-member: the existing statement concerns Affine pure-dimensional smooth members from an interpolating fixed system; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs def-zl-prescribed-point-system-data: the existing statement concerns Concrete prescribed-point linear systems; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-pc-q3-affine-open-twist-vanishing-independent: the existing statement concerns Affine-open twist vanishing independent of proper coherence; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-pc-c2-closed-immersion-fixed-degree-vanishing: the existing statement concerns Fixed-degree vanishing for a closed projective subscheme; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-pc-e4-affine-restricted-twist-fixed-degree: the existing statement concerns Fixed-degree affine-local twist cohomology vanishing; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-weil-pbc-closed-immersion-serre-vanishing: the existing statement concerns Serre vanishing for restricted projective-space twists over a Noetherian ring; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-projective-polarization-section-algebra vs lem-weil-pbc-ample-very-ample-immersion-affine-base: the existing statement concerns An ample invertible module over an affine base: a power is the pullback of O(1) along an immersion into projective space; it does not state the general section-algebra/chart/restriction package for arbitrary projective polarizations (shared source tag 0B5T).

lem-sfb-finite-graded-proj-projective vs lem-trf-alteration-relative-curve-preparation: the existing statement concerns Preparation of an alteration problem as a relative curve, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-trf-relative-marked-nodal-reduction: the existing statement concerns Marked nodal reduction of one relative curve, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-trf-projective-bundle-to-h-projective: the existing statement concerns Projective-bundle projectivity over an ample base implies H-projectivity, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-trf-projective-bundle-global-generated-h-projective: the existing statement concerns A globally generated projective bundle is H-projective, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-sfb-projective-affine-base-blowup: the existing statement concerns Blowups on a projective scheme over an affine Noetherian base are H-projective, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-sfb-projective-bundle-composition: the existing statement concerns Composition of projective-bundle morphisms over a qcqs base, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 0C4P).

lem-sfb-finite-graded-proj-projective vs lem-per-excellent-quasiprojective-normalized-blowup: the existing statement concerns Normalized blowups preserve quasi-projectivity over an excellent affine base, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-per-projective-bundle-composition: the existing statement concerns Composition of projective-bundle morphisms over a qcqs base, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 0C4P).

lem-sfb-finite-graded-proj-projective vs lem-per-excellent-normalized-blowup-tower: the existing statement concerns Geometry of finite normalized point-blowup towers, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 0C4P).

lem-sfb-finite-graded-proj-projective vs lem-per-surface-point-blowup-geometry: the existing statement concerns Regularity and projectivity of a point blowup on a regular surface, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-per-normalized-blowup-tower-etale-descent: the existing statement concerns Descent and projectivity of finite normalized blowup towers, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 0C4P).

lem-sfb-finite-graded-proj-projective vs lem-weil-pbc-finite-separable-base-refinement: the existing statement concerns Finite separable base refinement, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 087S).

lem-sfb-finite-graded-proj-projective vs lem-weil-pbc-projective-space-finite-coordinates: the existing statement concerns Finite homogeneous coordinates embed in standard projective space, rather than Veronese projectivity for arbitrary finite graded algebras with finite degree-zero part (shared source tag 01N0).

The existing lem-sc-ample-proj-open states existence of an open immersion into SOME graded Proj, not finite generation or the section-ring identification needed here. The local-chart node requires affineness of X_s as a hypothesis and does not prove it. The nodal log-canonical reconstruction statement assumes a specific marked nodal curve family and does not cover arbitrary polarized projective schemes. The existing finite-group projective quotient results assume a finite acting group, whereas PGL_r is positive-dimensional for r>1. None is a duplicate of a new node.
