# Q14 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-curve-function-field-morphisms.json: item, split into nine proof steps; no Mathlib match for the full correspondence.
- dag/nodes/sec-six-functors-basics/lem-sfb-valuation-stalk-proper-target-extension.json: statement-only general extension lemma; no Mathlib match. The project already proves a more general base-scheme version, identified below.
- citations.json: every step/node pair, with the verbatim statement used.
- report.md: this report.

## Attachments

AlgebraicGeometry.Scheme.exists_hom_of_valuationRing_stalk belongs to lem-sfb-valuation-stalk-proper-target-extension by specialization to S = Spec k: lean/WeilConjectures/Mathlib/AlgebraicGeometry/Birational/RationalMap.lean:40. Its proof ends at line 91 (namespace closes at 93), and contains no sorry. This is an attachment candidate for the maintainer's dependency audit, not an assertion that I ran an axiom checker. Its extra Y.IsSeparated and S.IsSeparated instances hold here: S is affine, and Y is separated over the separated scheme S. The new node is left statement-only and unsplit, rather than duplicating its existing project proof. I found no declaration of WeilConjectures stating the whole item, either by blueprint tag or by searches for curve/function-field equivalences. The Mathlib rational-map interfaces do not supply the everywhere-defined correspondence in the item.

## WANTED

None. All sources needed are present. No external download or SGA source was used.

## Corrections and scope

The statement is correct and is unchanged. There was no imported proof to preserve. The imported source's last assertion about finite field degree required an argument, supplied in step 5; I did not silently replace it by geometric finiteness or assume separability. The nonconstant convention is checked carefully: factorization through a k-point agrees here with the single-point-image convention used by Stacks, because the source is reduced and closed points of a finite-type scheme over algebraically closed k have residue field k.

The ancestor command prints blueprint.from.node = None for this item. I retained that inherited ancestry and its precise place and via list; the entire imported ancestry ends before an is-tagged blueprint node. The extension node inherits that result and prepends this item to via. Searches of all blueprint nodes for function field, rational map, proper curves, valuation rings, proper target, 0BX7 and 0BXZ found no node with the new extension statement. The existing completion lemma lem-pur-smooth-curve-map-completion concerns a given nonconstant map of smooth curves and chosen completions, with finite locally free conclusion; it does not assert extension of arbitrary maps from a generic field on arbitrary integral schemes with valuation stalks. The Conrad proper-target extension nodes permit modifying the source, which is a different conclusion.

## Not duplicates

The new node's source tag 0BX7 occurs in no existing node. It is not a clause of the item: it concerns arbitrary-dimensional integral schemes with valuation local rings and arbitrary proper targets, has no function-field embedding or curve correspondence assertion, and supplies only extension existence. The item retains nonconstancy/dominance, finite degree, the explicit construction from an embedding, uniqueness, and composition as arguments. No elementary field finiteness, constant-image factorization, or equalizer calculation became a new node.

## Review by Q14

I read Stacks curves.tex, lemma-extend-over-dvr (0BXY), lemma-extend-over-normal-curve (0BXZ), and theorem-curves-rational-maps (0BY1), especially its third proof paragraph. I checked morphisms.tex, lemma-extend-across (0BX7), whose reduced/finitely-many-components hypothesis holds for every integral source. I also read the actual project proof exists_hom_of_valuationRing_stalk, including its valuative lift at each stalk, spreading to a partial map, maximal domain equal to top, and resulting everywhere-defined map. This is the source justification and existing implementation for the sole new node; it is not a restatement of the equivalence being proved. Its valuation-ring condition is defined inline, and all its scheme, properness, base, spectrum and function-field notions have statement dependencies.

For step 1 I read all three clauses of lem-sc-smooth-connected-curve-local-rings and the integral-scheme definition. Integrality gives connectedness, so the hypotheses really are satisfied. The DVR fraction formula in clause 3, rather than the name DVR alone, proves the valuation property used later. The generic local ring is a field and is also a valuation ring; I did not incorrectly call it a DVR.

For step 2 I read the definition of finite-type morphism, the affine fraction-field statement, and lem-sc-closed-irreducible-dimension-trdeg. The last node gives the dimension/transcendence equality for the whole irreducible closed set C, unlike lem-sc-dimension-locally-algebraic, which only compares dimensions of opens. Thus I cite the former, not the latter. Choosing charts from a finite-type cover provides finite algebra generators; their fractions explicitly provide field generators. Dimension exactly one is a hypothesis of this item, not the weaker dimension-at-most-one convention of def-sc-curves.

For step 3 I read the point classification in the curve-local-rings node, the generic-point definition, the closed-immersion definition, the Nullstellensatz node's first clause, and the reduced-source closed-subscheme factorization node. A nongeneric image is closed, continuity makes the entire image that point, and the affine quotient realizes it as a closed immersion. Nullstellensatz applies on a chart of the finite-type cover. The factorization node assumes the source reduced, which follows from integrality, and actually asserts the factorization used. This rules out treating topological containment as a scheme factorization without justification.

For step 4 I read the function-field, residue-field, field-extension, scheme-over-base and affine-spectrum statements. The residue map is the generic stalk map because the local rings there are fields; a field homomorphism is injective. Compatibility with k follows from the commutative structural triangle, not from an arbitrary choice of embedding.

For step 5 I read lem-kun-transcendence-degree-tower, including its trdeg-zero iff algebraic clause, and the field-degree definition. The image field E is k-isomorphic to k(Y), and E and L are in the required tower. Both degrees over k are finite and equal to one. I also read lem-weil-pbc-algebraic-generators-finite-extension (Stacks Fields 09GH, lemma-algebraic-finitely-generated), an existing Mathlib leaf. After L = E(a_1,...,a_r) is written out, it applies with base E and ambient L, and gives the required finiteness. In final review I replaced the inline monomial-span proof with this existing leaf so that the algebraic finiteness input is explicit. It does not require separability, and the empty list of generators gives degree one.

For step 6 the affine fraction-field node gives the injection A into k(Y), and the affine-spectrum definition gives the resulting map Spec k(X) into the chosen affine chart. Kernel zero proves its image is the generic point. The quotient a/b formula verifies the induced map really is the given embedding. This is an explicit construction, not a hidden appeal to a full rational-map equivalence.

For step 7 I checked every hypothesis of the new extension node: k is a field, X is integral, its generic field is the one already constructed, its local rings are valuation rings by step 1, Y is proper, and h is over k by its construction. Its statement gives the restriction equality needed to identify the resulting pullback with phi. The point classification excludes constancy. I did not use uniqueness from the new node, since it does not state uniqueness.

For step 8 I read def-pc-fibre-product, the properness and closed-immersion definitions, part (b) of lem-weil-pbc-proper-fp-permanence, and the reduced-source factorization statement. The equalizer uses Y times_k Y, exactly the base over which properness supplies a closed diagonal. The generic morphisms are equal because their maps on an affine chart coincide. Thus the generic morphism factors through E, whose closed image is all of X. Reduced-source factorization supplies a section X to E, and f e = g e proves f = g. This avoids borrowing a relative version of a uniqueness lemma from its proof or blueprint_update while quoting a different stored statement.

For step 9 I read the scheme-as-locally-ringed-space and stalk definitions. The identity and composite formulas are evaluated on individual germs and use composition of the actual pullback maps. A composite still sends generic point to generic point and is therefore nonconstant. This verifies the domain of the composition assertion, not just its displayed algebraic identity.

I tested the main statement and the new node on identity maps, maps of degree one, constant maps, projective-line maps t to t^n, and in characteristic p the purely inseparable map t to t^p. The last has finite degree p and is not excluded anywhere. Removing properness would invalidate extension (the generic map t^{-1} from the affine line to itself), so properness is retained in the new lemma; no smoothness or dimension assumption was smuggled into that general lemma. A zero-dimensional field source also satisfies the valuation condition and makes its extension assertion tautological. Empty and disconnected sources are excluded where integrality is assumed. All nine steps are below 2000 characters. I checked delivery-errors B through E: new statements are self-contained and statement-only, all citations are actual statements, every non-elementary input is cited, no item clause was relocated wholesale, and no source or unit route was changed. Definitions and the generic field/geometric tools outside this unit are used only as auxiliary tools; the relevant tool uses are declared in split_report.

## Unfinished work

No part of the requested stage-1 split remains unfinished. The new node has no new proof because the contract calls for a statement-only child and the project extension theorem is already available for attachment review. No Lean was written or compiled; no git command was run in the read-only repository.

## Validation

The first server dry run passed at ab689cbfd24. Final review then added the existing algebraic-generators Mathlib leaf to step 5 and corrected the extension theorem source line endpoint. The dry run is repeated on this final version before pushing.
