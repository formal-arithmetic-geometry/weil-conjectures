# Worker report: thm-sf-pf-field

## Files written

- `dag/nodes/sec-six-functors/thm-sf-pf-field.json`: statement, split into six proof steps; seven actual Mathlib searches recorded, no exact Mathlib match.
- `dag/units/sk-thm-sf-pf-field.json`: only `realized` and `realized_by`, recording this key node against the inherited unit's statement and its one rationalization/common-stage proof paragraph.
- `citations.json`: one verbatim statement excerpt for every cited node of every proof step.
- `report.md`: this report. There are **0 new nodes and 0 new Mathlib leaves**.

## Attachments

No exact attachment. I searched the blueprint id and projection-formula/rationalization notions throughout `WeilConjectures/`. `AlgebraicGeometry.Etale.isIso_fromIntegral_map_projectionMap` (Rational.lean:82), `AlgebraicGeometry.Etale.isIso_reductionModIdeal_pow_map_projectionMap` (Rational.lean:113), and `AlgebraicGeometry.Etale.hasProjectionFormula_field` (Rational.lean:139), under `WeilConjectures/SixFunctors/Etale/Derived/ProjectionFormula/`, give only the rational map and invertibility of reductions of its integral representative. Their file explicitly says in its implementation notes that the common-stage algebraically closed category and finite scalar-extension compatibility have not been constructed/stated. The analogous pro-etale rationalization theorem in `SixFunctors/ProEtale/Derived/ProjectionFormula.lean` likewise does not supply those missing clauses. These are partial existing Lean, not an attachment of this item. No master sorry declaration was used as a finished proof.

## Wanted literature

None. The proof follows the available blueprint's coefficient-passage route and is marked `proof_origin.by = agent`; it does not claim a human-written source for this argument. Every source used is already in `literature/`. No SGA source was used.

## Statement clarified — STATEMENT-DISPUTED

The imported phrase “compatible ... with finite reduction” is ill-typed if it means a reduction functor out of a rational coefficient category. For the point with R = Z_l and E = Q_l, multiplication by l becomes invertible after rationalization, whereas multiplication by l on R/l is zero. Thus a coefficient reduction taking the rationalized integral unit to R/l and preserving its scalar maps cannot exist. Equivalently E tensor_R R/l = 0; tensoring the rational unit with R/l does not recover the reduction of the integral unit. One must retain an integral representative. This is also explicit in the accepted DAG statement of `def-exchange-projection` (“There is no reduction functor from rational coefficients to A_{E,n}”).

The statement now spells out the diagram from the integral projection map to its finite reductions and to its rationalization. It asserts no invariant finite reduction of a field object without a lattice. This is the intended reading supported by the blueprint proof, the integral theorem, and the actual Lean rational file's reduction theorem. It retains every field-stage isomorphism and coefficient-extension clause. No new finite-Tor hypothesis was imposed: integral models are arbitrary objects of the derived-complete D^b_c category, and Step 1 obtains their required uniform finite-Tor bounds from the existing `lem-coef-integral-residue-tor`. This repaired an initial draft that explicitly assumed finite-Tor integral models and could otherwise have narrowed the statement.

## Other corrections and blueprint correspondence

The imported one-paragraph argument hid the coefficient-comparison theorem and did not write the descent argument. I replaced this with explicit localization of the actual two factors of the projection map, the localized inverse, naturality on fractional morphisms, the finite-extension comparison square, and inverse classes in the common-stage Hom colimit. An arbitrary functor preserves an inverse; exactness is unnecessary for that step.

The current `main-20261015/.../sec-six-functors-basics/sk-thm-sf-pf-field/thm-sf-pf-field.md` and its `.proof.md` retain this node's original statement/route. The current `_section.md` is broader than the inherited unit record: it additionally addresses tensor closure and proper base change on localizing categories. This subordinate node is not a proof of those additional claims. I kept the maintainer-owned unit/chapter binding and filled only the realization fields of the supplied older unit record, whose statement is exactly the rationalization/common-stage assertion being split. No unit route was replaced. `blueprint.same_as` is empty because the all-stage `fix-prop-projection-formula` is a more general package, not the same statement; neither the localizing-stage claims nor notation definitions are aliases of this node.

The proof uses three existing statements as generic tools outside its inherited unit route: `lem-coef-integral-residue-tor` for uniform integral Tor bounds, `lem-fix-operation-reduction` for the coefficient comparisons and preservation of units/counits, and `lem-weil-scalar-extension-composition` for the transition identifications. They are declared in `split_report.tool_uses`. I did not set maintainer-owned `tool_uses` or use axiom (A3) as a shortcut to the conclusion.

## Mathlib and duplicate searches

All recorded queries were actually run through `/home/ubuntu/weil-launcher-nt/msearch.py Q73 thm-sf-pf-field`, using LeanFinder, Loogle, LeanSearch and grep, including a second formulation. All services answered; none was described as unavailable. Searches for the geometric theorem returned unrelated profinite, adic-completion and linear-projection facts. A second phrasing returned generic linear localization declarations. Loogle and grep found `CategoryTheory.Functor.map_isIso` in `Mathlib/CategoryTheory/Iso.lean:493`; I read lines 480–505. That is only the elementary preservation-of-inverse calculation, not the geometric theorem or identification of its projection map, so it does not finish the item and deserves no new node.

I searched the whole DAG by projection/rationalization/coefficient-passage keywords, and ran `tools/blueprint_refs.py search` for rational, projection, and the exact title “Rational and algebraically closed stages”. Those searches found the existing definitions and coefficient-comparison nodes used here. No new node was needed. The existing all-stage projection-formula package was read as a duplicate/generalization check, not used to replace the assigned integral-to-rational route.

## Not duplicates

No new nodes, hence no new/existing node pairs sharing a source tag.

## Review by Q73

I read the current main-20261015 statement and proof of `thm-sf-pf-field`, the current integral `thm-sf-pf-adic` statement/proof, the current `lem-fix-operation-reduction` statement/proof, the rationalization and common-stage definitions, the operation definitions, and the finite scalar-extension composition statement/proof. I also read the current residue-Tor statement/proof and the stronger accepted DAG statement explaining its pro-etale domain. These are blueprint sources, not Stacks citations; no new source-tagged node is being proposed.

In Step 1 the cited residue-Tor statement says D^b_c = D^b_ctf for this actual derived-complete DVR category. Its hypotheses hold because l is invertible on every k-scheme here and each chosen model is in D^b_c. The integral projection theorem then supplies exactly the integral isomorphism and its normalized reductions; the definition only supplies the name of the map. This avoids inferring finite integral Tor amplitude merely from field coefficients, and avoids invoking the desired field axiom.

In Step 2 the three definitions identify the raw localization functor, localized tensor/pullback, and localized compact support. I checked that `lem-fix-operation-reduction` explicitly says the comparisons preserve tensor associativity, evaluations, units and counits, rather than merely comparing objects. The displayed definition of projection factors through the proper-factor projection mate followed by the open-immersion projection comparison. Applying preservation to these two factors identifies the actual rational morphism. The two inverse equations are written explicitly; no claim about transporting adjunctions through an arbitrary localization is assumed.

In Step 3 rational Hom groups and the bilinear action formulas come directly from the cited definitions. Integral naturality is part of the definition's specified natural transformations. Multiplying the two sides of its equality by the product of the two scalar coefficients proves fractional naturality, and additivity gives all arrows. Conjugating by specified presenting isomorphisms proves representative independence. These are elementary calculations, not a new descent lemma.

In Step 4 the operation-reduction statement gives the needed comparison isomorphisms and preservation of the actual primitive maps. The proof writes the source and target comparisons and derives the correctly oriented equation c_V T(p_E) = p_F c_U by composing the two factor squares. The inverse formula has the reverse comparisons in the correct order. Identity/tower identifications are the coherent supplied data in the exchange definition and the scalar-extension composition statement. These comparisons are used on the stated bounded coefficient domains, not on the unrestricted ambient unbounded category; no exceptional-adjoint hypothesis or internal-Hom extension theorem is invoked.

In Step 5 I checked that the common-stage definition really gives both finite-field representatives and the equality criterion after a further finite extension. For invertibility I use the class of the inverse at that same finite field and multiply there; faithfulness of a stage functor is unnecessary. Independence under field enlargement is Step 4, and arbitrary specified changes of presentations reduce over a further common field to the naturality equation from Step 3. The common-stage construction defines the operations on morphisms, so this is an elementary consequence of previous steps, not a hidden theorem about infinite scalar extension.

In Step 6 the integral theorem's statement explicitly includes compatibility with every finite reduction and normalized transition maps. The operation-comparison statement identifies their endpoints and primitive maps. The only finite reductions are reductions of p_0. This is exactly where the original ambiguous sentence was repaired: no reduction functor out of E or Qbar_l appears anywhere.

I checked sections B–E against the actual files. There are no new statement-only nodes to audit and no Mathlib leaf claimed. Each proof `uses` is represented by an actual statement excerpt in `citations.json`, rather than by a fact extracted from another proof. The union of these lists is `proof_deps`. None of the cited statements has a dependency path back to this item; I checked this against the complete current DAG, including the residue-Tor addition. The inherited unit's integral/rational/common-stage route is kept, with generic off-unit tools declared. All notions in the expanded statement have statement dependencies.

Small cases checked were K_0 = 0 or L_0 = 0 (both maps are the unique isomorphism between zero objects), f = identity (the specified projection comparison specializes to the identity/unit comparison), E = F (the coefficient comparison is identity), a tower E contained in F contained in G (the intermediate comparisons cancel), unequal initial coefficient fields (take their compositum), and two different integral lattices inside the same rational object (field naturality holds but their reductions are not asserted canonically equal). The counterexample with multiplication by l on the coefficient unit distinguishes precisely the impossible reduction interpretation. No geometric, coefficient-category, finite-Tor, or uniformity hypothesis is silently added.

## Remaining work

Server `check_dag` and `review_split` passed. The first delivery dry run required a longer residue-Tor quotation (the displayed equality alone was shorter than its 40-character minimum); I replaced it with the exact statement passage giving both the uniform Tor interval and the equality of subcategories. No mathematical split step remains open. A fresh second reader must inspect this sandbox and deliver it; this worker does not push. The server dry run is the required final check, and its result is recorded by the delivery tool.

## Second reading by Q73

- Item statement: checked against the current `main-20261015` blueprint statement and the imported `def-sf-datum`, rationalization, compact-support, projection, and common-stage definitions; verdict: the integral-representative formulation preserves the field-stage, finite-extension, and finite-reduction clauses and explicitly avoids an ill-typed reduction functor from rational coefficients.
- Step 1: checked against `lem-coef-integral-residue-tor`, `thm-sf-pf-adic`, `def-sf-pf`, and the six-functor datum; verdict: the hypotheses give the required uniform finite-Tor bounds and the cited integral theorem supplies the isomorphism and actual finite reductions.
- Step 2: checked against the rationalization, operation, compact-support, coefficient-comparison, exchange, and projection definitions; verdict: localization of both factors identifies the specified rational projection map, and the displayed functor-law equations prove its inverse.
- Step 3: checked against the Hom-localization and linear-operation definitions and the naturality clause of `def-exchange-projection`; verdict: bilinearity handles fractional arrows and the common-stage presentation argument is elementary from those statements.
- Step 4: checked against `lem-fix-operation-reduction`, `def-exchange-projection`, and `lem-weil-scalar-extension-composition`; verdict: the source and target comparison squares are oriented correctly, their middle comparison cancels, and the inverse and tower formulas follow.
- Step 5: checked against the common-stage category and operation definitions; verdict: a common finite field represents both inputs, the inverse equations hold at that stage, and the colimit equality criterion gives presentation independence.
- Step 6: checked against the finite-reduction clause of `thm-sf-pf-adic`, coefficient reduction comparisons, and `def-exchange-projection`; verdict: only reductions of the chosen integral map are asserted, with the rational and algebraically closed maps obtained from the same representative.
- New nodes: none; there were no new statements or Mathlib leaves requiring B1–B7 review.

Changes made in this second reading: appended this per-step audit; no node or citation was changed because every cited statement was present verbatim in `citations.json`, the dependency union matched `proof_deps`, and the worker's existing source clarification and edge-case checks were complete.
