# Worker report — repaired delivery

1. Files written:
   - dag/nodes/sec-smooth-purity/lem-route-exists-right-derived-lower-shriek-comp-iso.json: split, seven proof steps; the exact ordinary unbounded finite-ring statement is retained.
   - dag/nodes/sec-smooth-purity/lem-pur-etale-proper-open-exchange-cube.json: statement-only, unsplit, no Mathlib match; original statement retained, source corrected to include Stacks 0F7E and 0F7F.
   - dag/nodes/sec-smooth-purity/lem-pur-etale-graph-comparison-base-change.json: statement-only, unsplit, no Mathlib match; retained single-morphism graph cocycle, pullback and refinement-API normalization.
   - dag/nodes/sec-smooth-purity/lem-pur-etale-graph-comparison-interchange.json: NEW in this repair, statement-only, unsplit, no Mathlib match; the elementary presentation-move normalization and the missing C/Gamma square for two proper/open presentation diagrams.
   - citations.json: regenerated exact statement quotations for every citation in every proof step. searches.jsonl retains the original search results and the repair's actual msearch.py results. The old report is preserved as sandbox report-before-repair.md; the present report supersedes its mathematical review and validation claims.
2. Attachments: none. AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso at lean/WeilConjectures/SixFunctors/Etale/Derived/LowerShriekCompositionCoherence.lean:84 ends in sorry. Searching the whole project for the blueprint tag and rightDerivedLowerShriekCompIso finds no complete declaration establishing both clauses. nonempty_iso_rightDerivedLowerShriek_comp establishes existence only. It is not an attachment for this item or a citation for a specified coherent construction.
3. WANTED: none. No SGA is used; no Lean is written or compiled.
4. The maintainer identified a real gap in the delivered Step 5, not an issue cured by rebase. The Gamma cube did not relate graph comparisons to Gamma. The repaired proof cites a separate precise statement for that relation and explicitly uses its equation. The item's statement is unchanged: finite commutative ring, ordinary unbounded small-etale categories, arbitrary schemes and non-quasi-compact unprimed opens, quasi-compactness of f',g',h' only. There is no STATEMENT-DISPUTED.
5. Stage-1 assembly is complete; three new nodes remain deliberately unsplit for later workers. The earlier two nodes and their proofs-to-be, source citations and actual logged searches are retained. This repair adds one obligation, not a purported finished Lean proof of those obligations.

## Route and current repository

Read AGENTS.md, roles/worker.md, coord/brief-stage1.md, stages/1-dag.md, SETUP.md (all three levels and the generic-tool exception), GOAL.md, coord/STATE.md, tools/README.md, and both copies of delivery-errors.md B–E. Read dag/chapters/sec-smooth-purity.json and dag/units/sk-prop-sf-cbc.json. The chapter and unit are untouched. There is no released stage-1 repair-note file for this id; the explicit return in the brief is the repair order. The current repository item is unsplit. I compared it with the retained delivered version and rebased only the split-owned fields onto the current item, retaining the current source, title, Lean and ownership metadata. The previous dry-run head recorded in the report was 3d2acfc7909; the retained work, rather than an empty restart, was dry-run first and passed again at ef7f1de8966. Neither pass is treated as a mathematical repair.

The newest blueprint is read exclusively through literature/blueprint/latest; COMMITS.txt names 7284bb09daf97437d544c51882b325f9c52cd345. Read prop-asd-smooth-base-change.proof.md coherences (i),(iii), the current sk-prop-sf-pf-coherence proof, the composition proof and det-sf-comp-composition-interchange and its proof, and the package's composition/base-change clause. Their more restricted pro-etale or constructible statements are not silently substituted for this ordinary unbounded finite-ring item. This remains the compactification/graph route below the node level. The new graph/interchange lemma is an explicit strengthening needed for the actual upstream graph normalization; the proof is marked agent-written, not attributed wholesale to the blueprint or Stacks.

Whole-DAG, current-blueprint and project-Lean searches were repeated for the changed search question: graph comparison, proper/open interchange and choice/refinement compatibility. blueprint_refs.py searches for graph comparison and 0F7J have no blueprint match; interchange and proper/open return the restricted composition/interchange nodes discussed below. The computed ancestor still prints None because the maintainer-created parent's created.item chain ends at a module rather than a node. New nodes keep the required computed null from.node and explicit from.place/via; the item's existing prop-asd-smooth-base-change ancestor is retained. No parent metadata or launcher tool is changed.

## Review by NC

I checked the source signature, including the surrounding finite-ring variables, against every hypothesis and direction. ProjectionTensorMap.lean:346-349 specifies the projection equation with E:F_h -> F_g F_f and h* -> f*g*. Lines 485-499 specify the exchange equation c*F_h -> F_g' F_f' a*. LowerShriekBaseChange.lean:150-168 defines the actual exchange as the proper-plus-open exchange followed by rightDerivedLowerShriekIso. LowerShriekIndependenceUnbounded.lean:203-225 fixes that latter map by Compactification.inf and its two proper-refinement maps. The retained graph-comparison node's last clause identifies precisely that map under primed quasi-compactness.

For the cube node I reread Stacks more-etale.tex Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (vertical pasting), 0F7D (horizontal pasting), 0F7E (remark-going-around) and 0F7F (lemma-shriek-proper-and-open-base-change). In 0F7B(b) the torsion ring allows all unbounded inputs. Open immersions are the present special case. The original square need not be Cartesian: its two routes through support extension give the same sheaf, and the comparison uses the indicated K-injective representative. The cube is precisely the assertion of 0F7F, and the grid is 0F7E. Only its equality with the specified Cartesian unit/open-mate/counit map is an extra normalization assertion, as already specified by lem-sf-etale-proper-open-tensor-square. I corrected the source field's old claim that the cube itself was agent-stated.

For the retained single-map graph node I read lem-sf-etale-locally-closed-graph-model's whole statement and LowerShriekComposition.lean:193-268: the two product opens, their intersection, the proper graph maps and eA/eC/eB factors. The retained node states cocycle, base change and equality with the actual refinement API. It says nothing about C commuting with a composition interchange; it is now used only for the claims it actually states.

For the NEW graph/interchange node I read Stacks 0F7J (lemma-shriek-composition) through the final A-F diagram calculation, plus 0F7I (single-map independence), and the actual graph eh factor at LowerShriekComposition.lean:344-372. The source's final equalities compare proper/open tower maps with refinement maps. Our new statement deliberately extends that identification to the specified product-graph maps and proper/open/proper presentations on arbitrary schemes with supplied compactifications. This extension is explicitly agent-stated and unsplit. Its first equation identifies the missing H-to-S map: inverse Gamma for a proper map factoring through an open, whiskered by the other open and proper factors. Its second equation says exactly C_s I_1 = I_2 (C_d F_t2) F_d1(C_t), and introduces every scheme, map, factor and equation. It assumes neither a morphism between the two diagrams nor quasi-compact opens. It asserts no inverse-image or tensor equation, no family E, and no existence of an auxiliary tower. Thus it is a smaller normalization lemma genuinely missing from the old proof, not a restatement of either clause of the item.

Step 1 cites the graph clause of lem-sf-etale-compact-projection-coherence and the fully specified graph model of lem-sf-etale-locally-closed-graph-model. Those statements give this particular product-graph realization, with proper graphs into the indicated opens. I checked its P,O,V,W and a,a' against the explicit upstream construction. No arbitrary isomorphism is extracted from lem-etale-unbounded-compact-support-composition, whose existence-only statement has been removed from the proof citations. None of the two actual inputs assumes Noetherianity or quasi-compactness of the opens.

Step 2 cites the cube node for the specified Gamma, the NEW node's first clause for C_{S,H}, and the retained graph node for its cocycle. The square with top identity, bottom u and verticals a',a has proper verticals and open horizontals. The relation ua'=a gives its commutativity; e u=k e' is the pullback relation for W. This explicitly performs the omitted passage from the h-presentation through O (the open isomorphic to X x_Z Ybar_g) to W (isomorphic to X x_Z Y). The formula E=(G B_f^-1) I^-1 C_{S,H} B_h has the exact e1/e3/e2 direction of the source graph proof. The projection-coherence node identifies this same graph word as the E for which its second identity holds. A uniform recipe fixes the family before either requested compatibility is deduced.

Step 3 takes invertibility of the specified projection from lem-sf-etale-ambient-adjoint-projection and the second identity from lem-sf-etale-compact-projection-coherence. I checked both full statements on the ordinary unbounded domain and the h* to f*g* compositor. The step cancels q_h pi_h, pi_g q_g and F_g(pi_f q_f), so this step is elementary once those two cited results are supplied. No projection composition assertion is being proved by an unrelated adjoint uniqueness claim.

Step 4 uses the full statement of lem-weil-pbc-mate-pasting: both directions of pasting and change of adjunctions identify the squares for proper compositors. lem-asd-open-base-change-unit-mate gives the actual unit-normalized open mate; lem-cbc-extension-zero-composition specifies the composite open comparison. The cube node gives the square for both Gamma factors, including the one at u, and the graph node gives those for B_h,B_f and their inverses. Each input is unbounded or categorical and has exactly the stated normalizations. Step 5 is only substitution/pasting of those factor equalities; it does not make the choices-independence claim that caused the return. Fibre-product association here is its universal-property identification, and the endpoint exchanges are written out.

Step 6 instantiates the NEW node's SECOND equation with the pulled-back and supplied-primed graph diagrams. Both live on the same X',Y',Z', their squares have proper verticals/open horizontals and their presented composites are f',g',h'. Presentations of f' and h' have the required supplied open-then-proper factorizations. It takes the two exact cocycle equations from the retained graph node, substitutes them into the new interchange equation, and applies naturality of kappa_g. The displayed calculation gives E' kappa_h = (kappa_g F_f') F_gb(kappa_f) E_b. This time the cited statement contains precisely the C/Gamma compatibility being used. No step infers it merely by drawing a Gamma grid. Step 7 uses only the retained graph node's quasi-compact refinement identification and elementary substitution into Step 5, obtaining the specified API exchange equation.

The old compatible-tower citation and finite-type/separatedness detour are removed. Their hypotheses did not justify passage from E_b,E' to a tower word, and quasi-compactness of the open parts was also uncited. The repaired argument makes no use of that theorem or a quasi-compact-open assertion. It therefore needs no extra geometric hypothesis and no extra elementary quasi-compactness node. All uses of primed quasi-compactness are now exactly the last refinement-API clause of the retained graph node.

I replaced boilerplate tool_uses with individual explanations. In particular lem-sf-etale-compact-projection-coherence is explicitly the entire independent graph projection-pentagon input for clause (1), not a generic base-change lemma. The CBC unit has no tensor/projection composition statement, so its second identity is legitimately an off-unit generic projection tool below the fixed graph route; Step 3 proves clause (1) from that input by inversion. The graph-model node provides endpoint maps absent from the CBC unit, the ambient projection node provides only invertibility, and mate-pasting is the coefficient-independent categorical identity for individual graph factors. Nothing in these tool declarations substitutes another unit's proof for the compactification/base-change route.

I reviewed B–E point by point: new files have statements only and empty proofs; the coefficient domain, all objects, maps and hypotheses are explicit; all notions have their actual defining/corresponding statement dependencies; formulas are derived-category transformations with readable TeX. Every proof citation was opened and citations.json quotes its actual statement. A cited definition is never used as a missing theorem. The three helpers are neither elementary steps nor item clauses; each has independent nontrivial normalization content, and the item retains its actual graph construction, projection cancellation, factorwise base change, comparison algebra and final substitution. None of the seven steps exceeds 2000 characters. No cycle is introduced: the new interchange node depends on the two retained helper nodes and existing proper/open notions, never on this item or its conclusion.

Small-case and typing checks: identity presentations make C=1 and identity squares give the proper/open unitors; if the two diagrams coincide the new interchange equation is I=I; its first clause has inverse Gamma from R_a to J_u R_a', the required direction. Empty source opens give zero functors, and the zero ring gives the zero derived category. In the new square both sides have source F_d1 F_t1 and target F_s2, including the crucial whiskering C_d F_t2 after F_d1(C_t). No assertion of properness for an open is used. Non-Cartesian proper/open squares are allowed exactly as in 0F7B. The arbitrary opens remain arbitrary everywhere: there is no covert appeal to Nagata, finite type, finite Tor amplitude or a bounded-below result.

The original logged Mathlib searches were read and retained, not rerun. For the new helper msearch.py ran LeanFinder twice with different descriptions, LeanSearch, Loogle and source grep. I read the hits: scheme properness/restriction and gluing results do not state the equality; module-sheaf pushforwardComp is an ordinary compositor, not graph comparison compatibility. Mathlib/CategoryTheory/Adjunction/Mates.lean:170,209 (also 350 for conjugates, read in the original work) gives the general mate pasting equations, but identifying the specified graph C with those interchanges is not a one-line specialization. The new node is therefore unsplit, not a Mathlib leaf. The invalid earlier Loogle identifier query remains recorded unavailable; no successful query is invented and no down service is described as a negative search.

## Return points repaired

- E5/D5: the missing C/Gamma compatibility is now its own explicit statement-only node, and Step 6 uses its exact equation with both graph diagrams before the elementary endpoint substitution.
- C1: removed the tower lemma and its unproved quasi-compact-open application; the new comparison argument uses only supplied arbitrary-open graph diagrams.
- C4: removed the existence-only composition citation as a construction claim; Step 2 now writes the extra H/S interchange omitted before.
- B5: attributed the cube to 0F7F and grid to 0F7E, keeping the extra adjunction-normalization obligation explicit.
- Tool declarations: replaced every boilerplate explanation, including the specific justification for the projection-coherence tool carrying all of clause (1).

## Not duplicates

lem-pur-etale-proper-open-exchange-cube vs lem-sf-ambient-clopen-restriction-uniqueness: the existing “Clopen factorization and restriction uniqueness for proper/open sheaf maps” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-clopen-comparison-tensor-square: the existing “Tensor squares for open base change and the clopen comparison” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-projection-refinement-descent: the existing “Projection mates descend along non-Cartesian compactification refinements” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-unbounded-compact-support-proper-composition: it assumes the first map proper and all schemes separated finite type over a field; it asserts a proper-composition isomorphism, not the arbitrary-presentation graph/interchange equation.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-ambient-proper-open-pasting: the existing statement is finite-type over a fixed algebraic closure on pro-etale or semilinear-system categories; the new statements are ordinary etale over arbitrary schemes and finite commutative rings.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-native-weil-compactification-model-comparison: the existing statement asserts “Native Weil compactification models under proper refinement”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-strict-reduction-compact-support-normalization: the existing “Coherent normalization of strict reduction compact-support exchanges” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-ambient-exact-clopen-comparison-localization: the existing “Exact localization identifies the intrinsic clopen comparison and its mate” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-integral-compactification-comparison-bridge: the existing “Constant-tower and semilinear-counit normalizations of integral compactification composition agree” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-completed-shriek-composition-laws: the existing “Completed shriek composition laws” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-exceptional-refinement-mates: the existing conclusion is “Exceptional coefficient construction: refinement mates”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-semilinear-alpha-pullback: the existing “Pullback cube for the intrinsic semilinear alpha transformation” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-semilinear-product-compactification-calculation: the existing “Product compactification mate calculation in semilinear systems” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-system-proper-open-scalar-square: the existing “Finite-free scalar extension of the intrinsic semilinear proper/open mate” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-native-weil-open-closed-triangle: the existing statement asserts “Native Weil open-closed triangle before taking compact image”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-native-weil-open-proper-interchange: the existing “Proper/open interchange for native bounded constructible Weil complexes” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-semilinear-scalar-ordinary-comparison: the existing statement asserts “Ordinary scalar restriction with section-normalized comparisons”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-integral-normalized-refinement-pasting: the existing “Integral refinement pasting for the prescribed normalized maps” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-finite-exchange-projection-commshift: the existing “Finite geometric exchange and projection commute with shifts” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-compact-support-limit-equation-realization: the existing “Realization of compact-support path equations through the completed limit” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-semilinear-proper-open-mate-pasting: the existing “Intrinsic proper/open mates and pasting for varying coefficient systems” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-weil-basechange-semilinear-pasting: the existing statement asserts “Mixed geometric base-change and semilinear exchange pasting”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs def-coef-semilinear-proper-open-mate: the existing conclusion is “Canonical semilinear proper/open adjunction mate”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-kunneth-second-open-substitution: the existing “Second-open substitution and its proper/open projection square” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-composition-projection-mate: the existing statement asserts “Normalized compact-support composition satisfies the projection mate identity”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs def-sf-ambient-underived-clopen-comparison: the existing “Ordinary intrinsic clopen comparison and normalized open compositors” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-proper-open-projection-mate: the existing “Normalized proper/open interchange commutes with projection” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-finite-compact-support-evaluation-refinement: the existing “Finite evaluation normalization of compact-support exchanges and refinements” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-finite-projection-exchange-transposes: the existing “Finite projection exchange transposes” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the specified arbitrary-open Gamma, its two pastings and arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs def-sf-semilinear-proper-open-comparisons: the existing “Canonical semilinear proper/open compositors and intrinsic clopen comparison” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-integral-open-product-diagram-normalization: the existing conclusion is “Strict-diagram normalization of integral open product comparisons”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-ambient-underived-clopen-pasting: the existing “Vertical and horizontal pasting of underived clopen comparison maps” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-compact-coefficient-composition: the existing “Finite coefficient comparison respects compact-support composition” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-product-compactification-identity: the existing conclusion is “Product compactification identity for the exchange/projection composite”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs def-sf-integral-system-realization-data: the existing conclusion is “Canonical integral system realization and proper/open coherence data”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-etale-smooth-stratified-ctf: the existing statement asserts “Smooth-stratum finite-Tor devissage over an arbitrary algebraically closed field”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-package-compactified-tower-comparisons: the existing “Compactified direct-image towers, reduction and composition” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs def-sf-etale-support-compositor: the existing conclusion is “Canonical unbounded etale compact-support compositor”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-proetale-composition-tower-normalization: the existing “Pro-etale composition on a compatible tower has the open-adjoint normalization” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-compact-support-exchange-counit: the existing conclusion is “Compact-support exchange intertwines proper ordinary counits”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-compact-composition-proper-square-normalization: the existing “Compact-support composition along a proper square: closed and open normalizations” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-finite-horizontal-shriek-mate: the existing “Compact-support exchange as a mate along finite horizontal arrows” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-filtered-derived-operation-lifts: the existing “Filtered lifts of sheaf-derived operations and their canonical adjunction maps” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-proper-unit-localization-composition: the existing “Proper-endomorphism units commute with open and closed compact-support composition” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-compact-composition-tower-formula: the existing “Computing finite pro-etale compact-support composition on a compatible tower” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-finite-structural-maps-commshift: the existing “Canonical finite-coefficient structural maps commute with shifts” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-proper-composition-site-transport: the existing “Site comparison preserves compact-support composition with a proper factor” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-trf-proper-open-site-transport: the existing “Site comparison preserves finite proper/open interchange” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-proper-open-tower-single-unit-formula: the existing conclusion is “Single derived-unit formula in a proper/open tower”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-proper-open-tower-successive-unit-formula: the existing conclusion is “Successive derived-unit formula in a proper/open tower”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-proper-open-tower-derived-unit: the existing “Derived-unit resolution calculation in a proper/open tower” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-tame-pair-lattice-realization: the existing “Realization of an integral lattice stratum by a proper tame pair” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-etale-compact-projection-coherence: it gives tensor/projection identities for one normalized graph compositor, not the normalization of arbitrary presentation changes against Gamma or a Gamma base-change cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-tame-pair-proper-generators: the existing “Proper tame-pair generators for finite-field constructible complexes” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-etale-proper-open-tensor-square: it gives Cartesian Gamma and its tensor equation, not arbitrary-square pasting, its base-change cube or compatibility with graph C.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-exact-compactification-unit-refinement: the existing “Normalized exact compactification units respect canonical refinements” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-quasifinite-compact-support-exact: the existing “Quasi-finite compact support is exact and agrees with compactifications” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-sfb-exact-compactification-unit-composition: the existing “Composition of normalized exact compact-support units” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-etale-locally-closed-graph-model: it defines a single specific invertible product-graph B; it gives no C cocycle, graph pullback equation or graph/interchange equation.

lem-pur-etale-proper-open-exchange-cube vs lem-weil-pbc-etale-shriek-qcqs-composition: the existing statement asserts “Composition of qcqs etale compact-support candidates”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-weil-pbc-etale-open-proper-interchange: the existing statement asserts “Open extension by zero and proper derived pushforward interchange”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-weil-pbc-etale-shriek-compactification-independence: the existing statement asserts “Compactification independence on the qcqs etale site”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-proper-open-adjunction-normalization: the existing “Adjunction normalization of unbounded proper/open interchange” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-proper-open-clopen-projector: the existing “Clopen lift and adjunction-normalized component projection for a proper/open square” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-clopen-tensor-compatibility: the existing “Proper/open tensor-mate interchange on varying-coefficient systems” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-weil-pbc-proper-open-identification-unit: the existing statement asserts “Unit normalization of the proper/open restriction identification”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-compact-support-graph-sheaf-normalization: the existing “Graph comparison agrees with the canonical map into direct image” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-normalized-proper-open-pasting: the existing “Horizontal pasting for fixed normalized proper/open comparisons” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-complete-proetale-composition-pasting-coherence: the existing “Composition Pasting Coherence” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-ordinary-vertical-pasting-transport: the existing conclusion is “Transport of a vertical square-pasting equation through coherent comparisons”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proper-open-coefficient-mate: the existing “Coefficient and site squares for cartesian proper/open interchange” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-exc-proetale-finite-cd-proper-open-interchange: the existing “Deriving proper/open support under all-sheaf finite cohomological dimension” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-clopen-mate-identification: the existing “Identification of the intrinsic strict-system clopen arrow and proper mate” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-etale-adjoint-locality: the existing “Etale localization of the ambient adjoint” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-proper-open-interchange: it assumes Noetherian schemes throughout; the new assertions retain arbitrary schemes and, for the graph helper, add the missing graph C/Gamma identification.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-compact-support-graph-geometric-base-change: the existing comparison is for etale maps at a geometric-point base change; the new graph statement covers arbitrary compactifiable maps and arbitrary base maps.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-strict-tower-composition-maps: the existing conclusion is “Canonical strict-tower composition comparison maps”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sf-proper-open-comparison-site-normalization: the existing “Normalization of the proper/open comparison under the site comparison” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-diagram-open-clopen-shift-models: the existing “Section models for open and clopen integer-shift squares on ring diagrams” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-exc-proetale-cartesian-open-injective-acyclic: the existing “Proper acyclicity of injectives extended from an arbitrary Cartesian open” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-open-extended-injective-proper-acyclic: the existing conclusion is “Open extension of an injective sheaf is acyclic for the proper right-hand map”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-normalized-proper-open-geometric-normalization: the existing result assumes D+ and supplied normalized maps; the new statement is unbounded and constructs its Gamma.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proper-open-derived-support: the existing “Proper pro-etale direct image preserves extension-by-zero support” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-tower-geometric-composition: the existing conclusion is “Geometric composition and exact etale sum-extension”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-compact-support-open-source-composition: the existing “Compact-support composition with a source open” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-finite-clopen-mate-site-transport: the existing “Counit-normalized etale/pro-etale transport of the finite clopen mate” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-finite-constant-coefficient-transport: the existing “Normalized finite scalar and etale-origin transport to constant coefficient modules” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proper-open-tower-refinement: its conclusion compares proper refinements of compatible quasi-compact towers in an assumed calculus; it neither constructs nor identifies arbitrary proper/open/proper product-graph comparisons.

lem-pur-etale-proper-open-exchange-cube vs lem-exc-cartesian-open-finite-stage-hypercohomology-model: the existing “Finite-stage hypercohomology model for a Cartesian open extension” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-etale-compact-comparisons: the existing “The etale compact-support comparisons” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-compact-support-integral-coefficient-comparison: the existing “Integral compact support under finite free coefficient extension” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-compact-support-finite-graph-isomorphism: the existing “The specified graph comparison for finite etale morphisms” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-proper-open-invertibility: the existing “Invertibility and finite normalization of varying-ring proper/open mates” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proetale-proper-boundary-cohomology: the existing “Boundary cohomology of an open-extended pro-etale injective on a proper scheme” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-shriek-open-tower-counit: the existing “Open compact-support composition on the pullback tower” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-etale-clopen-mate-normalization-data: the existing “Derived etale clopen mate normalization data” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs def-sp-varying-ring-clopen-arrow-factors: the existing conclusion is “Separate the cartesian lift and clopen section factors before taking mates”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-cartesian-lift-pullback-equivalence: the existing conclusion is “Cartesian clopen lifts and equivalence of varying-ring inverse image”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-refinement-constructible-domain: the existing “Constructible domain and finite normalization of system refinement inverses” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-sp-varying-ring-proper-open-arrows: the existing conclusion is “Intrinsic varying-ring clopen proper/open arrows”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-proper-open-pasting: the existing “Clopen proper/open projections and pasting over a varying ring system” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-proper-open-base-change: it assumes Noetherian schemes and normalized Gamma as data, whereas the new Gamma cube is unrestricted and constructs that normalization.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-finite-compact-site-coherence: the existing “Finite-ring compact-support site comparisons respect refinements and towers” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-pur-system-tensor-mate-arrows: the existing “Canonical tensor and proper/open arrows for varying coefficient systems” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-closed-section-compact-origin: the existing “Identity-normalized compact origin for a map out of a closed section” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-complete-proetale-refinement-exchange-coherence: the existing “Refinement Exchange Coherence” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-proper-open-pasting: the existing pasting theorem assumes Noetherian schemes and supplied normalized maps; the new actual interchange/cube is over arbitrary schemes.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-compact-support-site-coherence: the existing “Compact-support site comparison respects compactification calculus” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-compact-support-strict-scalar-refinement: the existing “Scalar mate compatibility with strict compactification refinements” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-compact-support-comparisons: it assumes Noetherian schemes and separated finite-type maps; the new graph/interchange assertion is for arbitrary schemes, arbitrary supplied opens and proper/open/proper presentations.

lem-pur-etale-proper-open-exchange-cube vs prop-exc-base-change-proper: the existing “Base change for a proper morphism, against an open immersion” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-proper-open-horizontal-composition: the existing “Horizontal composition of unbounded proper/open interchange” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs fix-lem-exchanges: the existing “Exchange functoriality: naturality, identities, and pasting” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-etale-local-compact-support-extension: the existing “Zariski-local extension of etale compact-support functors and exchange morphisms” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-finite-site-tower-paste: the existing “Finite-site comparison of the proper/open compatible-tower word” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-shriek-tensor-composition: the existing statement asserts “Tensor projection maps respect compact-support composition”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-clopen-arrow-evaluation: the existing conclusion is “Compose the separately evaluated clopen arrow factors”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-open-base-change-evaluation: the existing conclusion is “Normalized coefficient evaluation of cartesian open base change”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs def-asd-compact-support-graph-comparison: the existing conclusion is “The specified sheaf and unbounded derived graph comparison”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-compactification-refinement-coherence: it assumes an abstract proper/open calculus and quasi-compact compatible-tower geometry; it has no identification of the concrete arbitrary-open graph comparisons with Gamma.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-reconstructed-pair-refinement-coherence: the existing “Refinement coherence of reconstructed exceptional representing pairs” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proper-open-comparison-normalization: the existing conclusion is “Structural normalization of explicit proper/open comparison”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-compactification-pf-substitution: the existing “Refinement comparisons intertwine strict-system projection maps” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-compatible-compositor-normalization: the existing “Compatible-triangle word for the geometric semilinear compositor” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-compact-support-graph-derived-isomorphism: the existing “Invertibility of the specified graph map on unbounded complexes” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-compact-support-staircase-expansion: the existing “Expansion of binary compact-support tower comparisons on a fixed staircase” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-unbounded-proper-open-composition: the existing pasting theorem assumes Noetherian schemes and a supplied normalized Gamma; the new actual interchange/cube is over arbitrary schemes.

lem-pur-etale-proper-open-exchange-cube vs lem-exc-proetale-proper-open-sheaf-comparison: the existing “Proper/open comparison for pro-etale module sheaves” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-natural-transformation-whisker-exchange: it is the general elementary naturality interchange of two transformations; it does not identify these specified geometric graph and proper/open maps.

lem-pur-etale-proper-open-exchange-cube vs lem-exc-etale-origin-proper-open-interchange: the existing “Site transport preserves the canonical Cartesian proper/open interchange” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-refinement-coefficient-mate: the existing “Coefficient and site squares for the explicit refinement theta” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-compactification-projection-composition: the existing statement asserts “Projection maps respect the explicit proper/open compactification tower”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-coprojection-composition-mate: the existing “Co-projection composition is the mate of projection associativity” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-tower-composition-refinement: it compares D+ compatible towers connected by proper refinement maps; the new graph/interchange assertion is unbounded, uses proper/open/proper presentations and requires no map between its two diagrams.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-proper-open-refinement-adjoint-projection: the existing statement asserts “Adjoint of the unbounded proper-open refinement comparison”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-etale-compact-support-normalization: the existing “Normalization of compactified etale support and its exchange” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proper-open-tower-comparison: the existing “Open-adjunction normalization of proper/open interchange on strict coefficient towers” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-strict-tower-ordinary-proper-open-arrows: the existing “Unit-normalized ordinary proper and open arrows on strict towers” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-strict-tower-open-extension: the existing conclusion is “Normalized exact open extension on strict constant-coefficient towers”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-system-level-projection-formula-coherence: the existing “Strict-system projection formula composition coherence” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-strict-tower-proper-open-calculus: the existing “Normalized proper/open calculus on strict pro-etale towers” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-section-compact-source-exchange: the existing “Normalized compact-support source and arbitrary exchange for a closed section” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-etale-closed-chart-exceptional-preservation: the existing conclusion is “Exceptional inverse image on a closed affine-space chart”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-clopen-section-evaluation: the existing conclusion is “Normalized coefficient evaluation of the clopen section factor”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-etale-horizontal-support-tower: the existing “Etale compact-support composition on a pullback compactification tower” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: the existing “The cartesian open comparison on varying-ring systems relabels lifts” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-etale-clopen-mate-normalization: the existing “The finite etale clopen mate has the proper-support resolution normalization” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-shriek-open-exchange-adjoint: the existing “Open compact-support exchange is the extension-composition mate” has the geometric/coefficient setting written in its statement; the new Gamma calculus with its cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-compact-support-graph-sheaf-normalization-transpose: the existing conclusion is “Transpose of graph comparison”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-asd-compact-support-graph-coherence: the existing result concerns an etale-map sum/compact-support graph comparison over locally Noetherian quasi-compact bases; the new graph comparison concerns arbitrary compactifiable maps and their proper/open/proper presentations.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-finite-site-counit-projection-transport: the existing “Finite site comparison preserves counit and projection transposes” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the specified arbitrary-open Gamma, its two pastings and arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proetale-open-injective-proper-acyclic: the existing “Open-extended injectives are proper-direct-image acyclic on pro-etale sites” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-line-zero-class-exchange: the existing “Normalized exchange and geometric-fibre identification of the zero-section compact class” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-varying-ring-ordinary-clopen-evaluation: the existing conclusion is “Ordinary coefficient evaluation preserves the single-square clopen arrow”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs thm-amb-vector-bundle-purity: the existing “Vector-bundle purity before smooth orientation” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-strict-constant-tower-operations: the existing “Strict constant-coefficient towers and normalized inverse/direct-image operations” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs def-cbc-strict-tower-proper-open-arrows: the existing “Unit-normalized proper and open arrows on strict towers” concerns its stated pro-etale/adic or system operations; the new proper/open Gamma cube is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-proper-open-exchange-cube vs lem-amb-derived-compact-support-composition-coherence: the existing conclusion is “Structural coherence of three derived images and open extensions”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-proper-open-coefficient-mate-transposed: the existing statement asserts “Transposed coefficient mate identity for proper/open interchange”; the new normalized arbitrary-open proper/open interchange, its two pastings and cube is a different assertion and assumes none of that application-specific data.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-etale-chart-compact-support-normalization: the existing “Unbounded compact-support normalization on a closed affine chart” has its stated bounded-below domain; the new Gamma calculus/cube is asserted on every ordinary unbounded input.

lem-pur-etale-proper-open-exchange-cube vs lem-pur-refinement-inverse-mate-comparisons: it supplies single-map cocycles from assumed refinement maps and explicitly assumes no non-refinement proper/open comparison; the new graph/interchange square relates the actual graph C to Gamma.

lem-pur-etale-proper-open-exchange-cube vs def-sp-proper-open-calculus: it defines assumed proper/open data for quasi-compact opens, without proving that the concrete arbitrary-open product-graph C has those normalizations.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-proper-open-interchange-coherence: its Gamma, pasting and cube are only on D+; the new assertion is on all ordinary unbounded inputs and additionally identifies the specified graph C where relevant.

lem-pur-etale-proper-open-exchange-cube vs lem-sp-ordinary-horizontal-pasting-transport: the existing conclusion is “Transport of a horizontal square-pasting equation through coherent comparisons”; it does not assert the specified concrete unbounded proper/open Gamma together with both pasting equations and its arbitrary-base cube.

lem-pur-etale-proper-open-exchange-cube vs lem-cbc-proper-open-alpha-pasting: the existing alpha equations are on pro-etale strict towers with quasi-compact opens; the new Gamma equations are on ordinary etale D with arbitrary opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-unbounded-compact-support-proper-composition: it assumes the first map proper and all schemes separated finite type over a field; it asserts a proper-composition isomorphism, not the arbitrary-presentation graph/interchange equation.

lem-pur-etale-graph-comparison-base-change vs lem-sf-ambient-proper-open-pasting: the existing statement is finite-type over a fixed algebraic closure on pro-etale or semilinear-system categories; the new statements are ordinary etale over arbitrary schemes and finite commutative rings.

lem-pur-etale-graph-comparison-base-change vs lem-pur-strict-reduction-compact-support-normalization: the existing “Coherent normalization of strict reduction compact-support exchanges” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-integral-compactification-comparison-bridge: the existing “Constant-tower and semilinear-counit normalizations of integral compactification composition agree” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-completed-shriek-composition-laws: the existing “Completed shriek composition laws” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-semilinear-product-compactification-calculation: the existing “Product compactification mate calculation in semilinear systems” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-integral-normalized-refinement-pasting: the existing “Integral refinement pasting for the prescribed normalized maps” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-pur-compact-support-limit-equation-realization: the existing “Realization of compact-support path equations through the completed limit” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-semilinear-proper-open-mate-pasting: the existing “Intrinsic proper/open mates and pasting for varying coefficient systems” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-composition-projection-mate: the existing statement asserts “Normalized compact-support composition satisfies the projection mate identity”; the new cocycle and arbitrary-base-change equation for the specified product-graph comparisons of one morphism is a different assertion and assumes none of that application-specific data.

lem-pur-etale-graph-comparison-base-change vs def-sf-ambient-underived-clopen-comparison: the existing “Ordinary intrinsic clopen comparison and normalized open compositors” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-proper-open-projection-mate: the existing “Normalized proper/open interchange commutes with projection” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-pur-finite-compact-support-evaluation-refinement: the existing “Finite evaluation normalization of compact-support exchanges and refinements” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs def-sf-semilinear-proper-open-comparisons: the existing “Canonical semilinear proper/open compositors and intrinsic clopen comparison” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-integral-open-product-diagram-normalization: the existing conclusion is “Strict-diagram normalization of integral open product comparisons”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-sf-ambient-underived-clopen-pasting: the existing “Vertical and horizontal pasting of underived clopen comparison maps” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sf-product-compactification-identity: the existing conclusion is “Product compactification identity for the exchange/projection composite”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-sf-package-compactified-tower-comparisons: the existing “Compactified direct-image towers, reduction and composition” has its stated bounded-below domain; the new graph comparison naturality is asserted on every ordinary unbounded input.

lem-pur-etale-graph-comparison-base-change vs lem-trf-filtered-derived-operation-lifts: the existing “Filtered lifts of sheaf-derived operations and their canonical adjunction maps” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-weil-pbc-etale-shriek-compactification-independence: the existing statement asserts “Compactification independence on the qcqs etale site”; the new cocycle and arbitrary-base-change equation for the specified product-graph comparisons of one morphism is a different assertion and assumes none of that application-specific data.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-normalized-proper-open-pasting: the existing “Horizontal pasting for fixed normalized proper/open comparisons” has its stated bounded-below domain; the new graph comparison naturality is asserted on every ordinary unbounded input.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-complete-proetale-composition-pasting-coherence: the existing “Composition Pasting Coherence” has its stated bounded-below domain; the new graph comparison naturality is asserted on every ordinary unbounded input.

lem-pur-etale-graph-comparison-base-change vs lem-sp-ordinary-vertical-pasting-transport: the existing conclusion is “Transport of a vertical square-pasting equation through coherent comparisons”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-amb-etale-adjoint-locality: the existing “Etale localization of the ambient adjoint” has the geometric/coefficient setting written in its statement; the new specified single-morphism graph comparison cocycle and cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-graph-comparison-base-change vs lem-amb-unbounded-proper-open-interchange: it assumes Noetherian schemes throughout; the new assertions retain arbitrary schemes and, for the graph helper, add the missing graph C/Gamma identification.

lem-pur-etale-graph-comparison-base-change vs def-cbc-strict-tower-composition-maps: the existing conclusion is “Canonical strict-tower composition comparison maps”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-normalized-proper-open-geometric-normalization: the existing result assumes D+ and supplied normalized maps; the new statement is unbounded and constructs its Gamma.

lem-pur-etale-graph-comparison-base-change vs lem-sp-tower-geometric-composition: the existing conclusion is “Geometric composition and exact etale sum-extension”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs def-cbc-finite-constant-coefficient-transport: the existing “Normalized finite scalar and etale-origin transport to constant coefficient modules” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sp-proper-open-tower-refinement: its conclusion compares proper refinements of compatible quasi-compact towers in an assumed calculus; it neither constructs nor identifies arbitrary proper/open/proper product-graph comparisons.

lem-pur-etale-graph-comparison-base-change vs lem-pur-compact-support-integral-coefficient-comparison: the existing “Integral compact support under finite free coefficient extension” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-sp-varying-ring-proper-open-pasting: the existing “Clopen proper/open projections and pasting over a varying ring system” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-complete-proetale-refinement-exchange-coherence: the existing “Refinement Exchange Coherence” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-amb-unbounded-proper-open-pasting: the existing pasting theorem assumes Noetherian schemes and supplied normalized maps; the new actual interchange/cube is over arbitrary schemes.

lem-pur-etale-graph-comparison-base-change vs lem-pur-compact-support-site-coherence: the existing “Compact-support site comparison respects compactification calculus” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-pur-compact-support-strict-scalar-refinement: the existing “Scalar mate compatibility with strict compactification refinements” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-amb-unbounded-proper-open-horizontal-composition: the existing “Horizontal composition of unbounded proper/open interchange” has the geometric/coefficient setting written in its statement; the new specified single-morphism graph comparison cocycle and cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-etale-local-compact-support-extension: the existing “Zariski-local extension of etale compact-support functors and exchange morphisms” has its stated bounded-below domain; the new graph comparison naturality is asserted on every ordinary unbounded input.

lem-pur-etale-graph-comparison-base-change vs lem-sp-compactification-refinement-coherence: it assumes an abstract proper/open calculus and quasi-compact compatible-tower geometry; it has no identification of the concrete arbitrary-open graph comparisons with Gamma.

lem-pur-etale-graph-comparison-base-change vs lem-pur-reconstructed-pair-refinement-coherence: the existing “Refinement coherence of reconstructed exceptional representing pairs” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-pur-system-compactification-pf-substitution: the existing “Refinement comparisons intertwine strict-system projection maps” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-amb-compact-support-staircase-expansion: the existing “Expansion of binary compact-support tower comparisons on a fixed staircase” has the geometric/coefficient setting written in its statement; the new specified single-morphism graph comparison cocycle and cube is the unrestricted arbitrary-base ordinary-etale assertion, not that specialized conclusion.

lem-pur-etale-graph-comparison-base-change vs lem-amb-unbounded-proper-open-composition: the existing pasting theorem assumes Noetherian schemes and a supplied normalized Gamma; the new actual interchange/cube is over arbitrary schemes.

lem-pur-etale-graph-comparison-base-change vs lem-pur-coprojection-composition-mate: the existing “Co-projection composition is the mate of projection associativity” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-tower-composition-refinement: it compares D+ compatible towers connected by proper refinement maps; the new graph/interchange assertion is unbounded, uses proper/open/proper presentations and requires no map between its two diagrams.

lem-pur-etale-graph-comparison-base-change vs def-cbc-strict-tower-ordinary-proper-open-arrows: the existing “Unit-normalized ordinary proper and open arrows on strict towers” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs def-cbc-strict-tower-open-extension: the existing conclusion is “Normalized exact open extension on strict constant-coefficient towers”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-strict-tower-proper-open-calculus: the existing “Normalized proper/open calculus on strict pro-etale towers” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-asd-compact-support-graph-coherence: the existing result concerns an etale-map sum/compact-support graph comparison over locally Noetherian quasi-compact bases; the new graph comparison concerns arbitrary compactifiable maps and their proper/open/proper presentations.

lem-pur-etale-graph-comparison-base-change vs def-cbc-strict-constant-tower-operations: the existing “Strict constant-coefficient towers and normalized inverse/direct-image operations” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs def-cbc-strict-tower-proper-open-arrows: the existing “Unit-normalized proper and open arrows on strict towers” concerns its stated pro-etale/adic or system operations; the new single-map product-graph comparison is on ordinary small-etale constant finite-ring D with arbitrary scheme bases and opens.

lem-pur-etale-graph-comparison-base-change vs lem-amb-derived-compact-support-composition-coherence: the existing conclusion is “Structural coherence of three derived images and open extensions”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-pur-refinement-inverse-mate-comparisons: it supplies single-map cocycles from assumed refinement maps and explicitly assumes no non-refinement proper/open comparison; the new graph/interchange square relates the actual graph C to Gamma.

lem-pur-etale-graph-comparison-base-change vs def-sp-proper-open-calculus: it defines assumed proper/open data for quasi-compact opens, without proving that the concrete arbitrary-open product-graph C has those normalizations.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-proper-open-interchange-coherence: its Gamma, pasting and cube are only on D+; the new assertion is on all ordinary unbounded inputs and additionally identifies the specified graph C where relevant.

lem-pur-etale-graph-comparison-base-change vs lem-sp-ordinary-horizontal-pasting-transport: the existing conclusion is “Transport of a horizontal square-pasting equation through coherent comparisons”; it does not assert the product-graph comparison cocycle, its arbitrary-base-change equality and its normalization to rightDerivedLowerShriekOfCompactificationIso.

lem-pur-etale-graph-comparison-base-change vs lem-cbc-proper-open-alpha-pasting: the existing alpha equations are on pro-etale strict towers with quasi-compact opens; the new Gamma equations are on ordinary etale D with arbitrary opens.

lem-pur-etale-graph-comparison-interchange vs lem-sf-native-weil-compatible-tower-calculation: the existing “Native Weil calculation on a compatible proper/open tower” is a different assertion: its stated domain is the native equivariant Weil categories; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-unbounded-compact-support-proper-composition: it assumes the first map proper and all schemes separated finite type over a field; it asserts a proper-composition isomorphism, not the arbitrary-presentation graph/interchange equation.

lem-pur-etale-graph-comparison-interchange vs lem-sf-native-weil-compactification-model-comparison: the existing “Native Weil compactification models under proper refinement” is a different assertion: its stated domain is the native equivariant Weil categories; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-completed-shriek-composition-laws: the existing “Completed shriek composition laws” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-compactified-strict-compositor: the existing “Finite normalization and completed realization of the strict compact-support compositor” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-native-weil-shriek-composition: the existing “Composition of native compactly supported Weil direct images” is a different assertion: its stated domain is the native equivariant Weil categories; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-isomorphism-finite-exchange-coherence: the existing “Finite semilinear exchange: pasting and quotient-coefficient naturality” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-coef-dualizing-construction: the existing “Bounded etale dualizing objects and their coefficient counit mates” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-projection-compatible-triangle-assembly: the existing “Compatible triangles realize the canonical compact-support projection compositor” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-kunneth-second-open-substitution: the existing “Second-open substitution and its proper/open projection square” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-composition-projection-mate: the existing “Normalized compact-support composition satisfies the projection mate identity” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-compact-coefficient-composition: the existing “Finite coefficient comparison respects compact-support composition” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-product-compactification-identity: the existing “Product compactification identity for the exchange/projection composite” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-coef-dualizing-open-adjoint: the existing “Open structural adjunction with normalized composite counit” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-package-compactified-tower-comparisons: the existing “Compactified direct-image towers, reduction and composition” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-sf-etale-support-compositor: the existing “Canonical unbounded etale compact-support compositor” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-zl-compact-support-leray-filtration: the existing “Finite compact-support Leray filtration in constructible Weil sheaves” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-zl-field-shriek-composition-qcqs: the existing “Compact-support composition at field coefficients over qcqs finite-type schemes” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-section-exceptional-fibre-coherence: the existing “Coherence of exceptional fibre comparisons for section families” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-nearby-compact-tensor-coherence: the existing “Tensor and compact-support coherence before duality” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-proper-compact-unit-reduction: the existing “Finite reduction of the proper compact-cohomology unit” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-proetale-composition-tower-normalization: the existing “Pro-etale composition on a compatible tower has the open-adjoint normalization” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-compact-support-exchange-counit: the existing “Compact-support exchange intertwines proper ordinary counits” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-compact-composition-proper-square-normalization: the existing “Compact-support composition along a proper square: closed and open normalizations” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-finite-horizontal-shriek-mate: the existing “Compact-support exchange as a mate along finite horizontal arrows” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-filtered-derived-operation-lifts: the existing “Filtered lifts of sheaf-derived operations and their canonical adjunction maps” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-proper-specialization-borel-moore-compatibility: the existing “Borel–Moore specialization commutes with proper pushforward of lifts” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-etale-left-comparison-base-change: the existing “Etale compact-support composition comparison commutes with base change” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-proper-unit-localization-composition: the existing “Proper-endomorphism units commute with open and closed compact-support composition” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-compact-composition-tower-formula: the existing “Computing finite pro-etale compact-support composition on a compatible tower” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-finite-structural-maps-commshift: the existing “Canonical finite-coefficient structural maps commute with shifts” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-trf-proper-composition-site-transport: the existing “Site comparison preserves compact-support composition with a proper factor” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sfb-proper-open-tower-single-unit-formula: the existing “Single derived-unit formula in a proper/open tower” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-etale-chart-adjoint-comparison: the existing “Natural Hom comparison on an ordinary étale factored chart” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sfb-proper-open-tower-successive-unit-formula: the existing “Successive derived-unit formula in a proper/open tower” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sf-etale-chart-left-compositor: the existing “Specified compact-support source comparison for an equal factored chart” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sfb-proper-open-tower-derived-unit: the existing “Derived-unit resolution calculation in a proper/open tower” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sfb-quasifinite-compact-support-exact: the existing “Quasi-finite compact support is exact and agrees with compactifications” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sfb-exact-compactification-unit-composition: the existing “Composition of normalized exact compact-support units” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs sk-lem-geo-affine-local: the existing “Affine space and étale localization” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-per-prepurity-lci-classes: the existing “Fundamental classes before absolute purity for regular schemes over a trait” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-per-finite-exceptional-internal-hom: the existing “Internal Hom adjunction for finite etale direct image” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-per-field-exceptional-tensor: the existing “Exceptional tensor comparison for coefficients pulled from a field” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-weil-pbc-etale-shriek-qcqs-composition: the existing “Composition of qcqs etale compact-support candidates” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-weil-pbc-etale-compact-support-open-closed-triangle: the existing “Open-closed localization for relative etale compact support” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-weil-pbc-etale-lisse-open-relative-line-constructibility: the existing “Lisse coefficients on an open relative affine line over an integer model” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-weil-pbc-compatible-compactification-triangle: the existing “Compatible geometric compactifications of a composable pair” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-weil-pbc-finite-etale-shriek-transfer-retract: the existing “Derived compact-support retraction from a prime-to-primary finite etale cover” is a different assertion: its asserted domain has boundedness or constructibility restrictions; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-weil-pbc-etale-shriek-relative-mayer-vietoris: the existing “Relative Mayer Vietoris for qcqs etale compact support” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs thm-sf-comp-composition: the existing “The composition law for $Rf_!$” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-chart-left-scalar-normalization: the existing “Scalar normalization of the chart left comparison” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-cbc-complete-proetale-composition-pasting-coherence: the existing “Composition Pasting Coherence” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-chart-normalized-model-identification: the existing “Graph-normalized chart models and independent compactifications” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-compact-scalar-coherence: the existing “Ordinary etale compact-support scalar compatibility with projection and composition” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-pur-finite-compact-site-constructions: the existing “Computed finite-ring compact-support refinement, tower, composition and identity maps” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-cbc-strict-tower-composition-maps: the existing “Canonical strict-tower composition comparison maps” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-et-proet-coefficient-compatibility: the existing “Finite coefficient compact-support comparison respects site transport, refinement and composition” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-horizontal-double-counit: the existing “Double-counit identification in an etale-horizontal square” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-exceptional-base-change-pasting: the existing “Canonical dualizing base-change mate under composition” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-pur-finite-site-tower-etale-coordinates: the existing “Bounded-below etale coordinates for the finite-site tower” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-pur-compatible-triangle-compactifications: the existing “Compactifications supplied by a compatible proper/open triangle” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-tower-geometric-composition: the existing “Geometric composition and exact etale sum-extension” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-pur-etale-horizontal-support-comparisons: the existing “Canonical etale compact-support, horizontal composition and base-change comparisons” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-compact-support-open-source-composition: the existing “Compact-support composition with a source open” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-proper-open-tower-refinement: its conclusion compares proper refinements of compatible quasi-compact towers in an assumed calculus; it neither constructs nor identifies arbitrary proper/open/proper product-graph comparisons.

lem-pur-etale-graph-comparison-interchange vs lem-amb-etale-compact-comparisons: the existing “The etale compact-support comparisons” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-finite-etale-dualizing-normalization: the existing “Finite-coefficient etale exceptional normalization and its dualizing comparisons” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-site-coherence-descent: the existing “Descent and associativity of witnessed comparison pastes” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-sp-coefficient-tower-shriek-interfaces: the existing “Section-normalized coefficient tower calculus interfaces” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-horizontal-support-mate: the existing “Etale horizontal compact-support exchange is the composition mate” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-shriek-open-tower-counit: the existing “Open compact-support composition on the pullback tower” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-section-etale-restriction-coherence: the existing “Counit-normalized restriction on smooth section invariants and deformation endpoints” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-coefficient-tower-shriek-calculus: the existing “Compact-support calculus on varying coefficient towers” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-sum-right-adjoint-coherence: the existing “Coherence of normalized etale sum right adjoints” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-system-refinement-constructible-domain: the existing “Constructible domain and finite normalization of system refinement inverses” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-chart-diagonal-source-mate: the existing “Counit-normalized source comparison for coordinate diagonals” is a different assertion: its statement fixes a field/coefficient geometric setting; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs det-sp-composition-comparisons: the existing “Composition of adjunctions and of coefficient comparisons” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-system-compositor-refinement-square: the existing “Refinement square for compatible semilinear compact-support compositors” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-finite-compact-site-coherence: the existing “Finite-ring compact-support site comparisons respect refinements and towers” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-closed-section-compact-origin: the existing “Identity-normalized compact origin for a map out of a closed section” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-weil-integral-rational-qbar-compact-support: the existing “Integral, rational, and algebraically closed compact-support functors” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-unbounded-compact-support-comparisons: it assumes Noetherian schemes and separated finite-type maps; the new graph/interchange assertion is for arbitrary schemes, arbitrary supplied opens and proper/open/proper presentations.

lem-pur-etale-graph-comparison-interchange vs fix-lem-exchanges: the existing “Exchange functoriality: naturality, identities, and pasting” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-finite-site-tower-paste: the existing “Finite-site comparison of the proper/open compatible-tower word” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-shriek-tensor-composition: the existing “Tensor projection maps respect compact-support composition” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs cor-amb-affine-space-adjunction: the existing “Affine-space ambient adjunction” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-compactification-refinement-coherence: it assumes an abstract proper/open calculus and quasi-compact compatible-tower geometry; it has no identification of the concrete arbitrary-open graph comparisons with Gamma.

lem-pur-etale-graph-comparison-interchange vs lem-pur-reconstructed-pair-refinement-coherence: the existing “Refinement coherence of reconstructed exceptional representing pairs” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-system-compactification-pf-substitution: the existing “Refinement comparisons intertwine strict-system projection maps” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-system-compatible-compositor-normalization: the existing “Compatible-triangle word for the geometric semilinear compositor” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-composition-tensor-mate: the existing “Composite exceptional adjunction and tensor-map mate identity” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-finite-adjoint-mate-compatibility: the existing “Finite reduction preserves the canonical adjoint mates” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-compactification-projection-composition: the existing “Projection maps respect the explicit proper/open compactification tower” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-coprojection-composition-mate: the existing “Co-projection composition is the mate of projection associativity” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-system-level-projection-formula-coherence: the existing “Strict-system projection formula composition coherence” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-closed-chart-exceptional-preservation: the existing “Exceptional inverse image on a closed affine-space chart” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-horizontal-support-tower: the existing “Etale compact-support composition on a pullback compactification tower” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-normalized-mates-composition-pasting: the existing “Composition and refinement-pasting of actual etale normalized mates” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-shriek-open-exchange-adjoint: the existing “Open compact-support exchange is the extension-composition mate” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-amb-open-projection-composition: the existing “Composition of the canonical derived open tensor isomorphisms” is a different assertion: its assertion concerns the specific data and conclusion named in its title; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-cbc-compactifiable-compatible-tower: the existing “Compatible compactification towers with a supplied compactification of the composite” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs thm-amb-vector-bundle-purity: the existing “Vector-bundle purity before smooth orientation” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-pur-proetale-module-scalar-restriction: the existing “Restriction of intrinsic pro-etale modules to constant scalars” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-etale-chart-compact-support-normalization: the existing “Unbounded compact-support normalization on a closed affine chart” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-integration-transpose-composition: the existing “Composition and dualizing tensor calculus for integration transposes” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-pur-refinement-inverse-mate-comparisons: it supplies single-map cocycles from assumed refinement maps and explicitly assumes no non-refinement proper/open comparison; the new graph/interchange square relates the actual graph C to Gamma.

lem-pur-etale-graph-comparison-interchange vs lem-pur-product-exchange-counit-coordinates: the existing “Product compactification geometry, exchange factorization and open counit square” is a different assertion: its statement imposes Noetherian geometric hypotheses; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs lem-sp-open-scalar-inverse-transpose-factorization: the existing “Inverse-transpose factorization for open source composition” is a different assertion: its stated objects are pro-etale/adic or semilinear systems; it does not assert the actual product-graph C/Gamma normalization for two proper/open/proper presentation diagrams.

lem-pur-etale-graph-comparison-interchange vs def-sp-proper-open-calculus: it defines assumed proper/open data for quasi-compact opens, without proving that the concrete arbitrary-open product-graph C has those normalizations.

The new graph/interchange node also differs from the two retained new helpers: the graph-base-change node treats presentations of one fixed map but has no Gamma compatibility, and the Gamma cube node treats Gamma maps but has no graph C. The repair explicitly supplies their missing interaction.

## Validation

The required initial dry run of the retained split completed successfully at ef7f1de8966, before mathematical edits. Server checks for the repaired files and the final dry run/delivery are recorded below as they complete. No local check_dag.py, review_split.py or preflight_delivery.py is run.

The repaired dry run completed with exit 0: OK (not pushed), commit a5ce605e913, server preflight passed. This run included the repaired four node files, exact citations, search-log validation, duplicate comparisons and the signed review above.
