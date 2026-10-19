# Stage-1 delivery: lem-trf-algebraic-shriek-calculus

Group Q99, direct-delivery worker, 2026-10-18. This was a new sandbox split, not a repair of a returned delivery. All project and source checkouts were read-only. No Lean was written, no compiler was run, and no agents were started.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-algebraic-shriek-calculus.json`: item split into thirteen proof steps; statement retained verbatim. Mathlib searches found no exact declaration.
- `dag/nodes/sec-trace-formula/lem-trf-pseudocoherent-rhom-flat-base-change.json`: statement-only node, status unsplit; no Mathlib match. Ordinary-module RHom base change with pseudo-coherent first argument, bounded-below second argument, and flat scalar extension.
- `dag/nodes/sec-trace-formula/lem-trf-perfect-algebra-coinduction-tensor.json`: statement-only node, status unsplit; no Mathlib match. The perfect-algebra evaluation formula in the derived category of modules over the target algebra, for arbitrary unbounded coefficients.
- `citations.json`: one entry for each step/node citation, quoting its statement verbatim. `report.md`: this report. `searches.jsonl`: seventeen actual recorded search-command calls, whose queries and outputs are preserved in the node search fields. Sandbox Python preparation scripts are working files, not DAG deliveries.

## Attachments

None. Searches of `WeilConjectures/` in the read-only slopmaster2 source for the blueprint tag and for the upper-shriek/coinduction concepts found no declaration proving this whole item. The exact upstream master checkout is reference material only. The item has no imported Lean-audit declaration to attach. The ordinary Mathlib `ModuleCat.coextendScalars` and `ModuleCat.restrictCoextendScalarsAdj` are not derived functors and do not state either new lemma.

## WANTED

None. All mathematical sources used are already in `literature/stacks-project/`.

## Corrections and scope

The original item was unsplit; its mathematical statement is unchanged. The proof now distinguishes the actual algebra-valued derived coinduction from the ordinary RHom obtained by scalar restriction. In particular, a forgotten isomorphism of complexes is not treated as an algebra-linear isomorphism. Composition and flat base change retain their stated bounded-below hypotheses, while polynomial-refinement independence, arbitrary-ring coinduction composition, and the open-immersion calculation hold unboundedly. There is no claim that arbitrary polynomial presentations have canonical orientations.

During self-review I replaced an indirect scheme-level argument for polynomial Noetherianity with the existing finite-type-algebra Noetherian lemma, added affine quasi-compactness when checking the globally Noetherian hypothesis of the polynomial-resolution theorem, corrected the base-change source tags to 0E28/0E29/0E2A/0BZM, and separated zero quotients before invoking regular-sequence results whose definition requires a nonzero quotient. These are proof/citation repairs, not statement changes.

## Source error

Stacks `dualizing.tex`, Tag 0BZT, `lemma-composition-shriek-algebraic`, has a type error in the first line of its final displayed calculation: the scalar extension inside the argument of $\chi^!$ is written $\otimes_B^{\mathbf L}Q$, although $Q=P[y]$ is not supplied with a $B$-algebra structure and the argument must be a $Q'=B[y]$-complex. The preceding paragraph correctly writes $Q'$. For example, take the source's $A=\mathbf Z$, $B=\mathbf F_2$, $P=\mathbf Z$, $C=B$, and zero added variables. Then $Q=\mathbf Z$ has no unital $B$-algebra structure, so the printed tensor product over $B$ is not defined. Step 9 uses $Q'$ on that line and $Q$ only on the other side of the base-change comparison. This repairs the source's proof notation and leaves its theorem and the item unchanged.

## Unfinished work

The two new inputs are intentionally unsplit for later workers. No part of the item's proof is deferred to an uncited assertion; the remaining work on those inputs is exactly their self-contained statements. There is no missing source or statement dispute. Final server dry-run and push results are recorded below when available.

## Search and duplicate review

I searched the whole DAG by tags 0A6A, 0BZE, 0A70, 0A71 and by RHom/base-change/coinduction/perfectness keywords, the whole imported blueprint using `tools/blueprint_refs.py search`, and the project Lean source before creating either input. The nearest blueprint ancestor is `lem-trf-local-term-locality`; the precise inherited auxiliary route through relative-duality-polynomial-chart is preserved, and the item is prepended to the two new nodes' `via` chains. Neither statement is itself a blueprint node, so `same_as` is empty. These generic algebra inputs serve that inherited route; they do not replace a zero-stalk unit argument. Generic tools from other units are declared in `split_report.tool_uses`, without editing the maintainer-owned top-level `tool_uses`.

For each of the item and two new inputs I ran LeanFinder with a second phrasing, LeanSearch, Loogle, and source grep through the required `msearch.py` command. All services answered. The first broad RHom grep also matched unrelated BifunctorHomological names; a more precise grep over Algebra returned zero. The semantic hits were flat scalar-extension exactness, Ext/localization functoriality, ordinary finite-projective tensor-Hom equivalences and ordinary restriction/coextension adjunctions. I read the ordinary coextension implementation in `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, lines 520–680: this does not prove the derived formula for an algebra merely perfect as a module. Thus no new node is marked as a Mathlib leaf. Search records quote the command's actual logged results and do not infer absence from a failed service.

## Not duplicates

lem-trf-pseudocoherent-rhom-flat-base-change vs def-pc-perfect-rhom-base-change-map: the existing node defines the comparison using bounded finite-projective representatives; the new theorem proves invertibility for a possibly nonperfect pseudo-coherent source under flatness and a lower bound.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-base-change-rhom-perfect: the existing theorem assumes a perfect first argument and allows arbitrary base change and target; the new theorem allows a nonperfect pseudo-coherent first argument, requires a flat map and a bounded-below target. Neither hypothesis package subsumes the other.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-bounded-ring-hom-extension-degree: the existing result assembles degreewise comparisons with finite support; it does not state derived base change from an unbounded-above-length pseudo-coherent resolution.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-finite-projective-ring-hom-extension: the existing result concerns one finite projective module and ordinary Hom; the new result concerns RHom from a bounded-above, potentially infinite resolution.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-dual-term-flat: the existing conclusion is termwise flatness of an explicit dual, not a scalar-extension isomorphism.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-kflat: the existing conclusion is K-flatness of a finite-projective Hom complex, not pseudo-coherent derived base change.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-scalar-extension: the existing chain-level isomorphism assumes bounded finite-projective source; the new derived theorem covers pseudo-coherent nonperfect sources with bounded-below targets.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-degree-condition: the existing node defines a signed degreewise predicate; it is not the derived base-change theorem.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-degree-isiso: the existing invertibility theorem is degreewise for a bounded finite-projective source; it does not cover the new pseudo-coherent case.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-degree-map: the existing node constructs a degreewise dual-evaluation map, without asserting the new derived base-change isomorphism.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-degrees: the existing theorem gives signed degreewise tensor-dual evaluation for bounded finite-projective complexes, not pseudo-coherent scalar extension.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-differential: the existing conclusion is differential compatibility of normalized evaluation, not base change.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-dual-iso: the existing theorem is a chain isomorphism from a bounded finite-projective dual tensor; the new source may only admit an infinite bounded-above free resolution.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-postcomposition: the existing statement is the postcomposition summand of a differential calculation, not derived base change.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-perfect-ring-hom-tensor-precomposition: the existing statement is the precomposition summand of a differential calculation, not derived base change.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-ring-bounded-projective-extension: the existing conclusions are K-flatness and preservation of projectivity, not the new RHom base-change isomorphism.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-ring-extension-finite-support-product: the existing result preserves a product with finite support, not Hom from a pseudo-coherent complex into a bounded-below derived target.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-ring-extension-internal-hom-ext: the existing result detects equality of two module-sheaf maps on pure tensors; it neither asserts nor proves derived base-change invertibility.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-ring-hom-extension-transport: the existing result transports an already specified ordinary Hom comparison to a one-point site; the new result proves a derived isomorphism for pseudo-coherent complexes.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-pc-ring-projective-internal-hom-exact: the existing result is exactness of ordinary Hom from one projective module; it does not state pseudo-coherent RHom base change.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-sc-finite-pushforward-derived-hom-qcoherent: the existing result proves quasi-coherence and a lower bound on a finite-pushforward algebra RHom over schemes; it does not compare scalar extension of RHom.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-sc-proper-flat-image-global-hom-base-change-isIso: the existing theorem concerns a global sheaf Hom comparison for a proper flat map with perfect input; the new theorem concerns ordinary modules, a nonperfect pseudo-coherent first argument, and arbitrary flat ring maps.

lem-trf-pseudocoherent-rhom-flat-base-change vs prop-pod-biduality-at-the-point: the existing result is perfect biduality/evaluation in the fixed Poincare coefficient category at the point; the new theorem is ordinary-module flat scalar extension for arbitrary commutative rings and potentially nonperfect sources.

lem-trf-pseudocoherent-rhom-flat-base-change vs lem-weil-point-fibre-equivalence: the existing result is a fibre-category equivalence for four fixed coefficient systems, not derived Hom scalar extension over arbitrary commutative rings.

lem-trf-perfect-algebra-coinduction-tensor vs lem-trf-algebraic-shriek-calculus: the new input is the evaluation-normalized tensor formula for an arbitrary perfect algebra and arbitrary coefficients. It asserts none of the item's polynomial-presentation independence, finite-type composition, flat base change, or open-immersion calculations, and is not any one of those clauses. The item actually proves those clauses using it together with resolutions and explicit comparisons.

lem-trf-perfect-algebra-coinduction-tensor vs lem-trf-relative-duality-polynomial-chart: the existing geometric theorem constructs an oriented relative dualizing pair for flat locally finitely presented schemes and compares polynomial charts; the new input only identifies perfect-algebra coinduction with tensor by its dual, with no geometric relative-duality or chart-normalization conclusion.

lem-trf-perfect-algebra-coinduction-tensor vs lem-pc-perfect-ring-hom-tensor-dual-iso: the existing chain isomorphism is in the base ring module category and assumes an actual bounded finite-projective complex. The new theorem supplies the canonical comparison in $D(B)$ for an algebra perfect only after forgetting its action; the $B$-linear lift is an additional issue, and is why the existing ordinary-Hom theorem cannot simply replace it.

## Review by Q99

I read the actual Stacks text for the item: dualizing.tex Tags 0A70/0A71/0C0F (coinduction), 0BZI/0BZJ (polynomial construction and refinement), 0E28/0E29/0E2A/0BZM and 0BZN (base change), 0BZT (composition), and 0C0H (open localization). For the new pseudo-coherent base-change node I read more-algebra.tex Tag 0A6A clause (3), its map 0E1X, and the comparison 0E1W. Its flatness and lower bound are both retained, rather than applying the perfect-input theorem to an arbitrary quotient. For the new perfect-algebra tensor node I read dualizing.tex Tag 0BZE and its surrounding construction and proof; it gives the tensor functor in $D(B)$, not just a forgotten formula in $D(R)$. Evaluation normalization comes from 0A70/0A71. The new nodes contain statements only, with all objects introduced and no implicit Noetherianity, flatness, or finite-projective dimension assumptions. I used no SGA source.

I opened and read the statement of every cited node; the citations file records exactly the portions available to the following steps. Here is the mathematical check, including the hypotheses of each invocation.

1. `lem-weil-pbc-ring-modules-grothendieck-abelian` states precisely the needed Grothendieck property for modules over any ring; `lem-sfb-grothendieck-k-injective` supplies a K-injective resolution for any complex, without a bound. `lem-sc-kinjective-quasi-iso-comparison` supplies the homotopy-to-derived Hom bijection, not a claim about all representatives. `def-pur-derived-internal-hom` identifies the forgotten model. The degreewise Hom-adjunction, K-injectivity after coinduction, and evaluation counit are written explicitly, so no nonexistent general coinduction node is cited.

2. This uses only step 1 and an explicit chain isomorphism with inverse. Both have the correct $C$-action. Evaluating twice gives precisely evaluation at $1\in C$, verifying the requested compatibility rather than invoking a coherence slogan.

3. `lem-weil-pbc-regular-sequence-koszul-regular` accepts the injectivity condition, `lem-weil-pbc-regular-sequence-conormal-free` identifies the one-generator conormal, and `lem-sc-koszul-regular-sequence-dual-complex` gives the sole Ext group and its quotient action. The new perfect-algebra tensor node is applicable because the displayed two-term free resolution makes this quotient perfect. A unit $s$ or zero ring is handled before the regular-sequence argument; otherwise the required nonzero quotient is present. Concentration in one degree gives an isomorphism in the algebra-module category by truncation, not by fullness of a derived restriction functor.

4. `lem-pur-derived-change-of-rings` supplies the everywhere-defined extension functor; `lem-pc-derived-tensor-second-factor-functor` permits tensoring with the quotient complex and preserves the algebra action. The needed associativity is the displayed termwise identity on a K-flat representative. Monicity proves injectivity of $y-g$ over any coefficient ring. Adding one variable, then induction and the common presentation, proves independence up to an isomorphism without asserting canonical orientation.

5. Zero-variable presentations give the surjection and identity clauses directly from steps 1–2. No additional theorem is used.

6. `lem-weil-pbc-finite-type-algebra-noetherian` includes zero-kernel presentations, hence all the polynomial rings used here. `lem-weil-pbc-finite-free-resolution-noetherian` applies because a quotient is cyclic over that Noetherian polynomial ring. `def-pc-ring-pseudo-coherent-complex` then identifies the resulting bounded-above finite-free resolution with pseudo-coherence. `def-weil-pbc-flat-ring-map` is used only through its injection criterion: the monomial-basis and tensor-rebracketing arguments verifying flatness are actually written, rather than attributed to that definition.

7. The only new non-elementary input is `lem-trf-pseudocoherent-rhom-flat-base-change`. Step 6 proves pseudo-coherence of $A/P$, the map $P\to P'$ is assumed flat, and $M$ is explicitly bounded below. The map is constructed using the adjunction/counit already proved, and the source-restriction tensor identity is written out. The underlying comparison is the canonical map in the cited statement, so its invertibility and reflection by scalar restriction prove the $A'$-linear comparison; I do not infer fullness of restriction.

8. This is step 7 with $P'=R'[x]$. Flatness follows from the original flat ring map by the stated tensor identity, and polynomial freeness preserves the lower bound. The two coefficient complexes are literally the displayed successive exact extensions; the number of variables, hence the shift, is unchanged.

9. This is step 7 for the polynomial flat extension and step 2 for composable coinductions. The source and target rings are listed explicitly, and $Q'=B[y]$ is used as the $B$-algebra. The lower-bound hypothesis is checked before invoking step 7. There are $n+m$ variables in the composite presentation and exactly that combined shift. No new node merely restates the composition clause.

10. `def-weil-open-immersion` supplies stalk isomorphisms; `def-weil-flat-morphism` and `lem-weil-pbc-flat-morphism-affine-criterion` therefore give ring flatness. `lem-pc-flat-resolution-tor-comparison` applies to the length-zero flat resolution, verifying stalkwise Tor dimension zero. `pqf-def-locnoeth` and `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` verify that the affine target is globally Noetherian, as required by `lem-pc-affine-polynomial-resolution-of-stalkwise`; local finite type is the standing finite-type assumption. That theorem gives finite projective dimension, not finite ranks. To obtain actual perfectness I use the finite-free resolution from step 6 and `lem-weil-pbc-projective-resolution-kernel-projective`; its bound is the finite projective dimension just obtained. The terminal syzygy is finitely generated over the Noetherian polynomial ring. Thus the resulting bounded finite-projective complex meets `def-pc-perfect-ring-complex`. Dimension zero is separated, and the empty open was handled first.

11. The monomorphism assertion is proved directly from the open-subscheme definition. `lem-weil-pbc-fibre-product-affine-spectra` then identifies the tensor multiplication and both coprojections. The polynomial graph quotient is computed explicitly: after each variable is evaluated the next difference is monic, so the regular/Koszul hypotheses of the three cited sequence lemmas hold (with $A\ne0$ after step 10). Their dual statement supplies the unique top cohomology and its action. The empty sequence $n=0$ gives the same conclusion with no shift.

12. `lem-pc-base-change-rhom-perfect` really states a base-change isomorphism for arbitrary scalar extension and arbitrary target with perfect first argument; step 10 supplies perfectness. I apply it to ordinary RHom over $P$, as its statement requires, and use flatness to identify $A\otimes_R A=A$. The proof then checks the coefficient $A$-action on cohomology using the two coprojections, and obtains the isomorphism in $D(A)$ by truncation. It never treats an arbitrary underlying derived isomorphism as automatically $A$-linear.

13. `lem-trf-perfect-algebra-coinduction-tensor` is now applicable for $P\twoheadrightarrow A$ by step 10, with no bound on $K$. `lem-pc-derived-tensor-second-factor-functor` supplies tensoring in the actual $A$-module category and its compatibility with the last quasi-isomorphism. The middle rebracketing and K-flatness check are written termwise. This finishes the unbounded open clause, without incorrectly extending the bounded-below pseudo-coherent base-change theorem.

For the B–E checklist: the two new nodes are self-contained statement-only inputs with definitions or inline meanings for all specialized notions, single-escaped TeX, verified Stacks labels/tags, actual logged searches, and filled blueprint ancestry. They do not reproduce the item or one of its clauses. The proof dependency list is the union of step uses, and each cited node's statement (not its proof) supplies the quoted input. No comparison is silently promoted to a stronger coefficient category or made canonical beyond what was proved. I checked source/target rings, scalar actions, shifts, finite-generation assumptions, boundedness and flatness in the steps above. The longest proof step is below 2000 characters, and no long step conceals an extra black-box comparison.

Small-case tests were mathematical, with no compiler: the identity ring map, a quotient with zero variables, a field and its identity algebra, the zero algebra and empty open, a unit nonzerodivisor, zero polynomial variables, and adjoining one graph variable. For the first new node, $E=R$ reduces to identity base change; a nonperfect cyclic module over a Noetherian ring is still allowed, while arbitrary unbounded targets are deliberately not asserted. For the second, $B=R$ gives identity coinduction and $B=0$ gives zero; $B=R/(s)$ for a nonunit nonzerodivisor gives the checked shift $B[-1]$. Finite free and finite product algebras also give the ordinary tensor-dual formula with the specified action. None of these checks suggests an extra hypothesis or weakened conclusion.

## Server validation

The required direct-delivery dry run exited successfully: `OK (not pushed)` at `fc77b1f1b1`; server preflight passed. The final delivery invocation follows after a repeat dry run for the report typography correction.
