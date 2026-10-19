# thm-sf-kunneth-relative — Q20 stage-1 split

## Files written

- dag/nodes/sec-six-functors/thm-sf-kunneth-relative.json — split into the typing check, four canonical arrows, compatibility diagrams, restriction calculation, and point-fibre passage.
- dag/nodes/sec-six-functors/lem-sf-point-fibre-derived-tensor.json — new statement, unsplit; no exact Mathlib match. This concerns the specified finite, completed integral, rational, and common-stage point coefficient functors.
- dag/units/sk-thm-sf-kunneth-relative.json — only `realized` and `realized_by`; the existing coherence node still carries the extra symmetry and triple-product clauses of the unit.
- citations.json — every step/node pair has a quote copied from that node's actual statement. Longer quotes preserve hypotheses as well as conclusions.

## Attachments

None. `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`, WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Relative.lean:131–142, ends in `sorry`. Its statement only gives `Nonempty` of an isomorphism for a generic torsion coefficient category, not the naturality and compatibility assertions and the completed coefficient conventions of this node. The closed-immersion corollaries in that file depend on it. Neither is evidence that this node is finished. The new point-fibre result also has no exact existing declaration: the pro-etale GlobalSectionsMonoidal file gives lax monoidality, and the etale StalkMonoidal file gives underived stalk tensor comparisons; neither states the derived, completed all-coefficient assertion.

## WANTED

None. The shared tree has only literature lists, but the local read-only literature mirror at `/home/ubuntu/work-bp/sheaf/literature/` contains the exact master blueprint node, unit, coherence node, and Stacks `sites-cohomology.tex`, which I read there. The node sources retain their canonical `literature/` paths.

## Statement and source corrections

STATEMENT-DISPUTED: the unqualified compatibility with a morphism `B' → B` is outside the domains of the given datum if B' is arbitrary. For example, take B = Spec k and B' = Spec k(t_1,t_2,...) with infinitely many independent variables. This is a scheme mapping to B but is not a finite-type k-scheme, whereas the six-functor datum and the unit's constructible coefficient categories are indexed by separated finite-type k-schemes. The corrected compatibility quantifies over B' separated of finite type over k. This makes the diagrams well typed without changing the principal product theorem, any coefficient, or any input complex. It is the compatibility inside the source's stated six-functor setting. No extension of that setting to arbitrary bases is claimed.

The first dry run required a self-contained datum and the missing proper-coincidence route. The statement now explicitly introduces p,a,q,k_0,k,ell,E,n,Lambda and the six-functor datum; no mathematical hypothesis beyond the already assumed datum is added. Step 6 now cites cor-cbc-proper-coincidence exactly for its finite-level identification of the exchange under proper coincidence, using A5 for the supplied higher-stage passages.

The imported statement had a dangling reference `lem-pur-kunneth-supported`, which is absent from the DAG. It was a bibliographic aside about a separate supports theorem, not an input to this proof. Replaced it by prose and removed it from statement dependencies. The compact-support display and the distinction from cohomology with support are retained.

The imported paragraph swapped the factors before the first projection formula without recording the symmetry. I instead follow the unit's displayed composite exactly: the first projection is at (p*K,L), with no swap; the symmetry occurs after exchange and then after the second inverse projection. The original paragraph also omitted the finite-Tor typing, all compatibility arguments, the monoidal restriction calculation, and the point-fibre tensor comparison.

## New nodes

`lem-sf-point-fibre-derived-tensor` is a genuine extra input to turn an identity in the point sheaf category into the asserted tensor identity of coefficient complexes. A categorical equivalence alone does not assert its monoidality. It is not the relative product theorem or one of its clauses: it mentions no f, g, compact-support image, or exterior product. Its finite-level ingredient is Stacks Tag 07A4, label `lemma-pullback-tensor-product`; I read the statement and K-flat proof at lines 3683–3724 in the local literature mirror. The completed and scalar-localized point functors are the ones explicitly defined by `def-weil-finite-coefficient-point` and `def-weil-derived-pullback-tensor-hom`. Future splitting must identify the finite point fibre comparison and pass it through those completed/rational/common-stage constructions. It is not merely the underived Mathlib sheaf fibre monoidal instance.

For small-case checks, zero objects give zero on both sides, the two units give Lambda, and shifts of units give the same shift and Koszul symmetry on both sides. At finite nonfield coefficients inputs are required finite-Tor: no boundedness of a derived tensor of arbitrary bounded finite modules is assumed. At the integral level completed tensor is used in the source, while the target is the derived tensor of bounded finitely generated integral modules; at field and algebraically closed coefficients the assertion uses a common coefficient field. No identification of arbitrary pro-etale sheaves with constant modules is asserted.

Mathlib searches were run exclusively through msearch.py and copied from searches.jsonl, including the unavailable LeanSearch result and the rejected initial Loogle syntax. A second semantic phrasing and a valid Loogle query were tried. The item searches found unrelated group-homology/Tor and underived pushforward identities. For the new node Loogle did find Mathlib CategoryTheory.Sites.Point.Monoidal.lean; I read it, including the strong monoidal instance for sheafFiber. This is an underived site fibre functor, not the four-stage derived point functor here. The source grep restricted to a single file displayed line prefixes oddly; its actual hits and the later directory grep are recorded as returned. No Mathlib leaf is claimed.

## Not duplicates

lem-sf-point-fibre-derived-tensor vs lem-weil-pbc-ringed-projection-mate-exact: that node supplies exactness data for a projection mate under ordinary ringed-topos pullback; it does not identify the completed integral point fibre or its rational/common-stage tensor comparison.

lem-sf-point-fibre-derived-tensor vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: this general result supplies the ordinary finite-level derived pullback tensor comparison. It does not identify Fib_s with that pullback or prove its compatibility with the completed integral tensor and the rational/common-stage coefficient functors. That extra identification/passage is the new assertion, so the all-stage assertion is not a one-line specialization.

lem-sf-point-fibre-derived-tensor vs lem-weil-pbc-ringed-exchange-tensor-coherence: that node compares projection and exchange composites around a square of ringed topoi; the new node concerns the point functor and its coefficient stages and has no exchange square.

lem-sf-point-fibre-derived-tensor vs lem-weil-pbc-ringed-projection-restriction: that node concerns localization and projection maps for ordinary module sheaves; it does not state a tensor comparison for the completed point coefficient functors.

lem-sf-point-fibre-derived-tensor vs def-weil-pbc-ringed-tensor-square-presentation: that node defines representative presentations of tensor squares; it is not a theorem identifying Fib_s with a monoidal derived point functor.

lem-sf-point-fibre-derived-tensor vs lem-kun-inverse-image-monoidal: that node concerns ordinary etale inverse image along a morphism of schemes. The new node concerns evaluation/fibre to coefficient modules from the point pro-etale categories and includes completed integral and scalar-localized coefficients.

lem-sf-point-fibre-derived-tensor vs def-kun-constant-projection-morphism: that node defines the constant-coefficient projection morphism for the ordinary etale category. It does not assert the point-fibre tensor isomorphism for the completed integral and field coefficient functors.

lem-sf-point-fibre-derived-tensor vs lem-pur-derived-pullback-tensor-iso: that node concerns pullback along scheme morphisms with the same four coefficient stages; the new node concerns Fib_s into derived coefficient modules. In particular global sections at the pro-etale final object are not identified with a scheme pullback by that statement. I cite the existing node directly for restriction of exterior products rather than making another exterior-product lemma.

lem-sf-point-fibre-derived-tensor vs lem-pur-support-site-comparison: both cite Stacks 07A4, but the existing node only compares etale/pro-etale supported sections for finite ordinary ring coefficients, whereas the new node asserts monoidality of the derived point-fibre coefficient functor at finite, completed integral, rational, and algebraically closed stages.

## Review by Q20

I read the master theorem and the whole relative-product unit in the local literature mirror and compared them with the imported node. The proof keeps the unit's four-arrow route. I also read the separate coherence lemma to avoid citing it back into the present theorem: its statement depends on this theorem. The unit realization therefore lists it alongside the present node, without making it a dependency.

Step 1 uses the actual axioms of def-sf-datum, not unproved properties inferred from a definition of an operation. I checked the explicit A2–A5 clauses, the finite-stage pullback and shriek clauses (i),(iv) of thm-sf-ctf-stability, and the actual Mathlib-leaf statements lem-pod-separated-finite-type-base-change, lem-weil-pbc-closed-immersion-base-change and lem-weil-pbc-closed-immersion-comp. The composition calculation is written out using finite affine covers/algebra generators and the diagonal factorization. I removed the initial draft's citation of the definition-only scheme-property index for these permanence facts. Only these stability clauses are needed, not the internal-Hom/duality clauses. The higher-stage inputs are the operations on the stated categories supplied in this axiomatized theorem, with its stipulated coefficient constructions. This delivery does not establish existence of a concrete six-functor datum by fiat.

Step 2 quotes A4 for all coefficient stages and cites thm-sf-comp-composition only on its actual finite witnessed pro-etale domain; I read its current statement and did not silently treat it as an unrestricted all-coefficient composition theorem. Step 3 uses the displayed type of def-sf-pf and the actual all-stage isomorphism statement of fix-prop-projection-formula. I checked which factor is on T and which on Y. Step 4 uses A2 with f'=q and g'=p; hence it is the inverse of g* Rf_! → Rq_! p*, not an exchange for Rf_* or the wrong Cartesian square. Step 5 uses the second projection formula with first input L and second input Rf_!K, whose finite-Tor typing was checked first. This recovers exactly the canonical composite, including both symmetries.

Step 6 also uses the actual statement of cor-cbc-proper-coincidence: its compact-support exchange is the proper-base-change exchange under the canonical !/* identification. It uses the actual naturality, coefficient-change, compactification and proper-identification clauses in the two projection-formula statements, together with A5. Inversion preserves commuting comparison squares by multiplying the commutative square by the inverses, so no new compatibility lemma is hidden there. Step 7 is not an appeal to a generic claim of coherence: it specifies the two projection-formula base-change squares (q along v, g along b), the composition/exchange pasting equations in fix-lem-exchanges, and the monoidal pullback comparison in lem-pur-derived-pullback-tensor-iso. I read those statements, including the full completed and transported coefficient typing in fix-lem-exchanges. All schemes in this corrected compatibility claim are separated finite-type k-schemes. Compose the successive squares to obtain the base-change square for the canonical map, so no circular use of the later relative-product coherence is necessary.

Step 8 cites lem-weil-pbc-closed-immersion-proper for the actual properness theorem, then uses the explicit composition argument of step 1 to check the closed immersions yield separated finite-type structure morphisms and pulls back the input complexes. I read the derived pullback/tensor statement and used its actual composition compatibility; writing p r = i_Z p' and q r = i_W q' makes the restriction identification explicit. Step 9 uses the coefficient-complex definition of ordinary compact cohomology, not the support-cohomology functor. It explicitly cites the new point-fibre tensor statement for the passage through Fib_s. The separate support definition is quoted only for the kernel-of-restriction meaning, not as a theorem comparing ordinary and extraordinary restrictions.

I checked B1–B10: the one new node is statement-only, self-contained, has real searches, source tag/label, definition dependencies, and blueprint ancestry, and no false attachment or Mathlib leaf. I checked C1–C8 by opening each cited statement; citations.json includes every use and verbatim text. D1–D5 are addressed by retaining the proof's four arrows, avoiding any new relative Kunneth restatement, and exposing the point-fibre input. E1–E7 led to the base-change domain correction above, and the fibre/compact-support distinctions. Identity maps and zero inputs reduce the principal formula to the identity/zero formula; proper maps use the specified !/* identification; no supported formula over a relative base is deduced.

## Unfinished work

Only the new point-fibre tensor lemma is unsplit, as required by the one-level split rule. No Lean was written or compiled. The sandbox is for a fresh second reader; nothing is pushed by this worker.

## Second reading by Q20

- Source and item statement: reread the blueprint node and its full relative-product section; the finite-field, coefficient, separated finite-type, finite-Tor, compatibility, proper, and closed-subscheme clauses agree. I corrected the projection notation to `\\pi_X,\\pi_Y` so it cannot be confused with the characteristic prime `p` and `q=p^a`.
- Step 1: checked against [def-sf-datum], [thm-sf-ctf-stability], [lem-pod-separated-finite-type-base-change], and the closed-immersion base-change/composition statements; the affine-generator and diagonal arguments supply the stated typing.
- Step 2: checked the (A4) composition arrow and [thm-sf-comp-composition] on their stated witnessed domain; the target and inverse direction are correct after the projection renaming.
- Step 3: checked [def-sf-pf] and [fix-prop-projection-formula] for `\\pi_Y` with inputs `\\pi_X^*K,L`; the first projection introduces no symmetry.
- Step 4: checked (A2) on the displayed Cartesian square; the exchange has source `Lg^*Rf_!K` and target `R\\pi_{Y!}L\\pi_X^*K`, and the inverse plus tensor symmetry gives the written object.
- Step 5: checked the second projection formula for `g` with `(L,Rf_!K)` and the finite-Tor typing supplied in step 1; the final symmetry has the correct order.
- Step 6: checked naturality, finite reduction, scalar extension, proper `!/*` coincidence, and [cor-cbc-proper-coincidence] against the cited statements; each comparison is a composite of their commuting squares.
- Step 7: checked the corrected base-change domain (`B'` separated finite type over `k`) and the `\\pi_Y` projection square against [fix-lem-exchanges], [prop-sf-pf-coherence], and [lem-pur-derived-pullback-tensor-iso]; the pasted square is well typed and does not use the later coherence lemma circularly.
- Step 8: checked closed-immersion properness, composition, pullback monoidality, and the identities `\\pi_X r=i_Z\\pi'_X`, `\\pi_Y r=i_W\\pi'_Y`; the restricted external product is the ordinary pullback restriction.
- Step 9: checked [def-weil-ordinary-compact-cohomology], [lem-sf-point-fibre-derived-tensor], and [def-pur-support-cohomology]; the point-fibre tensor passage yields ordinary compact-support complexes and does not identify them with support cohomology.
- New node `lem-sf-point-fibre-derived-tensor`: reread its self-contained all-stage statement, three definition dependencies, Tag 07A4 source, searches, and zero/unit/shift edge cases; verdict genuine unsplit input, with no exact Mathlib match and no duplicate DAG node.

Changes made: repaired projection naming throughout the item proof and statement, including the compact-support restriction calculation; corrected the residual composition target and added this second-reading audit. No mathematical hypothesis or conclusion was weakened.
