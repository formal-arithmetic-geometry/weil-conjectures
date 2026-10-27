# Stage-1 repair: thm-pod-global-verdier-duality

## Files written

- dag/nodes/sec-six-functors/thm-pod-global-verdier-duality.json: unchanged statement, five-step assembly of 2859 characters instead of ten steps totaling 7179 characters.
- dag/nodes/sec-six-functors/lem-pod-point-exchange-coefficient-realization.json: statement-only, status unsplit, no Mathlib match. General point-local realization of an arbitrary dual exchange and its coefficient square, with a separate compact-support identification u.
- dag/nodes/sec-six-functors/lem-pod-smooth-oriented-exchange-comparisons.json: statement-only, status unsplit, no Mathlib match. Site operation comparison square and its identification under the specified smooth orientation, before point evaluation.
- citations.json: every item-step citation has its cited node's complete statement as an exact verbatim quote.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag and global Verdier/globalDuality terminology and read SixFunctors/Etale/Derived/GlobalDuality.lean:149–230. AlgebraicGeometry.Etale.coefficientDualRightDerivedLowerShriekIso and nonempty_iso_coefficientDual_rightDerivedLowerShriek supply finite small-etale-coefficient results. The object-level shift declaration explicitly does not assert the coherence equality, and neither declaration supplies all four stages and their specified comparisons. Hence these declarations cannot attach the item. OrientationDatum.IsCompatibleCoefficientChange is a definition of a predicate; it does not prove that the specified purity family satisfies it. TensorHom.lean's derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv assumes coefficient squares/projection compatibility and does not supply the point realization or the smooth four-stage comparisons in the new nodes.

## WANTED

None. The proof follows the archived current blueprint and statements already present in the DAG. No new Stacks or external-source claim is introduced; the new source places are sentences in the blueprint proof, not Stacks section numbers. No SGA source is used.

## Return repaired

The return requires spreading work, not compressing the same proof. Two comparable independent tasks are now available: point realization (3086-character statement) and oriented site comparisons (3929-character statement). Neither depends on the other, neither has proof steps or proof dependencies, and neither is the global theorem with a renamed label. Their conclusions have different objects: arbitrary point objects and arbitrary supplied exchange squares in the first, site-level operations and orientations in the second. The parent combines them with an actual exchange isomorphism, the cohomology definitions, the unit calculation and the independent proper branch. It is below 3000 characters. There is no non-elementary step above 2000 characters.

The dispatcher supplied an empty sandbox (only .brief files), rather than the retained files described in the generic repair brief. I copied the live reviewed item, which has exactly the ten returned steps and their 7179 characters, as the baseline. I read the retained Q24 and Q26 reports and the Q24 reviewer repairs in the node, including the distinction between ctf point objects and site-perfect objects and the correct sources of t_Q. No unchanged searches were rerun or fabricated: existing item searches are retained; every new-node search was actually run through msearch.py, and its results read. The baseline is preserved locally in baseline.json; only the item and the two new DAG nodes are part of the delivery.

## Argument allocation

All old arguments are retained below verbatim so a future worker can recover them without reading a historical commit. Their task boundaries are as follows.

1. Old step 1 remains parent step 1, including identity compactification, bound 0, identity adjunction and comparison maps. Its canonical exchange e is an input to both new tasks.
2. Old step 2 is the isomorphism/naturality/shift portion of point-exchange-coefficient-realization, applied in parent step 2. The cohomology substitutions remain in that parent step; no point equivalence is assumed merely from the definition of Fib.
3. Old step 3 is the site square of smooth-oriented-exchange-comparisons, with the source explicitly delta followed by contravariance along u_Q inverse.
4. Old step 4 is the sections/coefficient transport of point-exchange-coefficient-realization. Its statement specifies t_Q at every stage and retains the tensor/unit constraints. Parent step 2 checks the ctf membership of C,T and their point dual using thm-sf-ctf-stability. No finite quotient is assumed flat.
5. Old step 5 is the domain-sensitive identification of operation maps in smooth-oriented-exchange-comparisons. It distinguishes the site-perfect finite-Hom domain on X, finite-Tor point Hom and ordinary-direct-image comparison, derived-complete integral objects, and rational/common-stage maps.
6. Old step 6 is the nontrivial source-square identification in point-exchange-coefficient-realization. Its conclusion explicitly includes w=F(u)t_C and (w inverse)^vee, so the argument must use naturality of j and t in C, not just the coefficient-dual comparison at Q_s C.
7. Old step 7 is the orientation portion of smooth-oriented-exchange-comparisons. It specifies the finite, reconstructed integral, scalar-natural integral and rational/common-stage family, not arbitrary lifts with matching reductions. Both gamma and its inverse eta have typed commutation equations.
8. Old step 8 is parent step 3: the two independently established squares are substituted into one another. The oriented site lemma also identifies the transported comparison with the actual oriented internal-Hom comparison, preventing an unspecified conjugation from hiding the desired compatibility.
9. Old step 9 remains parent step 4 verbatim, including evaluation at 1, its inverse and exactness of Hom from the free rank-one unit.
10. Old step 10 remains parent step 5. Its four separate purity references are now carried by the unconditional orientation assertion of the oriented-site node. The proper branch uses the constructible exceptional adjoint in thm-sf-global-duality, never ambient admissibility inferred from properness.

The two new tasks carry roughly 2731 and 1633 characters of the old comparison argument (old steps 2,4,6 versus 3,5,7), in addition to their application/substitution in the assembly. They do not pass the entire argument to one new child. Their statements give a future worker all domains and actual comparison maps; the following original text records the argument to split further or prove.

## Not duplicates

lem-pod-point-exchange-coefficient-realization vs lem-pod-point-dualizing-complex: the latter gives j, whereas the new node realizes an arbitrary e and transports a whole site square with a separately supplied u and v.
lem-pod-point-exchange-coefficient-realization vs lem-pod-point-duality-coefficient-compatibility: the latter gives the coefficient square for j alone at C; the new assertion identifies the evaluated exchange source after u:Q_s C -> C', including the contravariant inverse and the target comparison.
lem-pod-point-exchange-coefficient-realization vs lem-pod-point-scalar-hom-evaluation: the latter handles one finite-projective integral scalar-Hom model, with no arbitrary exchange and no finite reduction/target square.
lem-pod-point-exchange-coefficient-realization vs lem-sf-point-fibre-derived-tensor: the latter supplies only tensor/unit comparisons, not dual exchange realization or its source-square identification.
lem-pod-point-exchange-coefficient-realization vs lem-pod-global-duality-map-identification: the latter compares the particular global pairing/duality construction, depends on this item, and supplies no general coefficient-square transport. It cannot be cited here without a cycle.
lem-pod-point-exchange-coefficient-realization vs lem-sf-identification-exchange-comparison: that node compares tensor-Hom exchange at omega_s and at the unit; it does not transport an arbitrary coefficient square and u through j.
lem-pod-smooth-oriented-exchange-comparisons vs fix-cor-verdier-exchange: the exchange theorem gives e and compatibility, but does not identify its operation maps after insertion of the specified inverse purity orientation at every stage.
lem-pod-smooth-oriented-exchange-comparisons vs lem-fix-operation-reduction: the latter has only the listed operation domains, no purity family and no orientation-transported exchange square; in particular it does not give finite-quotient ordinary direct image.
lem-pod-smooth-oriented-exchange-comparisons vs thm-pur-finite-reduction-of-purity: finite purity reduction alone has neither integral/field comparison family nor the site-perfect internal-Hom exchange square.
lem-pod-smooth-oriented-exchange-comparisons vs thm-pur-adic-reconstruction: reconstruction supplies an integral lift with the finite reductions, not the full scalar-natural family and oriented site exchange.
lem-pod-smooth-oriented-exchange-comparisons vs lem-pur-adic-purity-scalar-naturality: this gives the integral scalar purity square, not the finite/field and operation-square identification.
lem-pod-smooth-oriented-exchange-comparisons vs thm-pur-rational-and-qbar-purity: this transports purity to field stages, without the point-independent site exchange square and its actual comparison maps.
lem-pod-smooth-oriented-exchange-comparisons vs det-sp-reduction-compatibilities: the latter is for ordinary constant finite coefficient rings and gives units/composition/purity; it has neither integral/field stages nor internal-Hom Verdier exchange under orientation.
lem-pod-smooth-oriented-exchange-comparisons vs prop-pod-dual-tate-data-compatibility: this concerns strict Weil structures and perfect dual/Tate objects, not site-level exchange-square identification for arbitrary K without a Weil structure or descent.
lem-pod-smooth-oriented-exchange-comparisons vs lem-pur-tower-trace-purity-comparison: that statement identifies integral trace-transpose and tower purity; it has no finite quotient or oriented site exchange assertion.
lem-pod-smooth-oriented-exchange-comparisons vs lem-pod-rational-purity-pairing: that concerns rational Weil/Frobenius compatibility and degreewise pairing, not coefficient change at all four stages.
lem-pod-smooth-oriented-exchange-comparisons vs lem-sf-identification-coefficient-transport: identity-point composition normalization has no smooth orientation or coefficient-change exchange square.
Neither new statement is a new instance of an existing Stacks tag; no tag collision exists. Whole-DAG statement scans and blueprint_refs searches for coefficient square, point dual, sections/coefficient, orientation, exchange, tensor/internal-Hom, oriented exchange and coefficient-duality square were made before creation; the above are the closest candidates. Existing global-duality formulations stay in the item's blueprint.same_as; neither new statement has a blueprint node stating it, so their same_as is [].

## Review by N9

I read the main-20261015 thm-pod-global-verdier-duality statement and its entire proof, the sec-six-functors chapter and sk-thm-sf-package unit route, the prior ten-step split, both previous reports and the attached independent review. The theorem statement, stmt_deps, imported blueprint data and Lean records are unchanged. There is no new statement dispute: in particular, the proper non-descending branch is read through its constructible exceptional adjoint, and the returned source never licenses assuming that properness implies ambient admissibility.

For the point-realization node, I read the complete statements of lem-pod-point-dualizing-complex, lem-pod-point-duality-coefficient-compatibility, lem-pod-point-sections-derived-reduction, lem-weil-point-sections-scalar-extension, lem-sf-point-fibre-derived-tensor, and def-weil-finite-coefficient-point. The source is the second blueprint proof paragraph, refined by these already reviewed canonical comparison statements. The t_Q maps use derived reduction, inverse phi, defining rationalization and tensoring sections respectively; the tensor lemma is used only for its unit/tensor constraints on ctf inputs, not on the generally nonperfect object (A_m)_s viewed over A_n. To type-check the square, u:Q_s C -> C' gives D_s(u inverse):D_s Q_s C -> D_s C'. The module arrow must therefore be (w inverse)^vee after b, with w=F(u)t_C. Applying naturality of j to u inverse gives exactly that direction. The point-duality comparison equation then identifies the source square; naturality of t transports v Q(e). This preserves the old step 6 argument instead of silently treating Q_s C and C' as equal. The independent task is to prove this comparison for the actual point fibre at the five kinds of coefficient passage, not just a formal diagram with unspecified maps.

For the oriented-site node, I read the current main-20261015 source statements of lem-fix-operation-reduction, thm-pur-finite-reduction-of-purity, thm-pur-adic-reconstruction and thm-pur-rational-and-qbar-purity, and the full DAG statement of lem-pur-adic-purity-scalar-naturality with its explicit counit-preserving scalar arrow. The source is the coefficient-comparison portion of the item's second paragraph, with these existing purity facts as its supporting route. The node separates unconditional smooth orientation compatibility from the additional admissibility assumption for the site exchange. The integral gamma is the specified scalar-natural family, not an arbitrary lift; reconstruction alone would not suffice. With z_Q:Q omega -> omega' and h_Q:Q H -> H', z_Q Q gamma = gamma' h_Q implies h_Q Q eta = eta' z_Q, so the inverse orientation equation is well typed. Applying internal Hom with site-perfect K and the actual operation comparisons identifies the transported exchange arrow, including the evaluation and counit maps. This is the work hidden by the old phrase 'under the smooth orientation'. No new purity route is introduced.

Parent step 1 cites def-pod-conventions for the actual structure morphism and its admissibility, fix-cor-verdier-exchange for the canonical isomorphism and its naturality/shifts, and def-weil-exceptional-adjoint-admissibility for the identity case. The identity compactification and all zero bounds check that the third admissibility hypothesis holds; no extra geometric hypothesis is smuggled in.

Parent step 2 uses thm-sf-ctf-stability for C, its point dual and T, including the integral/field domain, then exactly the isomorphism assertion of point-exchange-coefficient-realization. Def-weil-ordinary-compact-cohomology defines the two evaluated functors, so the substitutions have precisely the required source and target. These statements were read in full; their verbatim statements are in citations.json.

Parent step 3 uses the site-square conclusion and orientation-map identification of smooth-oriented-exchange-comparisons, then the coefficient-complex equation of point-exchange-coefficient-realization with C'=Ra_!Q_XK. It is not using a proof of either node or assuming site-perfectness of Ra_!K. The actual hypothesis needed at the point is ctf, already checked in step 2; site-perfectness is used only on X as stated.

Parent step 4 uses the definition of D_X in def-pod-conventions. Its evaluation-at-1 calculation, including its inverse and exactness, remains verbatim from the reviewed proof and is elementary.

Parent step 5 uses thm-sf-global-duality on its proper branch, which explicitly allows no descent and gives every asserted clause. Its statement already says the first displayed iso is in the coefficient-complex target, or equivalently in the point category; def-weil-finite-coefficient-point supplies the evaluation interpretation. The oriented-site node's first assertion has no admissibility, descent, connectedness or properness hypothesis, so it applies to the proper non-descending X and supplies the same orientation equations. This avoids applying the second, admissibility-requiring exchange assertion on that branch.

Small cases were checked on the new statements, not just on the parent: C=T=0; e the identity at a point; u an arbitrary nonidentity automorphism with v=D(u inverse), which detects the inverse/dual direction; Q the identity; m=n; n=1; a shifted unit; integral torsion C rationalizing to zero. Finite reduction m<n is derived and is not declared flat. For the oriented site case, X=s and d=0 give identity orientation, while a smooth nonproper X retains distinct Ra_! and Ra_*. For a smooth proper elliptic curve, the unconditional orientation statement applies but the extra ambient admissibility assumption of the exchange part is not inferred; the parent's proper branch uses the separate global theorem. The empty scheme, when allowed by the smooth pure-dimension convention, has zero cohomology and no point selection is used. Thus neither statement acquires an unnoticed connectedness/descent assumption or false flatness assertion.

I checked delivery-errors B through E: self-contained data and definition references, real archived source places, exact logged queries and honest verdicts, no proof in unsplit children, no duplicate or clause relabel, no proof-versus-statement citation, precise domains and actual comparison maps, no cyclic appeal to the pairing/map-identification node, no altered target or Lean, and no SGA route. The original ten steps appear below with their full argument, so no work has disappeared to meet a text limit.

## Mathlib search findings

For each new node, two distinct LeanFinder phrasings, Loogle, LeanSearch and Mathlib grep were run and are recorded exactly in searches.jsonl and mathlib_searches. For point realization, the hits are ordinary sheaf-section naturality, LightCondensed internal Hom, ModuleCat change-of-rings adjunctions and ordinary module dual base change; none supplies derived four-stage pro-etale point duality or its exchange comparison. I read Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:185–193 and CategoryTheory/Monoidal/Closed/Basic.lean:285–300: unitHomEquiv_symm_comp concerns underived sections, and internalHom's functoriality alone does not identify the stipulated point comparison. For oriented site comparisons, the results concern real vector-space orientation, smooth manifolds, Dold–Kan and generic naturality; the grep in Mathlib/AlgebraicGeometry has no smooth-purity/exchange result. These are no matches, not unavailable services. No Mathlib leaf is asserted. The existing item's old searches are retained without claiming they were run in this repair.

## Validation

Server review_split passed. The first full deliver.py --no-push exited successfully with OK at b37ed162099, including the maintainer preflight and DAG checks. After this validation note is added, the final dry run and the single direct push use the same unchanged mathematical files. No local checker, Lean compiler, Lake, git command in the shared repository, launcher edit or subagent was used.

## Prior argument, verbatim, with task ownership above

### Original step 1

Instantiate the Verdier exchange [fix-cor-verdier-exchange] at $f=a_X:X\to s$, $Y=s$, and $M=K$. The smooth separated finite-type scheme and the admissibility of $a_X$ are given by [def-pod-conventions]. The remaining structure morphism is $a_s=\operatorname{id}_s$. It satisfies [def-weil-exceptional-adjoint-admissibility]: take the identity compactification, cohomological-dimension bound $0$, identity right adjoint with identity unit and counit, and interval shifts $c^- = c^+ =0$; all coefficient comparisons are identities. Thus all three admissibility hypotheses of the exchange hold. It gives the canonical isomorphism $e_{\Lambda,K}:D_s(Ra_{X!}K)\xrightarrow{\sim}Ra_{X*}D_XK$, natural in $K$ and compatible with the specified coefficient comparisons and shifts.

Cited statements: def-pod-conventions, fix-cor-verdier-exchange, def-weil-exceptional-adjoint-admissibility.

### Original step 2

Apply the functor $\operatorname{Fib}_s$ defined at all four coefficient stages in [def-weil-finite-coefficient-point] to $e_{\Lambda,K}$; functors carry an isomorphism and its inverse to inverse morphisms. For $C=Ra_{X!}K$, [lem-pod-point-dualizing-complex] identifies the evaluated $D_sC$ with the derived coefficient dual of $\operatorname{Fib}_s C$. By [def-weil-ordinary-compact-cohomology], $\operatorname{Fib}_s C=R\Gamma_c(X,K)$ and $\operatorname{Fib}_s(Ra_{X*}D_XK)=R\Gamma(X,\mathbb D_XK)$. These identifications give the displayed canonical isomorphism. Their functoriality and the naturality and shift compatibility of $e$ give naturality in $K$ and shift compatibility of the result. No assertion that evaluation is an equivalence is needed for this step.

Cited statements: lem-pod-point-dualizing-complex, def-weil-finite-coefficient-point, def-weil-ordinary-compact-cohomology.

### Original step 3

Let $K$ be site-perfect as in [def-weil-site-perfect-complex]. For a stipulated finite reduction or scalar extension $Q$, let $L_Q$ and $R_Q$ be the comparison maps on the source and target of the exchange $e_{\Lambda,K}$. The coefficient-compatibility clause of [fix-cor-verdier-exchange] gives $R_Q\circ Q(e_{\Lambda,K})=e_{\Lambda',QK}\circ L_Q$.

Cited statements: def-weil-site-perfect-complex, fix-cor-verdier-exchange.

### Original step 4

Put $C=Ra_{X!}K$. The preservation assertions of [thm-sf-ctf-stability] place $C$, its point dual and $Ra_{X*}D_XK$ in the constructible finite-Tor point domain, including the integral and field passages. Apply $F_\Lambda=\operatorname{Fib}_s$ to the exchange equality. The stipulated sections/coefficient comparisons $t_Q:q\circ F_\Lambda\cong F_{\Lambda'}\circ Q_s$ on these objects are: for $\mathcal O_E\to A_{E,n}$ the derived-reduction isomorphism of [lem-pod-point-sections-derived-reduction]; for integral and common-stage scalar extension the inverse of $\varphi$ of [lem-weil-point-sections-scalar-extension]; for rationalization the identity of the definition [def-weil-finite-coefficient-point]; for $A_{E,n}\to A_{E,m}$ the tensoring-sections map, invertible by [lem-pod-point-duality-coefficient-compatibility]. Their unit and tensor constraints are those of [lem-sf-point-fibre-derived-tensor]. Applying $F_{\Lambda'}$ to the exchange equality and using naturality of $t_Q$ to replace $F_{\Lambda'}(Q_s e_{\Lambda,K})$ by $t_Q\circ q(F_\Lambda e_{\Lambda,K})\circ t_Q^{-1}$ gives the evaluated exchange equality, since a functor preserves compositions and equalities.

Cited statements: thm-sf-ctf-stability, def-weil-finite-coefficient-point, lem-sf-point-fibre-derived-tensor, lem-pod-point-sections-derived-reduction, lem-weil-point-sections-scalar-extension, lem-pod-point-duality-coefficient-compatibility.

### Original step 5

The comparison clauses of [lem-fix-operation-reduction] identify the tensor, internal-Hom, evaluation, compact-support and adjunction maps in this square on their stated domains. For its finite-quotient site-level internal Hom on $X$ the first argument is the assumed site-perfect $K$. For point Hom use the finite-Tor comparison of [thm-sf-ctf-stability]. Integral reduction uses the derived-complete domain, and field passages use rationalization and common-stage comparisons. Thus no unasserted finite-quotient ordinary-direct-image isomorphism is inferred from the operation-reduction lemma.

Cited statements: lem-fix-operation-reduction, def-weil-site-perfect-complex, thm-sf-ctf-stability.

### Original step 6

Apply [lem-pod-point-duality-coefficient-compatibility] to $C=Ra_{X!}K$, whose point-domain membership was checked in step 4. Its displayed equation identifies the evaluated source comparison, after the specified point-dualizing identification $j$, with the coefficient-dual comparison. The source comparison of step 3 is $\delta_{Q,C}$ followed by $D_s$ of the compact-support coefficient isomorphism $Q_sRa_{X!}K\cong Ra_{X!}QK$; naturality in $C$ of the canonical identification $j_{\Lambda',-}$ of [lem-pod-point-dualizing-complex] and of $t_Q$ carries the displayed equation along that isomorphism. Consequently the evaluated exchange square is exactly the coefficient-duality square for $g=F_\Lambda(e_{\Lambda,K})\circ j_{\Lambda,C}^{-1}$, the global isomorphism of step 2.

Cited statements: lem-pod-point-duality-coefficient-compatibility, lem-pod-point-dualizing-complex.

### Original step 7

For $f=a_X$ and the unit on $s$, use the smooth-orientation comparisons already supplied by the purity chapter. Finite reduction of $\gamma_{a_X,\Lambda}$ is its lower-level comparison by [thm-pur-finite-reduction-of-purity]. Its integral comparison reduces to those finite maps by [thm-pur-adic-reconstruction]. Under integral coefficient-field extension it satisfies $b\circ C(\gamma_E)=\gamma_F\circ a$ by [lem-pur-adic-purity-scalar-naturality]. Rationalization and common-stage extension carry this adic comparison to the field comparison by [thm-pur-rational-and-qbar-purity]. Inverting these isomorphisms gives the coefficient compatibility of the convention's orientation $\eta_X$.

Cited statements: thm-pur-finite-reduction-of-purity, thm-pur-adic-reconstruction, lem-pur-adic-purity-scalar-naturality, thm-pur-rational-and-qbar-purity.

### Original step 8

Insert the point-duality comparison equation of step 6 and the orientation equations of step 7 into the evaluated exchange equality of steps 3--5. Both paths are then the same composite; this is the requested compatibility of $g$ with finite reduction and scalar extension under the smooth orientation.

Cited statements: .

### Original step 9

For the unit object, [def-pod-conventions] gives $\mathbb D_X\Lambda_X=R\mathcal Hom_X(\Lambda_X,\omega_{X,\Lambda})$. The unit Hom identity is evaluation at $1$: $h\mapsto h(1)$, with inverse $x\mapsto(r\mapsto rx)$. Since internal Hom from the free rank-one unit is already the identity exact functor, its derived functor is the identity as well. Thus $\mathbb D_X\Lambda_X\cong\omega_{X,\Lambda}$, and substitution in step 2 gives $R\Gamma_c(X,\Lambda_X)^\vee\cong R\Gamma(X,\omega_{X,\Lambda})$.

Cited statements: def-pod-conventions.

### Original step 10

For $X=X_0\times_{k_0}k$, steps 1--9 apply to every separated smooth $X_0$ in [def-pod-conventions]: no step replaces $Ra_{X!}$ by $Ra_{X*}$, so properness is not needed. For the alternative smooth proper geometrically connected $k$-scheme $X$ of pure dimension $d$, use the proper branch of [thm-sf-global-duality]. Its hypotheses require no descent to $k_0$ and its conclusion supplies the canonical global isomorphism, naturality, shifts, coefficient compatibilities and unit specialization. Applying $\operatorname{Fib}_s$ of [def-weil-finite-coefficient-point] reads its isomorphism in the point category as the displayed isomorphism of coefficient complexes. These imply the requested clauses, with coefficient compatibility restricted to site-perfect $K$; its comparisons are read under the smooth orientation of the smooth separated $a_X$ through the same orientation compatibilities as in step 7 ([thm-pur-finite-reduction-of-purity], [thm-pur-adic-reconstruction], [lem-pur-adic-purity-scalar-naturality], [thm-pur-rational-and-qbar-purity]), which require no descent and no properness. This appeal uses its constructible exceptional adjoint and does not assume that properness supplies the stronger ambient admissibility condition.

Cited statements: def-pod-conventions, thm-sf-global-duality, def-weil-finite-coefficient-point, thm-pur-finite-reduction-of-purity, thm-pur-adic-reconstruction, lem-pur-adic-purity-scalar-naturality, thm-pur-rational-and-qbar-purity.

## Remaining work

The two new unsplit nodes are independent queued stage-1 proof tasks, as requested by the return. The repaired split passed the server checks; the authorized direct delivery follows the final dry run.
