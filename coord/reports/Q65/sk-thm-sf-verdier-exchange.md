## Worker report

Q65 repaired the returned stage-1 split. The sandbox initially had only dispatcher marker files: no node, report, citations or search log. I recovered the exact returned eight-step proof from the current shared node and retained the Q84 report from coord/reports/Q84. Thus there was no sandbox attempt or search log to overwrite. I ran the required initial dry run on that recovered copy; it stopped because the old report had no Review by Q65. I then made the substantive repair below. The delivery tool rebases the stage-1 fields on current origin; no git command was run by me in the shared repository.

Files written:

- dag/nodes/sec-six-functors/sk-thm-sf-verdier-exchange.json: statement unchanged; four assembly steps, 2464 characters total, status split.
- dag/nodes/sec-six-functors/lem-sf-constructible-exceptional-compositor.json: statement, unsplit, no Mathlib match. Constructible geometric composition, its Hom bijection and its actual counit characterization at all coefficient stages.
- dag/nodes/sec-six-functors/lem-sf-finite-exceptional-compositor-coefficients.json: statement, unsplit, no Mathlib match. Finite geometric composition/coefficient square and the counit-transpose calculation for exceptional composition, including ramification.
- dag/nodes/sec-six-functors/lem-sf-adic-exceptional-compositor-coefficients.json: statement, unsplit, no Mathlib match. Actual normalized-system mate, its completed realization and the higher-coefficient composition equations.
- dag/units/sk-thm-sf-verdier-exchange.json: only realized and realized_by filled, binding the unchanged unit's single proof paragraph to the item and these three nodes.
- citations.json: all ten assembly step/node citations backed by verbatim statement quotations. Search outputs and searches.jsonl remain in the sandbox.

Attachments: none. I read WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean lines 383–428 and the declaration/docstring of Sheaf/Paper/VerdierExchange.lean lines 782–838. The two upstream Nonempty-isomorphism declarations only give finite-ring isomorphisms, not the full canonical all-stage compatibility assertion; the project theorem verdier_exchange still ends in sorry. Neither finishes this item. No Lean was written, compiled or built.

WANTED: none. All sources needed for this one-level split are already present.

## Repair of the return

The return asked for at least three comparable independent statement-only obligations and an assembly of at most 3000 characters, with no lost argument. There are three new unsplit statements of lengths 2170, 2695 and 3437 characters; all have proof=[], proof_deps=[], proof_origin=null. Their proofs are reserved for future workers. They concern arbitrary composable separated finite-type morphisms X→Y→Z, not merely the structure-map specialization or the whole Verdier exchange. The work divides into construction, finite comparison, and coherent completion/field comparison. No new node states the whole item.

The old argument is accounted for as follows. Old step 1 stays as the elementary unit-and-functor typing in assembly step 1. Old step 2 is the constructible compositor obligation, including its Hom-chain, inverse direction, pasted counit, and all coefficient-stage interpretations. Old step 3 stays as assembly step 2, with the inverse tensor–Hom arrow and postcomposition displayed. Old step 4 stays as assembly step 3, with the contravariant naturality square and [-r] shift. Old steps 5 and 6 become the finite-coefficient obligation: both geometric q square and right-adjoint b/c square, with their common transpose, are in its statement; the complete two-transpose computation remains below for its future worker. Old step 7 becomes the adic obligation, explicitly requiring equality of actual derived-system maps before total limit and the actual compositor after realization, with the finite-free en subsequence and morphism-level field transport. Old step 8 is assembly step 4: evaluate at the unit, form kappa, and paste with tensor–Hom's coefficient square. The full old text is reproduced below without shortening. The original source places and the Q84 report are retained as well.

## Sources and searches

I read the current main-20261015 Verdier-exchange _section.md and proof.md, the chapter and unit records, SETUP's three levels and GOAL. The blueprint explicitly uses compact-support composition and its mate, then tensor–Hom; none of the new statements uses biduality or a duality-based formula for exceptional pullback. No prohibited SGA source is used.

For the constructible compositor I read the statements of lem-sf-constructible-exceptional-adjunction-coefficients, thm-sf-comp-composition, fix-lem-exchanges, lem-weil-pbc-mate-pasting and def-weil-pbc-adjunction-conjugate. They give, respectively, the actual all-stage adjunctions, finite geometric compositor, completed/transported compositor, composite adjunction/counit, and conjugation bijection preserving isomorphisms. I also read Stacks more-etale.tex Tag 0F7J, lemma-shriek-composition (line 3159 onward): compatible compactifications, proper composition and proper/open interchange. That tag supplies the geometric starting point, not the all-stage right-adjoint statement by itself.

For the finite comparison I read lem-sp-et-proet-coefficient-compatibility's displayed canonical composition/coefficient equation and the exact counit equation in the constructible-adjunction theorem; Stacks Tag 0GL6, remark-Rf-lower-shriek-change-of-rings (more-etale.tex line 3739 onward) gives the underlying torsion change-of-rings comparison. The finite statement records the geometric square plus its exceptional mate, not a claim that 0GL6 alone asserts all coherence. The actual counit calculation is the retained old step 6 below.

For the adic comparison I read all four statements lem-coef-cartesian-section-adjoint-mates, lem-pur-finite-coefficient-adjoint-comparisons, lem-coef-semilinear-derived-sections and lem-sf-integral-compactification-system-realization. The first provides actual system adjunction maps and ordinary system mates of geometric composition. The second supplies coherent finite-free as well as quotient comparisons. The third gives simultaneous derived system operations and evaluation of specified mates without faithfulness on morphisms. The fourth intertwines the actual proper/open composition maps with total-limit realization on uniformly bounded constructible inputs. Their stronger system assertions are explicitly agent-formulated, not misattributed to their foundational Stacks tags. This is why the new nodes cite the blueprint's expanded argument as their source rather than falsely claiming a Stacks theorem with these exact conclusions.

Before creating any node I searched every DAG statement for exceptional/composition, conjugate/coefficient and composition/right-adjoint combinations, searched the relevant Stacks tags and key words with rg, and ran blueprint_refs ancestor and whole-blueprint searches for exceptional composition, adjoint composition, coefficient conjugate, counit coefficient, exceptional inverse image, exceptional coefficient, integral composition and Verdier exchange. I opened the relevant hits listed in Not duplicates. The same_as list is empty for each new specialized obligation; the item's existing thm-sf-verdier-exchange sibling correspondence is retained.

For EACH new id, five searches ran through the required msearch command: LeanFinder in two different phrasings, LeanSearch, Loogle and Mathlib grep. Every service returned a result, so none is falsely recorded unavailable. All query strings are copied exactly from the search plan and the command's log; every returned hit was read in the saved raw output. No historical Q84 search is represented as newly run.

The closest Mathlib results were conjugateIsoEquiv (Adjunction/Mates.lean line 425), mateEquiv_hcomp (line 209), conjugateEquiv_mateEquiv_vcomp (line 505), and Adjunction.comp, plus ordinary SheafOfModules.pushforwardComp (Sheaf/PushforwardContinuous.lean line 139) and derived-adjunction localization infrastructure. I read these source declarations. The generic conjugate and pasted-mate facts are ALREADY covered by the existing DAG nodes, and are to be reused in proving these obligations. They do not construct the actual geometric compactification compositors or compare their finite, completed and common-stage realizations. pushforwardComp is Iso.refl for ordinary sheaf-module pushforward. It cannot supply either the proper/open geometric square or the system realization. The other semantic hits concerned constructible sets, ramification of ideals, adic completion of modules and condensed modules. None states any of these geometric all-stage obligations, nor is a whole node a one-line specialization of it. Therefore all three new nodes stay unsplit with mathlib_match=null, and there are zero new Mathlib leaves.

## Review by Q65

I checked delivery-errors B–E against the actual node statements and source text. The return is a workload repair; the item's accepted statement, including all compatibility qualifications, is byte-for-byte unchanged. The earlier STATEMENT-DISPUTED correction is retained: the doubled-origin affine line with f=id is separated as a morphism but its structure map is not separated, so the original unconstrained scheme formulation did not type-check the dualizing object. The already corrected item requires separated X and Y. The new general compositor statements impose separated finite-type X,Y,Z, so every structure-map application in the parent is in their domain. No further statement correction is made.

Assembly step 1 cites sk-def-sf-setting for the coefficient unit and its integral/field conventions, sk-def-sf-operations(vi) for the actual constructible functor type, and the NEW constructible compositor for the canonical isomorphism c. I checked the last node really states an all-stage natural isomorphism for any L, with the direction G_f G_g→G_x; hence evaluation at L=Lambda_s proves exactly the needed comparison. The Hom bijection uses precomposition with alpha inverse, consistent with that direction. Absolute separatedness makes a_Y and a_X separated finite type. The unit has Tor interval [0,0], so no preservation theorem is smuggled in from an optional ambient functor.

Assembly step 2 cites sk-thm-sf-tensor-hom, whose statement is precisely the ambient D+ isomorphism in the reverse direction, natural in both inputs and compatible with coefficient comparisons and shifts. Its hypotheses are met by step 1 and the given M. sk-def-sf-operations(i) really defines internal Hom as a bifunctor, so postcomposing with c and applying Rf_* carries an isomorphism to an isomorphism. These are the two displayed arrows, not an appeal to the proof of a cited node.

Assembly step 3 is elementary after those citations: naturality for the first arrow is stated by tensor–Hom, while bifunctoriality makes precomposition and postcomposition commute for the second. The displayed equation has the contravariant order correct. Derived Hom in the first argument changes [r] into [-r]; postcomposition by a degree-zero map preserves that identification. No independent geometric assertion is hidden in this step.

Assembly step 4 cites the NEW finite node for the b_x C(c)=c G_f(b_g)b_f equation at finite quotients and finite-free ramified maps. It cites the NEW adic node for the identical equation for integral reduction, completed extension, rationalization and common stages. I read these equations in both statements and copied their actual text into citations.json; they do not merely define q or b. Put g=a_Y and L=Lambda_s and use naturality with C_s Lambda_s→Lambda'_s to obtain the kappa equation written in the parent. Naturality of the specified Hom and direct-image comparisons yields the postcomposition square, and the tensor–Hom statement explicitly supplies the other square. Pasting gives compatibility of the composite; it claims no extra coefficient-change isomorphism on arbitrary ambient objects. The field reduction qualification is explicit in the adic statement.

Each new statement introduces its field, coefficient rings, schemes, maps, functors, counits, coefficient change and every variable in its equations. The three definition dependencies genuinely supply the coefficient categories, operations and conjugation notion. Finite systems in the third statement are defined inline, including semilinearity, normalization and uniform bounds. I did not put proof sketches into the new statements: the displayed Hom and transpose formulas are the precise conclusions future proofs must establish; their arguments remain in this report. New proof and proof-dependency lists are empty. All new nodes carry the item's chapter/unit, a worker creation stamp, explicit blueprint.from.place for the source sentence they expand and same_as=[]; none asserts it is an imported blueprint node.

I recalculated the finite common transpose with all objects typed. Its source is F_x,B C_X(G_f,A G_g,A L), and its target is C_Z L. The inverse alpha_B goes first, then inverse q_gf, then C_Z(beta_A). Expanding the other transpose moves b_g past epsilon_f by naturality, eliminates the f counit with its normalized coefficient equation, and then eliminates the g counit; the left geometric square identifies the result. This is exactly the old two-transpose argument now assigned to the finite obligation. It does not assume an arbitrary mate of an invertible square is invertible; the b maps and the c conjugates have their separately specified invertibility.

For the adic obligation, all F/G intermediate inputs stay constructible finite-Tor by the existing exact-adjunction theorem, with common intervals for the finite diagram from the coefficient conventions and its uniform bounds. The normalized-system construction is performed BEFORE total inverse limit. The actual integral compositor is identified via the proper/open realization theorem, and adjunction uniqueness identifies its right conjugate. Evaluation detects isomorphisms, but no equality is inferred merely from equal evaluated arrows. Finite extension uses (varpi_E^n)=(varpi_E'^{en}) and a cofinal en subsequence. Rationalization is on morphisms as well as objects, and common-stage comparisons are made after a common finite extension. These qualifications are substantive obligations of the third node, not omitted details.

Small cases checked for the new statements: f or g an identity reduces alpha and its conjugate to the specified identity normalizations and the counit equation to a triangle/naturality identity. L=0 and the empty schemes give zero-map identities. At the one-point scheme the comparisons reduce to the usual module adjunction and scalar comparison. For A_n→A_n and E'=E the coefficient equations are the identity square. A nonflat quotient A_2→A_1 remains allowed because every tensor is derived and every input has the stated finite Tor interval. A ramified e>1 extension uses en, not n. For shifts, the Hom first argument reverses the shift; c is a degree-zero natural transformation. No smoothness, purity orientation, or arbitrary ambient exceptional adjunction is assumed. All these checks agree with the retained proof route and prevent the usual E1/E4 mistakes.

There is no step over 2000 characters in the new parent. I inspected the four assembly arguments for concealed claims: the independent construction, finite transpose, and coherent realization have actually become three queued statements, not one oversized replacement. All old non-elementary citations still needed by those future arguments appear with their exact roles in Sources and searches and in the unabridged retained proof below. The parent now cites the new statements for their conclusions, never for proof internals. No existing node was changed apart from the item and its unit realization fields.

## Not duplicates

lem-sf-constructible-exceptional-compositor vs def-weil-pbc-adjunction-conjugate: the latter is abstract conjugation infrastructure; the former concerns the specified geometric constructible compositor and its actual all-stage realization and counit.
lem-sf-constructible-exceptional-compositor vs thm-sf-comp-composition: the existing theorem only states finite-coefficient compact-support composition, not exceptional composition or its integral/field construction.
lem-sf-constructible-exceptional-compositor vs def-sf-verdier-exchange-data: the definition supplies stage data and predicates; it asserts no existence theorem for the geometric comparison.
lem-sf-constructible-exceptional-compositor vs lem-sf-identification-coefficient-transport: the existing lemma treats the identity map on Spec k composed with a structure map, not general composable maps.
lem-sf-finite-exceptional-compositor-coefficients vs lem-sp-et-proet-coefficient-compatibility: the existing theorem gives the LEFT compact-support q square; the new obligation includes its RIGHT exceptional c/b comparison and explicit common counit transpose.
lem-sf-finite-exceptional-compositor-coefficients vs lem-pur-finite-adjoint-mate-compatibility: that lemma's composition clause assumes both maps smooth and treats same-field finite quotient reduction; the new lemma treats arbitrary separated finite-type maps and ramified finite-free changes as well.
lem-sf-finite-exceptional-compositor-coefficients vs lem-weil-pbc-mate-pasting: generic mate laws do not identify the specified geometric coefficient and composition maps; the new obligation proves that identification using those laws and the geometric square.
lem-sf-adic-exceptional-compositor-coefficients vs lem-pur-composition-comparison-scalar-compatibility: the existing lemma is for smooth pure-relative-dimension maps at rational coefficients; the new obligation includes arbitrary separated finite-type maps, coherent systems and integral reduction.
lem-sf-adic-exceptional-compositor-coefficients vs lem-coef-cartesian-section-adjoint-mates: the existing lemma constructs system adjunctions and mate operations, not their identification with the actual all-stage exceptional compositor square.
lem-sf-adic-exceptional-compositor-coefficients vs lem-sf-integral-compactification-system-realization: the existing lemma realizes proper/open compact-support expressions and their generators; the new statement identifies their exceptional right-adjoint conjugate and higher coefficient squares.
lem-sf-adic-exceptional-compositor-coefficients vs lem-sf-constructible-exceptional-coefficient-coherence: coefficient COMPOSITION for a single f and compactification REFINEMENT is distinct from composition of two GEOMETRIC morphisms f,g and its exceptional conjugate.
All three new nodes vs lem-sf-package-exceptional-coherence-realization and lem-sf-package-verdier-coefficient-realization: these downstream package theorems already invoke Verdier duality and cannot supply the cycle-free construction required here. The new statements do not use them.

## Validation

Initial recovered-copy dry run: stopped at missing Review by Q65, as expected from the retained Q84 report. The repaired delivery must pass the required server preflight, check_dag and review_split via deliver.py --no-push, and only then be pushed with deliver.py. No local compiler or forbidden local DAG/preflight checker was invoked. Server outputs are retained in the sandbox.

## Retained original proof: unabridged worker material

The following is the full returned proof, preserved for the independent reader and future workers. It is NOT a proof field of any new unsplit node.

### Returned step 1

The coefficient unit $\Lambda_s$ is in $\Dctf(s,\Lambda)$: at a finite stage it is a constant free rank-one module in degree zero, and tensoring with it is the identity, hence its Tor interval is $[0,0]$. At the integral stage use its compatible rank-one reductions, and at the field stages its scalar images, with the conventions of [sk-def-sf-setting]. Since $a_X$ and $a_Y$ are separated and finite type, the functor type in [sk-def-sf-operations](vi) gives $\omega_X\in\Dctf(X,\Lambda)$ and $\omega_Y\in\Dctf(Y,\Lambda)$. This is an application of the specified constructible functors, not of the optional ambient functor in (v). In particular $N=\omega_Y$ is an allowed input to the tensor–Hom exchange.

Uses: sk-def-sf-setting, sk-def-sf-operations.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Step 1 and the typing needed for Step 2.

### Returned step 2

Write $F_h=Rh_!$ and $G_h=Rh^!$ for $h=f,a_Y,a_X$. Their exact constructible adjunctions, with finite-Tor preservation at every coefficient stage, are [lem-sf-constructible-exceptional-adjunction-coefficients]. The canonical composition isomorphism $\alpha:F_{a_Y}F_f\xrightarrow{\sim}F_{a_X}$ is [thm-sf-comp-composition] at finite coefficients. At the other stages use its completed and transported forms explicitly included in [fix-lem-exchanges](2),(4), not the finite theorem applied to a different coefficient category. The mate calculus [lem-weil-pbc-mate-pasting](2) supplies the composite adjunction $F_{a_Y}F_f\dashv G_fG_{a_Y}$ with pasted unit and counit. For $K\in\Dctf(X,\Lambda)$ and $L\in\Dctf(s,\Lambda)$ its Hom bijection is
$$\operatorname{Hom}_X(K,G_fG_{a_Y}L)\cong\operatorname{Hom}_s(F_{a_Y}F_fK,L)\xrightarrow{h\mapsto h\circ\alpha_K^{-1}}\operatorname{Hom}_s(F_{a_X}K,L)\cong\operatorname{Hom}_X(K,G_{a_X}L).$$
Equivalently, conjugate $\alpha^{-1}$ between these two adjunctions using [def-weil-pbc-adjunction-conjugate]. That node asserts that this conjugation preserves isomorphisms and sends inverse transformations to inverse transformations. It therefore gives a canonical natural isomorphism $c:G_fG_{a_Y}\xrightarrow{\sim}G_{a_X}$. Evaluating at $L=\Lambda_s$ gives $c_\Lambda:Rf^!\omega_Y\xrightarrow{\sim}\omega_X$. All adjunctions here are on constructible categories; no full ambient pro-étale exceptional adjoint is used.

Uses: lem-sf-constructible-exceptional-adjunction-coefficients, thm-sf-comp-composition, fix-lem-exchanges, lem-weil-pbc-mate-pasting, def-weil-pbc-adjunction-conjugate.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Step 1: structure-morphism composition and its adjunction mate.

### Returned step 3

Apply [sk-thm-sf-tensor-hom] with the given $M$ and with $N=\omega_Y$, whose finite-Tor constructible membership was checked in step 1. Take the inverse of its displayed isomorphism, since the required direction is from internal Hom on $Y$ to direct image on $X$, and then apply the functor $Rf_*\RHom_X(M,-)$ to $c_\Lambda$ from step 2. With the internal Hom operation of [sk-def-sf-operations](i), this is
$$\mathbb D_Y(Rf_!M)=\RHom_Y(Rf_!M,\omega_Y)\xrightarrow{\sim}Rf_*\RHom_X(M,Rf^!\omega_Y)\xrightarrow{Rf_*\RHom_X(M,c_\Lambda)}Rf_*\RHom_X(M,\omega_X)=Rf_*\mathbb D_XM.$$
Define $\varepsilon_{f,M}$ to be this composite. The first arrow is an isomorphism in the ambient $D^+(Y,\Lambda)$ by the cited exchange theorem; the second is the image of an isomorphism under a functor, hence an isomorphism in the same category.

Uses: sk-thm-sf-tensor-hom, sk-def-sf-operations.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Step 2: specialize tensor–Hom exchange and substitute Step 1.

### Returned step 4

For $u:M\to M'$, the naturality in [sk-thm-sf-tensor-hom] gives the contravariant naturality square for the first arrow of step 3. For the second arrow, precomposition by $u$ and postcomposition by $c_\Lambda$ commute by the bifunctoriality of the internal Hom of [sk-def-sf-operations](i). Applying $Rf_*$ and pasting the two squares gives
$$Rf_*\mathbb D_X(u)\circ\varepsilon_{f,M'}=\varepsilon_{f,M}\circ\mathbb D_Y(Rf_!u).$$
For a shift $M[r]$, the derived Hom shift identification is $\RHom_X(M[r],N)=\RHom_X(M,N)[-r]$; applying postcomposition by the fixed degree-zero map $c_\Lambda$ gives the shifted postcomposition map. The shift compatibility of the first arrow is the one asserted by [sk-thm-sf-tensor-hom]. Thus under the canonical identifications both sides and the entire exchange for $M[r]$ are the shifts by $[-r]$ of their values at $M$.

Uses: sk-thm-sf-tensor-hom, sk-def-sf-operations.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Final sentence: naturality and shifts.

### Returned step 5

For a finite quotient or finite-free coefficient extension $A\to B$, write $C_T=-\otimes_A^LB_T$, $F_h=Rh_!$ and $G_h=Rh^!$. The counit-normalized comparisons $q_h:C F_{h,A}\xrightarrow{\sim}F_{h,B}C$ and $b_h:C G_{h,A}\xrightarrow{\sim}G_{h,B}C$ are [lem-sf-constructible-exceptional-adjunction-coefficients]. Its counit equation reads
$$\epsilon_{h,B,CL}\circ F_{h,B}(b_{h,L})=C(\epsilon_{h,A,L})\circ q_{h,G_{h,A}L}^{-1}.$$
For $a=a_Y$, $x=a_X$ put $q_{a,f}=(F_{a,B}q_f)\circ(q_aF_{f,A})$. The geometric composition square
$$q_x\circ C_s(\alpha_A)=\alpha_B\circ q_{a,f}$$
is exactly the composition clause of [lem-sp-et-proet-coefficient-compatibility], used with $g=a$. That statement permits every homomorphism of finite rings annihilated by powers of $\ell$, hence both quotients and $A_{E,n}\to\mathcal O_{E'}/\varpi_E^n\mathcal O_{E'}$, including ramified extensions. All inputs are finite-Tor constructible by the adjunction theorem; $X,Y,s$ are separated finite type, as required by the geometric comparison. Thus the square concerns the specified compactification composition maps, not chosen objectwise isomorphisms.

Uses: lem-sf-constructible-exceptional-adjunction-coefficients, lem-sp-et-proet-coefficient-compatibility.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Final compatibility sentence: geometric composition/coefficient square.

### Returned step 6

Set $Z_L=G_{f,A}G_{a,A}L$ and $\beta_{A,L}=\epsilon_{a,A,L}\circ F_{a,A}(\epsilon_{f,A,G_{a,A}L})$. This is the pasted counit of [lem-weil-pbc-mate-pasting](2). The defining transpose identity for the conjugate $c_A$ of step 2 is
$$\epsilon_{x,A,L}\circ F_{x,A}(c_{A,L})\circ\alpha_{A,Z_L}=\beta_{A,L}.$$
We compare the two maps
$$b_{x,L}\circ C_X(c_{A,L}),\qquad c_{B,C_sL}\circ G_{f,B}(b_{a,L})\circ b_{f,G_{a,A}L}$$
from $C_XZ_L$ to $G_{x,B}C_sL$. Transposing the first, the counit equation of step 5 and naturality of $q_x$ give
$$C_s(\beta_{A,L})\circ C_s(\alpha_{A,Z_L}^{-1})\circ q_{x,Z_L}^{-1}
=C_s(\beta_{A,L})\circ q_{a,f,Z_L}^{-1}\circ\alpha_{B,C_XZ_L}^{-1}.$$
Here the equality is precisely step 5's composition square. Transposing the second gives
$$\beta_{B,C_sL}\circ F_{a,B}F_{f,B}(G_{f,B}(b_{a,L})\circ b_{f,G_{a,A}L})\circ\alpha_{B,C_XZ_L}^{-1}.$$
Expand $\beta_B$. Naturality moves $b_a$ past $\epsilon_{f,B}$; replace $\epsilon_{f,B}F_{f,B}(b_f)$ by $C_Y(\epsilon_{f,A})q_f^{-1}$. Then replace $\epsilon_{a,B}F_{a,B}(b_a)$ by $C_s(\epsilon_{a,A})q_a^{-1}$. Naturality of $q_a$ makes the result the first transpose displayed above. The adjunction bijection makes the original maps equal. This is the explicit instance of mate pasting and changing adjunctions in [lem-weil-pbc-mate-pasting](2),(3).

Uses: lem-weil-pbc-mate-pasting.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Final compatibility sentence: compute both counit transposes.

### Returned step 7

For integral coefficients the same calculation takes place on coherent cartesian sections before total inverse limit. Apply [lem-coef-cartesian-section-adjoint-mates] to the enhanced finite $F_h$, coherent invertible $q_h,b_h$ and adjunctions supplied by [lem-pur-finite-coefficient-adjoint-comparisons]. The former statement supplies actual section units, counits, and naturality for composition comparisons. The geometric comparisons and their composites have simultaneous enhanced models by [lem-coef-semilinear-derived-sections]. Consequently the transposition and equality in step 6 are identities of section maps, rather than an inference that evaluated derived morphisms determine a system morphism.
The integral compactification realization [lem-sf-integral-compactification-system-realization] intertwines nested compact supports and their composition maps, including the proper/open interchange, with total-limit realizations. Its hypotheses hold: all inputs here are normalized constructible systems with common Tor and cohomological bounds by [lem-sf-constructible-exceptional-adjunction-coefficients] and the coefficient conventions. That same adjunction theorem identifies the integral $b_h$ as the counit-normalized comparisons and includes their integral-reduction and integral-scalar-extension equations. Thus applying the section construction and its integral realization to step 6 gives exactly the integral equation for $c$, by uniqueness of conjugation [def-weil-pbc-adjunction-conjugate]. Finite extension uses the compatible finite-free systems at levels $en$, where $(\varpi_E^n)=(\varpi_{E'}^{en})$, and their common-stage identifications in the adjunction theorem. Rationalization and passage to common finite stages carry the same equation to field coefficients. No arbitrary family of finite derived maps is lifted in this argument.

Uses: lem-coef-cartesian-section-adjoint-mates, lem-pur-finite-coefficient-adjoint-comparisons, lem-coef-semilinear-derived-sections, lem-sf-integral-compactification-system-realization, lem-sf-constructible-exceptional-adjunction-coefficients, def-weil-pbc-adjunction-conjugate.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Final compatibility sentence: coherent integral and field passage.

### Returned step 8

Put $L=A_s$ in the coefficient equation of step 6, or its integral/field realization of step 7, and set $\kappa_T=b_{a_T,A_s}$ followed by $G_{a_T,B}(C_sA_s\cong B_s)$. Naturality in $L$ gives
$$\kappa_X\circ C_X(c_A)=c_B\circ G_{f,B}(\kappa_Y)\circ b_{f,\omega_{Y,A}}.$$
The operation comparisons are natural in their inputs. Apply this equation to postcomposition in $Rf_*\RHom_X(M,-)$: it gives the coefficient square for the second arrow in step 3, under the internal-Hom and direct-image comparison maps of [sk-thm-sf-tensor-hom]. The coefficient square for the first arrow is explicitly part of that theorem. Pasting the squares proves compatibility of $\varepsilon_{f,M}$. At field coefficients finite reduction means reducing chosen integral representatives before rationalization, as in [lem-sf-constructible-exceptional-adjunction-coefficients]; it is not an additional functor from fields to torsion coefficients. Every comparison is used only on its stated domain, without asserting any arbitrary-input internal-Hom coefficient isomorphism.

Uses: sk-thm-sf-tensor-hom, lem-sf-constructible-exceptional-adjunction-coefficients.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/sk-thm-sf-verdier-exchange.proof.md; Final compatibility sentence: evaluate at the coefficient unit and paste.

## Retained prior report by Q84

## Worker report

Files written: `dag/nodes/sec-six-functors/sk-thm-sf-verdier-exchange.json` (statement, split, no whole-item Mathlib match); `citations.json` records every step/node pair. No new nodes and no new Mathlib leaves. The sandbox initially contained an exact copy of the current unsplit repository node, including the earlier reviewed proof and coefficient searches, but no report or search log. I retained its statement correction, first four arguments, actual transpose calculation, source references and historical searches. The new searches made during this continuation are logged in searches.jsonl; their results are not falsely attributed to the older search records.

Attachments: the two `AlgebraicGeometry.Etale.nonempty_iso_...` declarations in `WeilConjectures/SixFunctors/Etale/Derived/TensorHom.lean` cover the finite-ring isomorphisms, not the integral/field coefficient and coherence clauses. Neither is an attachment for this complete item. The `lean_audit` open affine torsion cohomological-dimension declaration is already covered by `thm-sc-affine-torsion-cd`, not a new obligation specific to this item.

WANTED: none.

## Statement corrected

STATEMENT-DISPUTED: the imported source allows nonseparated X,Y even though its dualizing object uses the separated finite-type structure morphism. Take X=Y equal to the affine line with doubled origin over k and f=id. The identity is separated finite type but a_Y is not separated, so the displayed Ra_Y^! is outside the declared operation domain. The retained statement corrects this by specifying separated finite-type X,Y, consistently with the sibling thm-sf-verdier-exchange and the structure-morphism intent. The previous maintainer review and correction metadata are preserved; this continuation introduces no further statement change. All coefficient and compatibility clauses remain.

## Sources and searches

Read the main-20261015 `_section.md` and `sk-thm-sf-verdier-exchange.proof.md`, the unit and chapter records, and the sibling detailed thm-sf-verdier-exchange.md. The proof follows the blueprint's composition-mate then tensor–Hom route and is correctly marked agent-written. No SGA source is used. Read Stacks more-etale.tex, `lemma-shriek-composition` (0F7J), including its compatible compactification/open-proper interchange construction, and `remark-Rf-lower-shriek-change-of-rings` (0GL6). Neither source by itself claims every adic coherence statement; the exact coherent derived-system obligations below are cited as existing DAG statements, with their stronger scope distinguished from the foundational sources.

Searched all DAG chapters with blueprint_refs for Verdier-duality exchange, compact-support composition, coefficient composition and cofinality, and read all matching relevant statements. The finite quotient node lem-sf-compact-coefficient-composition alone does not handle field extension. The existing lem-sp-et-proet-coefficient-compatibility states precisely the composition square for arbitrary finite coefficient maps, so no new node is created. The existing lem-sf-integral-compactification-system-realization states the actual system/integral compatibility for nested compact supports and compositors. The current lem-sf-constructible-exceptional-adjunction-coefficients states exactness, finite-Tor preservation, adjunctions and counit-normalized coefficient maps at every required stage.

The msearch continuation queried LeanFinder about coefficient change of compact-support compositors, LeanSearch with a second phrasing, Loogle twice, and Mathlib grep twice. Hits concerned ordinary underived sheaf pushforward composition and algebraic base change, not derived compact support. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean lines 120–160: pushforwardComp at line 139 is Iso.refl for ordinary sheaf pushforward; it supplies neither compactification interchange nor derived completion. The first Loogle query reported an unknown NatIso identifier; the second found the ordinary sheaf declarations. All actual outputs were read. No search is fabricated. No new node needs a new absence verdict.

## Review by Q84

I checked B–E against the actual statements, rather than only the imported dependency list. The separated-scheme typing repair is needed as above. The coefficient ring unit has Tor interval [0,0], and its integral/field versions use the retained coefficient conventions. Step 1 uses only sk-def-sf-setting and the explicitly specified constructible functor of sk-def-sf-operations(vi), so omega_Y is an admissible tensor–Hom input. It never uses an unrestricted ambient pro-etale exceptional adjoint.

Step 2 now cites lem-sf-constructible-exceptional-adjunction-coefficients, whose statement actually gives F_h adjoint to G_h, exactness and preservation on the finite-Tor categories at all four stages. The old definition-only appeal risked C4. thm-sf-comp-composition gives alpha at finite coefficients; fix-lem-exchanges(2),(4) explicitly includes its completed/transported forms. mate-pasting(2) gives the composite counit, and def-weil-pbc-adjunction-conjugate explicitly says conjugation preserves isomorphisms. I checked the Hom-chain direction h maps to h composed with alpha inverse, so c is G_f G_a -> G_x. X,Y,s satisfy separatedness and finite type. Evaluating at the unit proves the first clause.

Step 3 uses sk-thm-sf-tensor-hom with N=omega_Y. Its statement has exactly the displayed internal-Hom exchange in D^+, in the opposite direction to epsilon; taking its inverse is essential. sk-def-sf-operations defines the bifunctor used for postcomposition by c. Thus the second arrow is a functor applied to an isomorphism. Step 4 uses the exchange theorem's stated naturality and shift compatibility and ordinary bifunctoriality. The contravariant square and [-r] sign are written explicitly, rather than treating the dual as covariant.

Step 5 uses the adjunction-coefficient theorem's actual q,b counit equation and lem-sp-et-proet-coefficient-compatibility's actual geometric composition square. That node allows any homomorphism of finite ell-primary rings, so it handles finite-free ramified extensions as well as nonflat quotients. It states the square on both sites, under the canonical comparison. No node is cited merely for a construction hidden in its proof. The map q_af has the correct order F_a q_f after q_a F_f. All its arguments, including G_f G_a L, remain finite-Tor by step 2.

Step 6 is the routine counit-transpose calculation using mate-pasting(2),(3), with both transposes written out. The left transpose uses q_x inverse; the composition square rewrites C(alpha inverse) q_x inverse to q_af inverse alpha_B inverse. On the right the f counit is eliminated first, then the a counit, by the equations in step 5. Both resulting maps have the same source and target. This proves the claimed equality, without assuming that an arbitrary mate of an isomorphism is invertible: only conjugation of isomorphic left adjoints is used in step 2.

Step 7 uses actual coherent section units/counits from lem-coef-cartesian-section-adjoint-mates, whose hypotheses are supplied by the finite-comparison theorem and semilinear section models, and then the stated integral realization of nested compact supports and their canonical transformations. This replaces the retained inline subsequence/K-injective argument, which was a hidden independent lemma. The adjunction-coefficient theorem states the integral-reduction/scalar comparisons and their counit normalization, so no equality of integral maps is inferred from equal finite evaluations. The entire equality is a coherent section identity before realization. Uniform bounds and normalized inputs are those of the exact constructible functors and coefficient categories; all intermediate F/G applications stay in that domain. Ramification uses levels en, never an incorrect unramified identification. The integral and field transports use the named canonical operations and no duality or biduality formula.

Step 8 evaluates the coefficient equation at the unit, applies naturality of internal-Hom/direct-image comparisons, and pastes it with the coefficient square explicitly asserted by tensor–Hom. It asserts only commutativity on the stated comparison domains; no invertibility on arbitrary ambient inputs is added. At field coefficients reduction refers to an integral representative, as the cited theorem explicitly says.

I read all statements named by the final eight steps; citations.json contains verbatim statement text for each use, allowing the reader to locate the displayed clauses. New dependencies are generic operation/coherence tools and are declared only under split_report.tool_uses; the maintainer-owned tool_uses and reviewed records are left unchanged. The extra tools expand the blueprint's final compatibility sentence and do not replace its proof route. Searches found no missing statement that requires a new node; no new statement-only lemma, duplicate, or restatement of the item was added.

Small cases checked: f=id makes alpha and c identities and recovers the inverse tensor–Hom map; M=0 gives zero-to-zero; empty X gives the same, and empty Y forces empty X. A one-point scheme gives ordinary module tensor–Hom. Quotient m=n and identity field extension give identity comparisons. A ramified extension uses A_{E',en} with e>=1, not A_{E',n}. The statements do not assume the nonflat quotient is flat. Shifting M by r changes the dual by -r. The doubled-origin case is excluded exactly by the necessary structure-map typing correction. No new false statement is introduced and no conclusion is weakened further.

The old 6403-character compatibility step has been replaced with four explicit steps, using existing statements for its independent geometric and realization facts. Every final step is shorter than 2000 characters; step 6 is a single counit calculation, not an unnamed geometric lemma. I also inspected its contents, not just its length. There are no unresolved mathematical tasks within this one-level split; the cited unsplit lemmas remain future DAG work.

## Not duplicates

No new nodes. The finite-coefficient composition fact is reused from lem-sp-et-proet-coefficient-compatibility, and the adjunction/coefficient and realization facts from their existing nodes.

## Validation

The required dry run and final delivery are recorded by deliver.py. No Lean file was written or compiled, no Lake or build tool was invoked, and no live project or launcher was modified.
