# Worker report: Q144 repair

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-normalized-orientation-perfect-duality.json`: statement unchanged; the returned nine-step, 7934-character proof is replaced by a 2335-character assembly.
- `dag/nodes/sec-six-functors/lem-sf-normalized-integral-purity-trace.json`: statement, unsplit; 2522 characters; the specified coherent integral purity component on the entire integral domain, its inverse, its counit trace, and their actual reduction equations; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-sf-normalized-field-purity-trace.json`: statement, unsplit; 2820 characters; the specified rational/common-stage purity component, its inverse, its counit trace, and their actual coefficient equations; no Mathlib match.
- `citations.json`: one verbatim statement extract for each use in each parent proof step.

## Attachments

None. I searched the live project under `lean/WeilConjectures/` by the exact blueprint tag and by normalized orientation, coefficient Frobenius, purity, trace, and perfect duality. The existing finite-stage orientation/dual-perfect declarations do not state the whole item, including the specified integral/field family and its traces. The upstream `Orientation.lean` explicitly describes its scope as finite coefficients. Its formal perfect-duality results are represented by the already cited DAG nodes, not new copies here. No Lean or compiler was run.

## WANTED

None. This is an agent-written assembly from the current blueprint and existing DAG statements; no additional external theorem or source was introduced.

## Return repaired

The sandbox was empty apart from dispatcher markers: there was no previous item, report, citation file or search log to overwrite. I copied the returned item from the read-only current repository, including its previous review fixes, metadata and search records. Its current statement and nine proof steps are the ones described in the return. The immutable statement was kept byte-for-byte as a JSON string. No repository git command or write was used.

The return asks for at least two separate statement-only tasks, comparable in size, and at most 3000 characters in the parent proof. The two tasks have 2522 and 2820 characters, have no proof steps, no proof dependencies and no proof origin, and retain the actual maps, domains and equations that require implementation. The integral task includes the nontrivial admission from bounded residue cohomology to a single Tor interval, the identification with the specified coherent family rather than an arbitrary lift, and the integral counit square. The field task includes rationalization, enlargement of a finite coefficient field, the integral family associators/cocycle, common-stage passage, and the rational exceptional counit square. Neither includes independent point or smooth perfect biduality, so neither restates the whole item.

All nine old arguments are copied verbatim below, with their intended destinations. Old steps 1 and 2 are the finite input and elementary inverse calculation of the integral task, and remain a short direct finite-level application in the parent. Old step 3 is the integral task. Old step 4 is the field task. Old steps 5 and 6 are partitioned by coefficient domain between the two tasks: each task states both the trace formula and its actual coefficient equation. Old steps 7--9 apply existing statements (`lem-weil-coefficient-frobenius`, `sk-def-perfect`, `sk-thm-sf-dual-perfect`) whose public conclusions already carry exactly this work; they remain explicit applications in the assembly. Creating another point-duality or smooth-perfect-duality node would duplicate those statements. Their complete arguments, including the distinction between ordinary and derived DVR duality, the actual structure morphism, and identification of the evaluation map, are retained below. Thus this repair does not discard an argument to meet the size limit.

## Sources and searches

I read `GOAL.md`, the three levels in `SETUP.md`, the chapter `sec-six-functors`, the unit `sk-thm-sf-package`, `stages/1-dag.md`, `coord/brief-stage1.md`, and delivery-errors B--E. The route source is main-20261015 `sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md`: clause (6) names finite purity, integral reconstruction and rational purity; the point/site-perfect sentence of (7) names coefficient Frobenius and relative perfect duality. I also read the current-snapshot proof files `sec-smooth-purity/sk-thm-purity-transport/thm-pur-adic-reconstruction.proof.md`, `thm-pur-rational-and-qbar-purity.proof.md`, `sec-six-functors/sk-thm-sf-dual-perfect/thm-sf-dual-perfect.proof.md`, and `sec-six-functors-basics/sk-prop-sf-biduality-general/lem-weil-coefficient-frobenius.proof.md`. They support, respectively, normalized reconstruction, lattice/common-stage passage, evaluation-compatible perfect duality, and the ordinary/derived coefficient distinction. I did not use an SGA source or change the finite purity route; finite purity continues through its existing diagonal/deformation theorem.

Before creating either node, I searched the whole DAG and the whole imported blueprint with `tools/blueprint_refs.py search` for coherent purity, trace counit, purity rational trace, purity integral trace, and purity counit coefficient. I searched node text by normalized purity, inverse purity, realization and coefficient trace; I opened every close candidate listed under Not duplicates. The two new ids did not exist. The blueprint ancestor command gives `prop-functor-package`; both new nodes have that ancestor and `[lem-sf-package-normalized-orientation-perfect-duality]` as their via chain, with the exact clause (6) place. No exact blueprint duplicate was found.

All searches were run through the required `msearch.py` and read as returned. Each new node records four executed searches: LeanFinder, Loogle, LeanSearch, and Mathlib grep. The natural-language tools give two different phrasings. Integral hits concern ordinary ring traces, adic completion and condensed counits; none is a smooth purity theorem or its oriented exceptional trace. Field hits concern smooth ring maps, field traces and comma-category equivalence counits; none gives the specified lattice/common-stage exceptional operations. Loogle purity hits are compiler purity, unrelated to geometric purity; the counit/map hits are comma functor identities. Mathlib grep gives either no hit or monadic-adjunction substrings, not adic purity. Additional whole-item searches return ordinary perfect pairings, compiler purity or smooth commutative algebra, not the whole item. Services answered normally; no unsuccessful service was recorded as a no-match. The detailed queries and returned digests remain in `searches.jsonl`, and each new node's `mathlib_searches` uses the exact tool and query text.

## Not duplicates

lem-sf-normalized-integral-purity-trace vs thm-pur-adic-reconstruction: reconstruction is for the uniform finite-Tor integral domain and asserts a coherent lift with specified finite reductions, without a chosen simultaneous scalar-natural family or its counit trace; the new task admits all stated integral objects and identifies the inverse orientation and trace of that specific family with the actual operation comparisons.
lem-sf-normalized-integral-purity-trace vs lem-pur-adic-purity-scalar-naturality: the latter gives an integral natural family and its scalar-extension squares on the integral finite-Tor domain; the new task supplies the residue-Tor admission, finite-quotient inverse squares and the actual compact-support/counit trace reduction equation.
lem-sf-normalized-integral-purity-trace vs prop-pur-adic-reconstruction-trace-coherence: that node asserts transport of the trace and geometric coherences in the reconstruction setting; the new task fixes the particular simultaneous scalar-natural component on all of D^b_c, its inverse and the fully typed comparison with the actual integral exceptional adjoint and counit. It is the joint normalization interface, not another assertion of trace transport alone.
lem-sf-normalized-integral-purity-trace vs prop-coef-integral-exceptional-adjoint: this supplies the actual integral adjoint and its reduced counits; it does not assert smooth purity or identify the normalized purity component and its inverse/trace.
lem-sf-normalized-field-purity-trace vs thm-pur-rational-and-qbar-purity: that node proves the forward purity isomorphism for a lattice presentation; the new task also fixes the same simultaneous scalar-natural family in every comparison and states the actual inverse and exceptional-counit trace squares, with identities and triple-extension cocycles.
lem-sf-normalized-field-purity-trace vs prop-pur-rational-purity-trace-coherence: that node asserts compatibility of purity with trace and geometric composition/base-change; the new task is the joint specified-map coefficient interface, including the exact inverse square, support comparison, rational exceptional counit, and common-stage equations. It does not reprove the geometric composition or base-change coherences.
lem-sf-normalized-field-purity-trace vs prop-pur-rational-purity-transitivity-summands: the latter asserts coefficient transitivity and summand preservation of forward purity; the new task concerns the same family together with its inverse and actual trace/counit comparisons on the specified presentations.
lem-sf-normalized-field-purity-trace vs lem-coef-rational-operations: this gives operation identifications and evaluation/unit/counit preservation, but not normalized smooth purity and the resulting inverse/trace equations.
lem-sf-normalized-integral-purity-trace vs sk-thm-purity-transport: that theorem is typed in the condensed coefficient conventions and asserts the broad normalized smooth adjunction; this task fixes the actual completed-sheaf natural family and its strict integral/finite comparison equations on the package's domains. I did not replace the actual operation constructions with the condensed convention theorem.
lem-sf-normalized-field-purity-trace vs sk-thm-purity-transport: the new task states the actual localized/common-stage comparison of chosen maps for completed-sheaf coefficient presentations, rather than importing the condensed-category adjunction and its asserted uniqueness.
lem-sf-normalized-integral-purity-trace vs cor-pur-adic-and-rational-smooth-dualizing-complexes: the corollary is for the coefficient unit and structure morphism; this task treats arbitrary objects and arbitrary smooth morphisms with the actual finite-reduction trace square.
lem-sf-normalized-field-purity-trace vs cor-pur-adic-and-rational-smooth-dualizing-complexes: the corollary identifies an absolute smooth dualizing object; this task treats arbitrary field-stage objects and relative smooth morphisms with explicit scalar/common-stage trace equations.
lem-sf-normalized-integral-purity-trace vs det-sp-trace-basic: that theorem describes a transported smooth adjunction, affine-space normalization and finite-etale summation; it does not fix the simultaneous varpi-adic natural-family component and the package's actual finite reduction comparison equation.
lem-sf-normalized-field-purity-trace vs det-sp-trace-basic: that theorem describes smooth trace and its geometric normalizations; this task supplies the coefficient-specific actual inverse/trace equations for the prescribed finite-field presentations.

## Review by Q144

I checked the item statement against clause (6) and the independent point/site-perfect sentence of (7), without changing a hypothesis or conclusion. For the new integral task I checked the reconstruction source and the statements of `lem-coef-integral-residue-tor`, `thm-pur-adic-reconstruction`, `lem-pur-adic-purity-scalar-naturality`, `prop-coef-integral-exceptional-adjoint`, `lem-coef-finite-exceptional`, `lem-fix-operation-reduction` and finite reduction of purity. The residue-Tor theorem really gives a common interval from residue cohomological boundedness. Reconstruction does not give uniqueness: I kept its chosen scalar-natural component explicitly and do not infer equality of integral maps merely from their reductions. The exceptional-adjoint node explicitly says that its actual units/counits reduce to the finite ones; the new task's trace equation uses that counit, not an arbitrary adjunction.

For the field task I checked the rational purity proof, the scalar-natural-family statement including tensor associators and the triple-field cocycle, and `lem-coef-rational-operations` and `lem-fix-operation-reduction`. The rational operations statement explicitly preserves the counits, including under finite scalar extension; this is precisely what the trace square requires. The statement has only the specified lattice/common-stage domains and never applies field-to-finite reduction. The displayed trace equality has source C_Y P H L, and both sides end in C_Y L. Its factor c_HL lands in P' C_X H L, then P'(a_L) lands in P'H'C_Y L, and the last trace lands in C_Y L. The inverse equality has source C_X G L and ends in H'C_Y L. All indices and domains therefore agree.

Parent step 1 uses the exact finite purity statement and the finite reduction theorem, whose statement includes smooth traces. The trace definition explicitly uses Rf_!(gamma), never Rf_!(gamma inverse). The inverse equation is elementary composition with the two inverses. Parent step 2 uses exactly the three comparison equations and domain assertions in the two new statements, rather than their unwritten proofs. Parent step 3 uses `lem-weil-coefficient-frobenius`'s separate finite, DVR and field clauses, with the canonical evaluation defined in `def-sf-coefficient-duality`. The countercheck R/(varpi) rules out ordinary DVR reflexivity. Parent step 4 applies the arbitrary-base relative statement `sk-thm-sf-dual-perfect`, which explicitly identifies the evaluation-defined double dual, not merely the dual objects. `sk-def-perfect` supplies the site-perfect/dualizable bridge; `def-weil-site-perfect-complex` has precisely the local finite-projective meaning used. `def-fix-six-functor-datum` defines omega from the structure morphism; the twist definition supplies the actual coefficient units at all stages. The integral residue-Tor assertion ensures the required integral finite-Tor domain. Taking a_T does not require descent of T to a finite field or geometric connectedness. I opened every cited node's statement and copied the relevant text to citations.json.

Small cases checked: n=1 and n=m give the residue-field and identity comparison; f=id has r=0 and the equations reduce to the adjunction identities; zero complexes and empty schemes cause no exception; d=0 cancels the trivial twist/shift; E=F gives the identity scalar equation, and E subset F subset L respects tensor associators. At a point, A_n-torsion modules and R/(varpi) test the essential finite-versus-integral distinction. No assertion identifies finite Tor amplitude on a scheme with site-perfectness. These checks revealed no statement dispute.

The two new nodes contain statements only, with every object introduced, one TeX escaping level, exact blueprint provenance and real searches. They share no Stacks tag requiring an additional same-tag comparison. The old direct theorem applications for point/site-perfect duality are reused because they already have nodes; no elementary inverse-algebra lemma or duplicate smooth-perfect theorem was added. The substantive correction is the two independently claimable coefficient-domain tasks and a short assembly. Each parent step is below 2000 characters; the longest is the direct relative perfect-duality application, which does not hide a new comparison lemma. All nine original texts are preserved next so the maintainer can audit loss of content.

## Complete retained arguments and work allocation

The following is the original text, not proof steps in either new node. Future workers receive statement-only nodes; these argument notes preserve the returned proof and the repair's intended division.

### Original step 1

Allocation: Integral task: finite-purity input; parent step 1 also gives this direct finite case.

At a finite stage apply [thm-pur-finite-coefficient-smooth-purity] to $f$ and $L$. Its coefficient ring is exactly $A_n$, its schemes are separated finite type over the fixed $k$, and its smoothness, pure relative dimension and finite-Tor hypotheses are exactly ours. Thus the specified $\gamma_{f,L}:f^*L(r)[2r]\to Rf^!L$ is an isomorphism. Define the displayed inverse-direction comparison to be $\gamma_{f,L}^{-1}$; both inverse identities follow from the isomorphism identities. This retains the diagonal/deformation normalization of that theorem.

Cited statements: `thm-pur-finite-coefficient-smooth-purity`.

### Original step 2

Allocation: Integral task: finite-reduction compatibility and inverse algebra; parent step 1 also uses this finite case.

For $n\ge m\ge1$, [thm-pur-finite-reduction-of-purity] says precisely that the square comparing the reduction of $\gamma_{f,L}$ with $\gamma_{f,L\otimes^L_{A_n}A_m}$ commutes, on the finite-Tor domains. Its statement also includes the smooth traces. Inverting the two horizontal isomorphisms gives the corresponding square for the inverse-direction comparison: from $b\,C(\gamma)=\gamma^\prime a$ one obtains $a\,C(\gamma^{-1})=(\gamma^\prime)^{-1}b$. This uses only composition with the inverses, not a new choice of orientation.

Cited statements: `thm-pur-finite-reduction-of-purity`.

### Original step 3

Allocation: Integral task: full-domain admission and identification of the specified coherent component.

At integral coefficients a stated object $L\in D^b_c(Y,R)$ lies in $D^b_{ctf}(Y,R)$ by [lem-coef-integral-residue-tor]: choose a cohomological interval for its bounded residue reduction, and the lemma supplies that same Tor interval for every finite reduction. Apply [thm-pur-adic-reconstruction] to $L$. It gives a coherent strict-tower realization of the compatible finite purity family and an isomorphism $\gamma_{f,L}$ whose reduction is exactly $\gamma_{f,L_n}$ for each $n$. We use the specified normalized realization, as required in the item; we do not assert uniqueness of a lift from its components. Concretely, the specified realization is the component $\gamma_{E,L}$ of the simultaneous normalized family of [lem-pur-adic-purity-scalar-naturality]: it is an isomorphism whose finite reductions are exactly the $\gamma_{f,L_n}$ of [thm-pur-adic-reconstruction], so it is such a realization, and Steps 3, 4 and 6 concern one and the same integral map. Its inverse is the integral comparison, with the reduction squares proved by the inverse calculation in Step 2.

Cited statements: `lem-coef-integral-residue-tor`, `thm-pur-adic-reconstruction`, `lem-pur-adic-purity-scalar-naturality`.

### Original step 4

Allocation: Field task: rationalization and simultaneous common-stage comparison.

For the specified integral lattice representing a field-stage object, [thm-pur-rational-and-qbar-purity] carries integral purity to an isomorphism at $E$ and then to the common finite-field presentation of the algebraically closed coefficient category. To track the choice when the coefficient field is enlarged, use the simultaneous normalized natural family of [lem-pur-adic-purity-scalar-naturality]. With its notation the square is $b\,C(\gamma_E)=\gamma_F a$, including the tensor associators, identities and triple-extension cocycle. The lattice and normalized purity system in the statement are this specified family. Functorial passage to rationalization and a common stage preserves the equation and the inverse identities. Consequently $a\,C(\gamma_E^{-1})=\gamma_F^{-1}b$ at those stages as well. No reduction functor from a field to $A_n$ is used.

Cited statements: `thm-pur-rational-and-qbar-purity`, `lem-pur-adic-purity-scalar-naturality`.

### Original step 5

Allocation: Both new tasks: the trace formula with the forward purity map, split by coefficient domain.

The coefficient-valued smooth trace is, by [def-pur-smooth-trace], $t_L=\epsilon_L\circ Rf_!(\gamma_{f,L})$. At higher coefficients define its normalized transport by the same composite using the specified purity isomorphism and exceptional counit. This has source $Rf_!(f^*L(r)[2r])$ and target $L$, exactly as at finite level. In particular reading purity in its inverse direction does not replace $Rf_!(\gamma_{f,L})$ by $Rf_!(\gamma_{f,L}^{-1})$ in the trace formula.

Cited statements: `def-pur-smooth-trace`.

### Original step 6

Allocation: Both new tasks: use integral/finite counit comparisons for the integral task and rational/finite-field counit comparisons for the field task. The whole calculation is retained here.

Here is the trace comparison calculation, including the counit. For any of the specified coefficient functors $C$, put $H(L)=f^*L(r)[2r]$, $G(L)=Rf^!L$, $P=Rf_!$, and write $a:CH\cong H^\prime C$, $b:CG\cong G^\prime C$, $c:CP\cong P^\prime C$. Purity compatibility gives $b_LC(\gamma_L)=\gamma^\prime_{CL}a_L$. Naturality of $c$ and counit compatibility then give
$$\begin{aligned} C(t_L)&=C(\epsilon_L)\,CP(\gamma_L)\\ &=\epsilon^\prime_{CL}\,P^\prime(b_L)\,c_{GL}\,CP(\gamma_L)\\ &=\epsilon^\prime_{CL}\,P^\prime(b_LC(\gamma_L))\,c_{HL}\\ &=t^\prime_{CL}\,P^\prime(a_L)\,c_{HL}.\end{aligned}$$
The counit equation used here is stated explicitly for finite quotients in [lem-coef-finite-exceptional], for integral reduction in [prop-coef-integral-exceptional-adjoint], and for rationalization and finite coefficient-field extension in [lem-coef-rational-operations]. The comparisons for $P$, pullback, twist and tensor and their naturality are those of [lem-fix-operation-reduction]. Together with Steps 2--4, this proves exactly the claimed trace squares. The equation passes to a common field stage because each arrow is represented there.

Cited statements: `lem-coef-finite-exceptional`, `prop-coef-integral-exceptional-adjoint`, `lem-coef-rational-operations`, `lem-fix-operation-reduction`.

### Original step 7

Allocation: Existing coefficient-Frobenius statement, applied in parent step 3; do not duplicate it.

For point coefficients apply [lem-weil-coefficient-frobenius], using the canonical coefficient evaluation of [def-sf-coefficient-duality]. At $A_n$, the ring is self-injective and the ordinary finite-module evaluation is invertible; the same node states derived biduality on bounded complexes with finite cohomology. At $R$, use its different assertion that every bounded finite-cohomology complex is perfect and that derived $R$-Hom evaluation is invertible. At $E$ and at a common finite field stage, the field assertion gives bounded finite-dimensional biduality. Thus the dualizing object in each assertion is the coefficient ring itself. In particular the $R$ assertion is not ordinary module reflexivity: the module $R/(\varpi)$ has zero ordinary dual but has the asserted derived biduality.

Cited statements: `lem-weil-coefficient-frobenius`, `def-sf-coefficient-duality`.

### Original step 8

Allocation: Parent step 4: structure-morphism specialization of the finite case and two new tasks, using the existing operation/unit definitions.

Let $T/k$ be as stated and set $a=a_T$. This is a smooth separated finite-type morphism of pure relative dimension $d$. Apply Steps 1--4 to $a$ and the coefficient unit. The unit-pullback identification yields $\gamma_{a,\Lambda}:\Lambda_T(d)[2d]\xrightarrow{\sim}\omega_T=Ra^!\Lambda$; take its inverse $\eta_T$. Put $J=\Lambda_T(d)[2d]$, $H=R\mathcal Hom$ and $M^\vee=H(M,\Lambda_T)$. These are exactly the operations of [def-fix-six-functor-datum] and the units, twists and coefficient presentations of [def-coefficient-twists-detailed], with the site-perfect hypothesis interpreted by [def-weil-site-perfect-complex]. The construction uses the structure morphism of $T$ itself; no model over a finite field or geometric connectedness assumption on $T$ is imposed.

Cited statements: `def-fix-six-functor-datum`, `def-coefficient-twists-detailed`, `def-weil-site-perfect-complex`.

### Original step 9

Allocation: Existing relative perfect-duality and perfectness statements, applied in parent step 4; do not duplicate their public evaluation-identification conclusion.

By [sk-def-perfect], an object of $D(T_{\mathrm{proet}},\Lambda)$ is perfect over $\Lambda_T$ (dualizable for $\otimes^L_{\Lambda_T}$) if and only if it is locally quasi-isomorphic to a bounded complex of finite projective $\Lambda_T$-modules; so the site-perfect $M\in\mathcal C_{T,\Lambda}$ (in $D^b_{ctf}$ at every stage, at $R$ by Step 3's [lem-coef-integral-residue-tor]) satisfies the perfectness hypothesis of the next citation. The isomorphism $\gamma_{a,\Lambda}$ of Step 8 is the smooth-purity orientation which that statement names. Apply the relative perfect-duality statement [sk-thm-sf-dual-perfect] with $f=a_T$, $K=M$, the orientation just obtained, and $Y=\operatorname{Spec}k$. This is its arbitrary-base relative form. It gives the specific composite
$$D_TM=H(M,\omega_T)\xrightarrow{H(M,\eta_T)}H(M,J)\xrightarrow{\sim}M^\vee(d)[2d],$$
and it identifies the evaluation-defined map $M\to D_TD_TM$, under the resulting double-dual comparison, with the coefficient evaluation $M\to M^{\vee\vee}$, an isomorphism for site-perfect $M$. This identification is part of the cited statement, not inferred from the mere existence of an object isomorphism. The relative theorem is the formal orientation/perfect-complex calculation: it uses the tensor--Hom adjunction, invertible Tate twist and perfect dual pair, not axiom (A6) of an axiomatized datum or general geometric biduality. Its statement allows an arbitrary base of the setting, so no hypothesis on $T$ beyond smoothness and pure dimension is needed. The coefficient categories here have exactly its completed, localized and common-stage meanings, so this proves the requested special case on each stated domain without changing site-perfectness into finite Tor amplitude.

Cited statements: `sk-thm-sf-dual-perfect`, `sk-def-perfect`.

## Unfinished work

The two new nodes deliberately have status unsplit, with their proofs left for separate workers as requested. No Lean work was authorized or attempted. Server validation and delivery are recorded by the required tools.

## Validation

The first local citation check rejected an operation-datum extract shorter than 40 characters. It has been replaced by the full verbatim dualizing-object paragraph. The server preflight subsequently passed on the same mathematical node contents; the final dry run validates the expanded supporting quotation before push.
