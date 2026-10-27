# Q95 repair report

## Files written

- lem-pur-shifted-tate-unit-scalar-coherence: existing statement, unchanged; repaired split and four-step assembly.
- lem-pur-tate-unit-flat-model-domains: statement, unsplit; no Mathlib match.
- lem-pur-unshifted-line-unit-tower: statement, unsplit; no Mathlib match.
- lem-pur-scalar-shift-line-tower-transport: statement, unsplit; no Mathlib match.

## Attachments

None. The complete item is not declared under WeilConjectures; Sheaf.Paper.PurShiftedTateUnitScalarCoherence ends its theorem in sorry (line 230). Upstream finite-coefficient Tate twist flatness uses a different coefficient category and states only part of the item.

## WANTED

None. This auxiliary argument is explicitly agent-written, as in the previous split; the blueprint states its coefficient-transport purpose rather than a numbered coherence theorem.

## What was wrong and what changed

The released stage-1 repair order (2026-10-22, keep_plan true) requires at least two comparable statement-only tasks and an assembly of at most 3000 characters. The sandbox initially had no node files or report, only dispatcher markers, so the current live returned node is the retained baseline. Its statement, statement dependencies, route, source, prior search records, blueprint history and Lean records were preserved. No statement dispute is needed. Three separate mathematical tasks replace the seven-step monolith. Each is unsplit with empty proof/proof_deps and null proof_origin. The full old argument is recorded below, not discarded or hidden in a new node's statement as a proof sketch.

## Not duplicates

lem-pur-tate-unit-flat-model-domains vs lem-weil-constant-coefficient-objects-constructible: the existing node gives the untwisted coefficient reductions and completeness, not actual K-flat Tate models and the shifted uniform Tor calculation.
lem-pur-tate-unit-flat-model-domains vs prop-weil-twist-preserves: preservation of intervals does not identify the coefficient-unit reduction models or the shift to [-n,-n].
lem-pur-tate-unit-flat-model-domains vs lem-pur-completed-unit-pullback-tower: that node supplies the untwisted unit and coherent geometric pullback, not shifted Tate models and scalar computation.
lem-pur-unshifted-line-unit-tower vs lem-weil-integral-twist-scalar-coherence: beta's naturality square has no multiplication maps u or their composite w=u(m) beta; the new task fixes these concrete unit and line coordinates and both multiplication equations.
lem-pur-unshifted-line-unit-tower vs lem-pur-completed-line-tensor-coherence: the general beta/evaluation tower does not assert the specialized multiplication maps on coefficient units or w.
lem-pur-unshifted-line-unit-tower vs lem-weil-integral-twist-base-change: b's module-sheaf tower equation supplies an input, not the normalized derived multiplication composites.
lem-pur-scalar-shift-line-tower-transport vs lem-weil-completed-scalar-chain-shift: the latter states chi's strict cone shift calculation, not the ordinary scalar associator shift square and transport of any coherent w tower.
lem-pur-scalar-shift-line-tower-transport vs lem-pur-coefficient-associator-shifts: the latter assumes counit-normalized coherent scalar shifts and only gives associator compatibility; the new task identifies the termwise tensor normalization, its actual chi comparison, and the resulting shifted object maps.
lem-pur-scalar-shift-line-tower-transport vs lem-weil-point-completed-scalar-shift: that node handles chi for one extension, not a tower of supplied line maps.

## Review by Q95

I read the returned item and its seven steps, the live repair note, both the chapter and unit records, the current purity-transport sketch, thm-pur-rational-and-qbar-purity and its proof, the current prop-weil-twist-preserves proof, and the integral rank-one construction in sk-def-sp-tate-twist-locally-free.proof.md. These provide the coefficient-transport route and local rank-one models; the detailed scalar equations are retained agent arguments, not falsely attributed as a verbatim source theorem. I also read every former cited statement and the possible duplicate statements listed above, and the Lean header/docstring and final sorry.

Assembly step 1 uses only the first new statement: it explicitly supplies identity K-flat resolutions, completeness, ctf membership, the canonical derived reductions, and uniform intervals. Its hypotheses hold because ell differs from p and S is finite type over k; m=d is nonnegative and n=2d is an integer. The new statement does not identify a containing Tor interval with nonempty cohomological support. This matters on the empty scheme. Its intended proof is precisely old Steps 1-3: tensor with the coefficient unit is identity; tensor with the Tate line is locally identity; use actual reductions of the constant object, twist preservation, and the signed cochain shift. The model and domain assertions form a task independent of the tower equations.

Assembly step 2 uses only the second new statement. I checked the formulas for u and w against the item and the exact beta chain formula in lem-weil-integral-twist-derived-scalar. Its ordinary associator has the same direction as the item's alpha. Both unit paths give iota20(x)iota21(b)c; the two line paths differ only by b20 versus b21(b10(-) tensor 1), the equation supplied by lem-weil-integral-twist-base-change. These comparisons assert equality of sheaf morphisms and derived morphisms, not the false assertion that all global tensor sections are global pure tensors. The future proof uses the tensor/sheafification universal properties. Repeated fields use multiplication and the natural completeness map, with no strict completed identity assumption.

Assembly step 3 applies the third statement to the actual K_i=U_i(d) and coherent w supplied by step 2. The hypothesis is the unshifted equation already obtained, not the shifted conclusion. I checked the types of the displayed s/alpha square: both maps start at C21 C10(K[n]) and end at (C20 K)[n]. Naturality of s for w10 then gives the q equation. The third node states the nontrivial model and completion-normalization part as a separate task: identity tensor components respect (-1)^n d, and the strict cone shift multiplies its second coordinate by (-1)^n. The zero coordinate of chi stays zero. No chain-level inverse to chi is needed. I checked this against both completed-scalar-chain-shift and point-completed-scalar-shift statements.

Assembly step 4 uses the exact isomorphism-closure clause of lem-weil-integral-ctf-triangulated, which I opened. T_E has the property by step 1 and q identifies AT_0 with it, so this is an elementary closure application. No scalar-preservation theorem with missing hypotheses is smuggled in.

Small cases: S empty gives zero objects and containing intervals, d=0 gives ordinary multiplication, n=0 gives unshifted maps, negative n in the generalized shift task moves degree zero to -n with the same signed cone formula, E0=E or E=F uses the stated unit comparisons, and ramified extensions require neither unramifiedness nor a uniformizer equality. General ring-module associativity in Mathlib does not prove these completed sheaf statements in one specialization: I read ModuleCat/ChangeOfRings.lean lines 984-1041. I read the general CommShift naturality/composition and termwise cochain shift construction; these require the specific shift compatibility which is part of the new task, so they are useful infrastructure, not a Mathlib match. All logged service responses were read; two semantic phrasings were used for each task. No Lean was written or compiled, no repository or launcher file changed, and no agents were started.

## Retained old arguments and exact work allocation

The following are copied verbatim from the returned live proof, with ownership of every argument. They are development guidance, not proof fields of the unsplit nodes.

### Old step 1 → lem-pur-tate-unit-flat-model-domains

Write $J_L=\mathcal O_L(d)$ for the unshifted Tate line. By prop-weil-twist-preserves, $J_L$ is locally free of rank one over $R_L$. Tensoring a complex with $R_L[0]$ is the identity, and tensoring with $J_L[0]$ is locally the identity; both therefore take acyclic complexes to acyclic complexes. By the definition of K-flatness, these degree-zero complexes, and their shifts, are K-flat with flat terms. The derived-change-of-rings computation thus uses these very complexes as their own resolutions. In particular all ordinary scalar comparisons below are represented by the displayed module maps, with no auxiliary choices. The specified natural comparison $\chi$ identifies this computation with the strict-tower functors on complete inputs; its finite-freeness assertion applies to every coefficient inclusion, including repeated fields.

### Old step 2 → lem-pur-tate-unit-flat-model-domains

For each $L$, clause 2 of lem-weil-constant-coefficient-objects-constructible gives derived completeness and bounded constructibility of $U_L$, with its actual derived reductions $(\mathcal O_L/\varpi_L^j)_S[0]$ for every $j\geq1$. Tensoring such a reduction with any module sheaf $M[0]$ is $M[0]$ by coefficient multiplication. Thus its Tor interval is $[0,0]$, independent of $j$, which is precisely the integral finite-Tor condition in def-weil-finite-tor-amplitude. No equality of cohomological support with $\{0\}$ is needed.

### Old step 3 → lem-pur-tate-unit-flat-model-domains

Apply prop-weil-twist-preserves to $U_L$ with twist $d$: $U_L(d)$ is derived complete and constructible, and its reductions retain Tor interval $[0,0]$. Closure under shifts in lem-weil-integral-ctf-triangulated gives $T_L=U_L(d)[2d]$ in the integral constructible finite-Tor category. More explicitly, reduction commutes with this canonical shift, and for each finite coefficient module $M$, the tensor of the reduced $T_L$ with $M[0]$ is the corresponding line-tensor module placed in degree $-2d$. The uniform interval is therefore $[-2d,-2d]$. This is a containing Tor interval also when $S$ is empty.

### Old step 4 → lem-pur-unshifted-line-unit-tower

On the degree-zero models of step 1, $u_{H/L}$ is multiplication $x\otimes b\mapsto\iota_{H/L}(x)b$, with inverse $b\mapsto1\otimes b$. The ordinary associator sends $(x\otimes b)\otimes c$ to $x\otimes\iota_{F/E}(b)c$. Consequently $u_F\alpha_{U_0}$ sends this tensor to $\iota_{F/E_0}(x)\iota_{F/E}(b)c$, and $vB(u_E)$ sends it to $\iota_{F/E}(\iota_{E/E_0}(x)b)c$, the same section since coefficient inclusions compose. Equality on pure tensors gives equality on tensor presheaves and hence their sheafifications and derived images. The resolving comparison is the canonical one from step 1, so this proves the equation for the specified $u$ maps.

### Old step 5 → lem-pur-unshifted-line-unit-tower

Let $b_{H/L}:J_L\otimes_{R_L}R_H\to J_H$ be the canonical twist-line base change of lem-weil-integral-twist-base-change. Put $w_{H/L}=u_{H/L}(d)\beta_{H/L,U_L}$ before shifting. The termwise formula in lem-weil-integral-twist-derived-scalar identifies this composite with $(x\otimes l)\otimes b\mapsto\iota_{H/L}(x)b\,b_{H/L}(l\otimes1)$, using the coefficient action $R_H\otimes J_H\cong J_H$. In the tower, $w_{F/E_0}\alpha_{U_0(d)}$ on $((x\otimes l)\otimes b)\otimes c$ has value $\iota_{F/E_0}(x)\iota_{F/E}(b)c\,b_{F/E_0}(l\otimes1)$. The successive path $w_{F/E}B(w_{E/E_0})$ has value $\iota_{F/E_0}(x)\iota_{F/E}(b)c\,b_{F/E}(b_{E/E_0}(l\otimes1)\otimes1)$. These are equal by the tower compatibility explicitly asserted for $b$. The same pure-tensor/sheafification argument proves equality of these unshifted maps. Each $w$ is an isomorphism since both its factors are.

### Old step 6 → lem-pur-scalar-shift-line-tower-transport

Take $n=2d$. On a complex $P$, termwise coefficient extension identifies $(P[n])^r\otimes R_H=P^{r+n}\otimes R_H=(P\otimes R_H)[n]^r$ by the identity on tensors, which also respects the differential $(-1)^n d_P\otimes1$. Thus the specified $s$ is exactly this comparison. For two extensions, applying these identity component maps twice and then $\alpha_P[n]$ gives $\alpha_{P[n]}$ followed by the direct shift comparison: both send $(z\otimes b)\otimes c$ to $z\otimes\iota_{F/E}(b)c$. The same component calculation commutes with each $w$. Shift the equality of step 5 using these identities. Its direct composite is $q_{F/E_0}\alpha_{T_0}$, and its successive composite is $q_{F/E}B(q_{E/E_0})$, by the defining formula for $q$. The equality is for the specified completed normalization as well: the chain-shift compatibility of the actual quotient-map comparison $\chi$ is precisely lem-weil-completed-scalar-chain-shift. No inverse to $\chi$ at chain level is used.

### Old step 7 → lem-pur-unshifted-line-unit-tower (identity multiplication), lem-pur-scalar-shift-line-tower-transport (identity shift), assembly step 4 (iso closure)

The composite defining $q_{H/L}$ is an isomorphism, so $AT_0\cong T_E$ by $q_{E/E_0}$. The isomorphism-closure in lem-weil-integral-ctf-triangulated and step 3 put $AT_0$ in the required category. For an identity coefficient extension, multiplication $x\otimes b\mapsto xb$ is the canonical coefficient unitor, $b_{L/L}$ is the tensor-power unitor (the zero twist is coefficient multiplication), and $s$ is the componentwise comparison of step 6. In the formulas of steps 4 and 5 replace the relevant inclusion by the identity; the same products and the same tensor-power maps result on both paths. Hence both equations include repeated fields. Under $\chi$ the identity functor is identified by the natural completeness map, as specified by lem-weil-finite-free-completed-scalar-comparison, rather than assumed strictly equal to its completion.

## Unfinished work

No unresolved repair issue. The three new nodes intentionally remain statement-only for independent workers. Required dry-run and delivery results are recorded after execution.
