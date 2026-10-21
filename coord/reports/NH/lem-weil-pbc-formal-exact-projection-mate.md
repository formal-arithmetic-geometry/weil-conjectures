## Worker report

1. Files written: the item JSON (statement unchanged; four assembly steps); lem-weil-pbc-tensor-arrow-mate-naturality-shifts.json (statement; no Mathlib match, unsplit); lem-weil-pbc-tensor-arrow-mate-right-unit.json (statement; no Mathlib match, unsplit). Both new files are in dag/nodes/sec-proper-base-change/.
2. Attachments: none. The project declaration CategoryTheory.formalExactProjectionMate, lean/Sheaf/CategoryTheory/FormalExactProjectionMate.lean:85, ends in sorry; its definitions are actual compositions but do not prove the theorem. Whole WeilConjectures notion/tag searches found no full attachment. ProjectionMapMonoidal.lean assumes monoidal categories and so cannot supply the weaker bifunctor result.
3. WANTED: none.
4. This is the deliberate re-split ordered on 2026-10-21, rather than a stale assignment. No statement dispute or change. No source, maintainer-owned field, unit, chapter or Lean file changed.
5. Nothing unfinished in this stage-1 delivery: the two extracted arguments intentionally remain statement-only for other workers.

## Review by NH

I read the chapter and sk-thm-properbasechange unit, the current main-20261015 perfect-projection-formula proof, Stacks sites-cohomology.tex lines 13654–13681, Tag 0B56 equation-projection-formula-map, and derived.tex exact-composition and adjoint-exactness passages (Tags 014Y and 0A8D). Stacks defines precisely the adjunct of pullback-tensor comparison followed by counit tensor identity. It does not supply these weaker abstract bifunctor lemmas verbatim: their source records explicitly identify the agent-written expansion. The blueprint first paragraph requires the actual unit normalization and shift/triangle compatibility.

The first new node abstracts the old naturality and two shift calculations to arbitrary c:LK→E. It introduces every functor, comparison and morphism, and states both beta and alpha equations. Its commuting-square hypothesis bc=c'La specializes to counit naturality with a=Re. Its assumptions on shifts include naturality in the fixed tensor input; that hypothesis is indispensable at c. The second node abstracts the two unit calculations, retaining both the pre-adjunction equality k beta=c L rho and the mate equality R(k) alpha=R(c) eta rho. It assumes only natural right-action isomorphisms and the given unit equation, not an unprovided monoidal structure. Neither node restates the whole item: neither proves exactness or constructs a triangle morphism; the first has no right-unit data, the second no shifts.

I checked each parent citation against its full statement. Step 1 uses the exact-composite node's displayed chi and distinguished image triangle, twice; integer comparisons are the same supplied composite formula at each [n]. Step 2 uses the first new node's two commuting-square naturality equations and all-integer shift equation; the adjunction node explicitly gives natural eta and epsilon, so counit naturality is available. Step 3 uses the triangle definition's three equations and writes the connecting square at the actual arrow w, using step 2 at n=1. Step 4 uses the second new node's mate equality and the adjunction node's triangle identities; all sources and targets are displayed. citations.json contains verbatim portions of every cited statement for each use. No non-elementary uncited theorem is hidden in these four steps. No step exceeds 2000 characters; the total assembly is below 3000 characters.

I checked identity adjunction and identity tensor comparison, c=id, arbitrary c, and identity commuting squares: the equations reduce to naturality of tensor or rho. For n=0 the supplied unit-shift comparison gives the identity square; for negative n the same assumed compatibility is used directly without induction. The zero-object cases in the triangulated application and a contractible distinguished triangle satisfy the displayed equations; no alpha is inverted. The right-unit equality for arbitrary c need not be rho_K: its R(c) eta_K factor is essential and only cancels at the counit. This prevents smuggling the parent normalization into a new hypothesis.

Mathlib searches were run with the mandated msearch command and their actual logged results retained. I read CommShift.lean's composition and whiskering instances and Monoidal/Functor.lean:988–1040. Generic CommShift rules do not construct beta's compatibility from an arbitrary bifunctor comparison. The monoidal identities require full monoidal and (op)lax structure absent here. Whole-DAG and whole-blueprint searches (counit tensor, tensor comparison, right-unit, right unitor, shift-compatible mate, adjoint mate) find ringed/derived projection results, monoidal mates, and generic adjoint conjugation, none of these arbitrary-arrow bifunctor statements. The closest existing statements were read in full: lem-sfb-adjunction-oplax-mate, lem-sfb-monoidal-adjunction-mates, lem-sfb-ringed-projection-first-shift, lem-sfb-ringed-projection-canonical-normalization, lem-sc-derived-monoidal-pullback-unital-shift, and all five old proof citations.

## Argument preservation

Old step 1 is new parent step 1 (composition and its actual comparisons); old steps 2–4 are the first new node, with c=epsilon, and parent step 2; old step 5 is parent step 3 verbatim in its mathematical content; old steps 6–7 are the second new node, with c=epsilon, and parent step 4. The following old calculations are retained exactly as the work assigned to the extracted nodes; these paragraphs are review evidence, not proof fields of the new unsplit nodes.

### Original step 1

Fix $E$. Write $T_E(Q)=E\otimes Q$ in $\mathcal D$ and $T_{RE}(P)=RE\otimes P$ in $\mathcal C$. These are additive exact functors with their supplied shifts. Thus $F_E=T_{RE}$ is exact. Apply [lem-weil-pbc-triangulated-functor-composite] first to $L$ followed by $T_E$, then to $H_E=T_E L$ followed by $R$: $H_E$ and $G_E=RH_E$ are exact. In particular, if $l,r,t^E$ denote the shift comparisons of $L,R,T_E$, respectively, then for every integer $n$ the induced comparisons are $s_{H_E,n,P}=t^E_{n,LP}\,T_E(l_{n,P})$ and $s_{G_E,n,P}=r_{n,H_EP}\,R(s_{H_E,n,P})$. The comparison of $F_E$ is the supplied one for $T_{RE}$. Exactness means precisely preservation of the triangles with connecting map given by these composites [def-weil-triangulated-category].

### Original step 2

The adjunction formulas and naturality in [lem-weil-pbc-adjunction-of-natural-bijection] identify $R(\beta)\eta$ with the adjunct of $\beta$. To check naturality explicitly, let $e:E\to E'$ and $p:P\to P'$, and put $f=R(e)\otimes p$ and $h=e\otimes L(p)$. Naturality of $\mu$ and the counit identity $e\varepsilon_E=\varepsilon_{E'}LR(e)$ give
$$h\beta_{E,P}=(e\varepsilon_E\otimes Lp)\mu_{RE,P}=(\varepsilon_{E'}\otimes1)\mu_{RE',P'}L(f)=\beta_{E',P'}L(f).$$
Consequently, by naturality of $\eta$,
$$R(h)\alpha_{E,P}=R(\beta_{E',P'})RL(f)\eta_{RE\otimes P}=R(\beta_{E',P'})\eta_{RE'\otimes P'}f=\alpha_{E',P'}f.$$
Taking either $e$ or $p$ to be an identity proves naturality in both variables.

### Original step 3

For fixed $E$, put $A_E=LF_E$ and $B_E(P)=LRE\otimes LP$. Let $a_{n,P},b_{n,P},h_{n,P}$ be their induced shift comparisons for $A_E,B_E,H_E$, respectively. The hypothesis on $\mu$ says
$$b_{n,P}\mu_{RE,P[n]}=(\mu_{RE,P})[n]a_{n,P}.$$
Put $q_P=\varepsilon_E\otimes1_{LP}:B_E(P)\to H_E(P)$. Naturality of the second-input tensor shift comparison in the fixed input, applied to the specific morphism $\varepsilon_E:LRE\to E$, and bifunctoriality with $l_{n,P}$ give
$$h_{n,P}q_{P[n]}=q_P[n]b_{n,P}.$$
Their composite $\beta_E=q\mu$ therefore satisfies
$$h_{n,P}\beta_{E,P[n]}=\beta_{E,P}[n]a_{n,P}.$$
This is composition and whiskering of shift-compatible transformations [lem-weil-pbc-commshift-nattrans-comp-whisker], applied to each chosen shift $[n]$; that lemma's calculation is for an arbitrary shift auto-equivalence, so applies also for $n=0$ and negative $n$.

### Original step 4

Keep $E,n$ fixed and abbreviate $f_{n,P}=s_{F_E,n,P}$, $g_{n,P}=s_{G_E,n,P}$. The composite shift of $A_E$ is $a_{n,P}=l_{n,F_EP}L(f_{n,P})$. Naturality of $\eta$ with respect to $f_{n,P}$ and the assumed shift compatibility of $\eta$ give
$$r_{n,A_EP}R(a_{n,P})\eta_{F_E(P[n])}=\eta_{F_EP}[n]f_{n,P}.$$
Indeed, factor $R(a)$ as $R(l_{n,F_EP})RL(f_{n,P})$, move $RL(f_{n,P})$ across $\eta$, and apply the unit shift equation at $F_EP$. Now the previous step, naturality of $r$ for $\beta_{E,P}:A_EP\to H_EP$, and this equality yield
$$\begin{aligned}
g_{n,P}\alpha_{E,P[n]}&=r_{n,H_EP}R(h_{n,P}\beta_{E,P[n]})\eta_{F_E(P[n])}\\
&=r_{n,H_EP}R(\beta_{E,P}[n])R(a_{n,P})\eta_{F_E(P[n])}\\
&=(R\beta_{E,P})[n]\eta_{F_EP}[n]f_{n,P}=\alpha_{E,P}[n]f_{n,P}.
\end{aligned}$$
Equivalently this is the whiskering by $F_E$ of $\eta$, followed by $R\beta_E$, using the composition/whiskering rules of [lem-weil-pbc-commshift-nattrans-comp-whisker].

### Original step 5

Let $P_1\to P_2\to P_3\xrightarrow{w}P_1[1]$ be distinguished. The two image triangles are distinguished by step 1. Naturality from step 2 supplies their first two squares. For the third square, naturality at the actual morphism $w:P_3\to P_1[1]$, followed by the shift identity of step 4 at $(n,P)=(1,P_1)$, gives
$$s_{G_E,1,P_1}G_E(w)\alpha_{E,P_3}=s_{G_E,1,P_1}\alpha_{E,P_1[1]}F_E(w)=\alpha_{E,P_1}[1]s_{F_E,1,P_1}F_E(w).$$
These are exactly the three equations defining a morphism of triangles in [def-weil-pbc-triangles-with-shift].

### Original step 6

Define $k_E=\rho_E(1_E\otimes u):E\otimes L\mathbf1_{\mathcal C}\to E$. Bifunctoriality, naturality of $\rho$ at $\varepsilon_E:LRE\to E$, and the assumed right-unit equation for $\mu$ at $M=RE$ give
$$\begin{aligned}
k_E\beta_{E,\mathbf1_{\mathcal C}}
&=\rho_E(\varepsilon_E\otimes u)\mu_{RE,\mathbf1_{\mathcal C}}\\
&=\varepsilon_E\rho_{LRE}(1_{LRE}\otimes u)\mu_{RE,\mathbf1_{\mathcal C}}\\
&=\varepsilon_E L(\rho_{RE}).
\end{aligned}$$
All three expressions have source $L(RE\otimes\mathbf1_{\mathcal C})$ and target $E$.

### Original step 7

Apply $R$ to step 6, substitute the definition of $\alpha$, and use naturality of $\eta$ at $\rho_{RE}:RE\otimes\mathbf1_{\mathcal C}\to RE$. The right triangle identity of the given adjunction [lem-weil-pbc-adjunction-of-natural-bijection] then gives
$$\begin{aligned}
R(k_E)\alpha_{E,\mathbf1_{\mathcal C}}
&=R(\varepsilon_E)RL(\rho_{RE})\eta_{RE\otimes\mathbf1_{\mathcal C}}\\
&=R(\varepsilon_E)\eta_{RE}\rho_{RE}=\rho_{RE}.
\end{aligned}$$
This is the specified right-unit equality, as an equality of morphisms $RE\otimes\mathbf1_{\mathcal C}\to RE$.

For the first extracted node, replace RE by K and epsilon_E by c throughout old steps 2–4; in old step 2 replace R(e) by a and e by b, using bc=c'La. The q-square follows from tensor-shift naturality at c. The beta shift equation is h beta=beta[n] a; factor a=l L(t), move RL(t) across eta, and use r R(l) eta_shift=eta[n] to obtain g alpha=alpha[n]t. This accounts for every comparison in the original calculation. For the second node replace RE by K and epsilon_E by c in old steps 6–7. Naturality of rho and the given mu unit equation give k beta=c L rho. Applying R and naturality of eta gives R(k)alpha=R(c)eta_K rho_K. The parent alone uses the counit triangle identity to simplify the last factor.

## Not duplicates

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-kun-constant-projection-morphism: the existing statement is Canonical constant-coefficient derived projection morphism. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-kun-projection-formula-map: the existing statement is The projection-formula morphism. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-pd-proetale-section-module-functors: the existing statement is Normalized tensor structures on existing pro-etale section-module functors. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-pd-section-derived-realization: the existing statement is Canonical derived section-module realization. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-pd-section-derived-tensor-data: the existing statement is Canonical derived section-module tensor data. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-pd-section-module-operations-data: the existing statement is Existing section-module operations and pure-tensor data. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-pur-system-tensor-mate-arrows: the existing statement is Canonical tensor and proper/open arrows for varying coefficient systems. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-sfb-module-projection-section-arrows: the existing statement is Canonical module projection mate and section comparisons. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-sfb-module-projection-section-composites: the existing statement is Unit-normalized forward section projection composite. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-sfb-module-projection-section-inverse: the existing statement is Conditional inverse section projection composite. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-sfb-module-section-projection-arrow: the existing statement is Canonical section projection arrow. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-sfb-proetale-projection-exchange-maps: the existing statement is Canonical projection and exchange maps on internal pro-etale modules. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-sp-finite-free-direct-image-data: the existing statement is Normalized scalar models and canonical coefficient comparison data. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-weil-pbc-four-arrows: the existing statement is Four finite-level arrows. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-weil-pbc-four-corners: the existing statement is Four finite-level corners. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs def-weil-pbc-projection-formula-map: the existing statement is Projection-formula map. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs det-cor-sf-direct-image-ctf-open-tor: the existing statement is Scalar projection formula and the Tor bound for an open immersion. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs det-prop-p1-adjunction-rational-triangle: the existing statement is Triangle identities for the rational projective line. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs det-thm-sf-pf-field-localizing: the existing statement is The proper projection formula on the rational localizing categories. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs det-thm-sfb-proper-base-change-rational: the existing statement is Proper direct image, base change and projection formula for $E$ and $\overline{\mathbf Q}_\ell$. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs fix-prop-projection-formula: the existing statement is Compact-support projection formula at all coefficient stages. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-asd-ordinary-finite-p1-adjunction: the existing statement is Ordinary etale projective-line adjunction with arbitrary finite invertible-exponent coefficients. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-asd-proper-finite-coefficient-extension: the existing statement is Canonical unbounded proper direct-image comparison for finite coefficient extension. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-asd-proper-finite-coefficient-extension-core: the existing statement is Unbounded proper coefficient comparison and restricted projection identity. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-cbc-rational-compact-support-coefficient-coherence: the existing statement is Coherent coefficient comparisons for rational compact-support exchange. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-coef-finite-adjunction-transition: the existing statement is Finite-level adjunction transition compatibility. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-fix-proetale-scalar-mate-normalization: the existing statement is Pro-etale scalar mate restricts to the specified projection arrow. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-fix-proper-etale-origin-scalar-isomorphism: the existing statement is Proper scalar comparison is invertible on bounded etale-origin inputs. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-kun-0f0f: the existing statement is Projection formula, integer coefficients. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-kun-0f12: the existing statement is Tensor product with a constant complex. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-kun-geometric-point-projection-comparison: the existing statement is Geometric-point projection morphism agrees with the constant-section projection morphism. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-kun-kunneth-map-agrees: the existing statement is Compatibility of the Kunneth map with Leray, proper base change and the projection formula. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-kun-kunneth-via-0f1n: the existing statement is Compatibility of the Kunneth map with the projection-formula variant. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-kun-proj-formula-natural: the existing statement is Naturality of the projection formula. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pd-module-ringed-topos-derived-comparison: the existing statement is Module-object and ringed-topos derived tensor comparison. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-per-field-exceptional-tensor: the existing statement is Exceptional tensor comparison for coefficients pulled from a field. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-per-noetherian-affine-line-unit: the existing statement is Ordinary finite-coefficient affine-line unit over a Noetherian base. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-per-regular-normal-crossings-constant-image: the existing statement is Constant etale direct image across a regular normal crossings boundary. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pod-frobenius-cup-transport: the existing statement is Finite-coefficient Frobenius transport commutes with mixed-support cup product. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-adic-projection-shift-coherence: the existing statement is Shift compatibility of the compact-support projection and trace transpose. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-compact-support-completed-projection-coherence: the existing statement is Completion coherence for the integral projection mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-compact-support-integral-coefficient-comparison: the existing statement is Integral compact support under finite free coefficient extension. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-etale-compact-scalar-coherence: the existing statement is Ordinary etale compact-support scalar compatibility with projection and composition. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-etale-exceptional-constant-tensor: the existing statement is Constant-coefficient tensor calculus for the finite etale exceptional adjoint. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-finite-projection-action-laws: the existing statement is Tensor-action and open-counit identities for finite-level projection maps. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-flag-local-comparison: the existing statement is Coordinate Gysin composition and the supported cup product. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-flag-localized-product: the existing statement is Forgetting a composite of subbundle divisor classes. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-ordinary-adjunction-scalar-compatibility: the existing statement is Scalar compatibility of the ordinary completed adjunction. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-projection-formula-coefficient-coherence: the existing statement is Unit and coefficient associativity of compact-support projection maps. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-projection-purity-agreement: the existing statement is Agreement with the affine-line route on affine space. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-system-clopen-tensor-compatibility: the existing statement is Proper/open tensor-mate interchange on varying-coefficient systems. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-system-compactification-pf-substitution: the existing statement is Refinement comparisons intertwine strict-system projection maps. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-system-level-projection-formula-coherence: the existing statement is Strict-system projection formula composition coherence. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-system-projection-tensor-associativity: the existing statement is Tensor-variable associativity of the specified system projection maps. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-pur-system-tensor-transpose-composition: the existing statement is Composition of the counit-defined tensor transposes on systems. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sf-cbc-constant-tower-direct-image-normalization: the existing statement is Constant strict towers and normalized derived direct image. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sf-constant-semilinear-generator-comparison: the existing statement is Scalar restriction identifies the single proper and open reduction generators. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sf-exceptional-product-direct-image-compatibility: the existing statement is Exceptional external product is compatible with immersion direct images. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sf-finite-exchange-projection-commshift: the existing statement is Finite geometric exchange and projection commute with shifts. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sf-kunneth-coherence: the existing statement is Coherence of the relative product. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-coefficient-push-filtered-legs: the existing statement is Flat coefficient push comparison from a bounded filtered module presentation. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-integral-quotient-direct-image-comparison: the existing statement is Unbounded quotient-scalar refinement of integral direct image. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-integral-quotient-projection-comparison: the existing statement is Reduction of the actual unbounded integral projection morphism. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-qlbar-direct-image-comparison: the existing statement is Algebraic-closure coefficient change commutes with bounded-below direct image. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-ringed-kunneth-factorizations: the existing statement is Two factorizations of the ringed-topos external product comparison. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-ringed-projection-canonical-normalization: the existing statement is Identity and composition normalization of ringed projection mates. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-ringed-projection-first-shift: the existing statement is The ringed projection mate commutes with shifts in its direct-image input. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-ringed-projection-section-specialization: the existing statement is Symmetry-ordered section specialization of the canonical projection mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-ringed-projection-tensor-associativity: the existing statement is Canonical tensor constraints and associativity for one projection mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-ringed-projection-tensor-composition: the existing statement is Tensor and composition coherence of ringed-topos projection maps. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-trace-base-change-first: the existing statement is Trace and base-change rearrangement before the first triangle. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-trace-base-change-second: the existing statement is Trace and base-change rearrangement before the second triangle. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sp-completion-mate-comparison: the existing statement is The strict quotient-tower exchange realizes the completed-adjunction mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sp-finite-free-direct-image-coherence: the existing statement is Coherent finite-free coefficient comparison for ambient derived direct image. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sp-finite-free-direct-image-columns: the existing statement is Finite-basis columns of the restricted canonical coefficient mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sp-p1-counit-scalar: the existing statement is Scalar compatibility of the actual projective-line adjunction counit. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-trf-external-comparison-triangles: the existing statement is Triangle compatibility of the external direct-image comparison. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-trf-support-product-base-change: the existing statement is Support-product comparison with base change along the other leg. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-boundary-proetale-projection-comparison: the existing statement is Proper compact-support and tensor comparisons identify etale and pro-etale projection maps. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-augmented-diagram-projection-mate: the existing statement is Projection mate for an augmented coefficient diagram before taking inverse limit. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-derived-adjunction-shift: the existing statement is Canonical derived ringed-topos adjunction is shift-compatible. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-finite-level-rectangle: the existing statement is Finite-level exchange rectangle. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-formal-exact-projection-mate: the existing item combines exactness, counit-specialized naturality/shifts, triangle morphisms and unit normalization; this new lemma isolates an arbitrary-arrow argument and requires no exactness.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing statement is Coefficient normalization of the raw ordered completed exchange. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-realization-completed-mate: the existing statement is Ordered completed exchange equals the completion-unit-conjugated ordinary mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing statement is Projection-formula coherence for a square of ringed topoi. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-ringed-projection-mate-exact: the existing statement is Exactness data for the ringed-topos projection mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-weil-pbc-ringed-projection-restriction: the existing statement is Localization comparisons for the ringed projection mate. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lemma-weil-pbc-perfect-projection-formula: the existing statement is Perfect projection formula for reductions. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing statement is Operator and base-change naturality of the formula. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lemma-weil-pbc-projection-formula-tower-compatibility: the existing statement is Projection formulas form a coefficient tower. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs prop-coef-integral-dualizing: the existing statement is The integral dualizing object and its adjunction. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs prop-weil-pbc-direct-image-limits: the existing statement is Direct image, derived limits, and completeness. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs sk-def-sf-exchanges: the existing statement is Exchange and projection transformations, typed. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs thm-sf-direct-image-tor-amplitude: the existing statement is Direct image and finite Tor amplitude. It does not state commuting-square naturality and both beta/alpha shift equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-kun-constant-projection-morphism: the existing statement is Canonical constant-coefficient derived projection morphism. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-kun-projection-formula-map: the existing statement is The projection-formula morphism. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-pd-proetale-section-module-functors: the existing statement is Normalized tensor structures on existing pro-etale section-module functors. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-pd-section-derived-realization: the existing statement is Canonical derived section-module realization. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-pd-section-derived-tensor-data: the existing statement is Canonical derived section-module tensor data. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-pd-section-module-operations-data: the existing statement is Existing section-module operations and pure-tensor data. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-pur-system-tensor-mate-arrows: the existing statement is Canonical tensor and proper/open arrows for varying coefficient systems. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-sfb-module-projection-section-arrows: the existing statement is Canonical module projection mate and section comparisons. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-sfb-module-projection-section-composites: the existing statement is Unit-normalized forward section projection composite. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-sfb-module-projection-section-inverse: the existing statement is Conditional inverse section projection composite. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-sfb-module-section-projection-arrow: the existing statement is Canonical section projection arrow. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-sfb-proetale-projection-exchange-maps: the existing statement is Canonical projection and exchange maps on internal pro-etale modules. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-sp-finite-free-direct-image-data: the existing statement is Normalized scalar models and canonical coefficient comparison data. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-weil-pbc-four-arrows: the existing statement is Four finite-level arrows. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-weil-pbc-four-corners: the existing statement is Four finite-level corners. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs def-weil-pbc-projection-formula-map: the existing statement is Projection-formula map. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs det-cor-sf-direct-image-ctf-open-tor: the existing statement is Scalar projection formula and the Tor bound for an open immersion. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs det-prop-p1-adjunction-rational-triangle: the existing statement is Triangle identities for the rational projective line. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs det-thm-sf-pf-field-localizing: the existing statement is The proper projection formula on the rational localizing categories. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs det-thm-sfb-proper-base-change-rational: the existing statement is Proper direct image, base change and projection formula for $E$ and $\overline{\mathbf Q}_\ell$. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs fix-prop-projection-formula: the existing statement is Compact-support projection formula at all coefficient stages. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-asd-ordinary-finite-p1-adjunction: the existing statement is Ordinary etale projective-line adjunction with arbitrary finite invertible-exponent coefficients. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-asd-proper-finite-coefficient-extension: the existing statement is Canonical unbounded proper direct-image comparison for finite coefficient extension. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-asd-proper-finite-coefficient-extension-core: the existing statement is Unbounded proper coefficient comparison and restricted projection identity. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-cbc-rational-compact-support-coefficient-coherence: the existing statement is Coherent coefficient comparisons for rational compact-support exchange. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-coef-finite-adjunction-transition: the existing statement is Finite-level adjunction transition compatibility. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-fix-proetale-scalar-mate-normalization: the existing statement is Pro-etale scalar mate restricts to the specified projection arrow. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-fix-proper-etale-origin-scalar-isomorphism: the existing statement is Proper scalar comparison is invertible on bounded etale-origin inputs. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-kun-0f0f: the existing statement is Projection formula, integer coefficients. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-kun-0f12: the existing statement is Tensor product with a constant complex. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-kun-geometric-point-projection-comparison: the existing statement is Geometric-point projection morphism agrees with the constant-section projection morphism. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-kun-kunneth-map-agrees: the existing statement is Compatibility of the Kunneth map with Leray, proper base change and the projection formula. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-kun-kunneth-via-0f1n: the existing statement is Compatibility of the Kunneth map with the projection-formula variant. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-kun-proj-formula-natural: the existing statement is Naturality of the projection formula. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pd-module-ringed-topos-derived-comparison: the existing statement is Module-object and ringed-topos derived tensor comparison. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-per-field-exceptional-tensor: the existing statement is Exceptional tensor comparison for coefficients pulled from a field. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-per-noetherian-affine-line-unit: the existing statement is Ordinary finite-coefficient affine-line unit over a Noetherian base. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-per-regular-normal-crossings-constant-image: the existing statement is Constant etale direct image across a regular normal crossings boundary. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pod-frobenius-cup-transport: the existing statement is Finite-coefficient Frobenius transport commutes with mixed-support cup product. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-adic-projection-shift-coherence: the existing statement is Shift compatibility of the compact-support projection and trace transpose. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-compact-support-completed-projection-coherence: the existing statement is Completion coherence for the integral projection mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-compact-support-integral-coefficient-comparison: the existing statement is Integral compact support under finite free coefficient extension. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-etale-compact-scalar-coherence: the existing statement is Ordinary etale compact-support scalar compatibility with projection and composition. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-etale-exceptional-constant-tensor: the existing statement is Constant-coefficient tensor calculus for the finite etale exceptional adjoint. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-finite-projection-action-laws: the existing statement is Tensor-action and open-counit identities for finite-level projection maps. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-flag-local-comparison: the existing statement is Coordinate Gysin composition and the supported cup product. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-flag-localized-product: the existing statement is Forgetting a composite of subbundle divisor classes. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-ordinary-adjunction-scalar-compatibility: the existing statement is Scalar compatibility of the ordinary completed adjunction. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-projection-formula-coefficient-coherence: the existing statement is Unit and coefficient associativity of compact-support projection maps. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-projection-purity-agreement: the existing statement is Agreement with the affine-line route on affine space. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-system-clopen-tensor-compatibility: the existing statement is Proper/open tensor-mate interchange on varying-coefficient systems. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-system-compactification-pf-substitution: the existing statement is Refinement comparisons intertwine strict-system projection maps. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-system-level-projection-formula-coherence: the existing statement is Strict-system projection formula composition coherence. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-system-projection-tensor-associativity: the existing statement is Tensor-variable associativity of the specified system projection maps. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-pur-system-tensor-transpose-composition: the existing statement is Composition of the counit-defined tensor transposes on systems. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sf-cbc-constant-tower-direct-image-normalization: the existing statement is Constant strict towers and normalized derived direct image. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sf-constant-semilinear-generator-comparison: the existing statement is Scalar restriction identifies the single proper and open reduction generators. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sf-exceptional-product-direct-image-compatibility: the existing statement is Exceptional external product is compatible with immersion direct images. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sf-finite-exchange-projection-commshift: the existing statement is Finite geometric exchange and projection commute with shifts. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sf-kunneth-coherence: the existing statement is Coherence of the relative product. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-coefficient-push-filtered-legs: the existing statement is Flat coefficient push comparison from a bounded filtered module presentation. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-integral-quotient-direct-image-comparison: the existing statement is Unbounded quotient-scalar refinement of integral direct image. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-integral-quotient-projection-comparison: the existing statement is Reduction of the actual unbounded integral projection morphism. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-qlbar-direct-image-comparison: the existing statement is Algebraic-closure coefficient change commutes with bounded-below direct image. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-ringed-kunneth-factorizations: the existing statement is Two factorizations of the ringed-topos external product comparison. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-ringed-projection-canonical-normalization: the existing statement is Identity and composition normalization of ringed projection mates. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-ringed-projection-first-shift: the existing statement is The ringed projection mate commutes with shifts in its direct-image input. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-ringed-projection-section-specialization: the existing statement is Symmetry-ordered section specialization of the canonical projection mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-ringed-projection-tensor-associativity: the existing statement is Canonical tensor constraints and associativity for one projection mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-ringed-projection-tensor-composition: the existing statement is Tensor and composition coherence of ringed-topos projection maps. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-trace-base-change-first: the existing statement is Trace and base-change rearrangement before the first triangle. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-trace-base-change-second: the existing statement is Trace and base-change rearrangement before the second triangle. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sp-completion-mate-comparison: the existing statement is The strict quotient-tower exchange realizes the completed-adjunction mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sp-finite-free-direct-image-coherence: the existing statement is Coherent finite-free coefficient comparison for ambient derived direct image. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sp-finite-free-direct-image-columns: the existing statement is Finite-basis columns of the restricted canonical coefficient mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sp-p1-counit-scalar: the existing statement is Scalar compatibility of the actual projective-line adjunction counit. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-trf-external-comparison-triangles: the existing statement is Triangle compatibility of the external direct-image comparison. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-trf-support-product-base-change: the existing statement is Support-product comparison with base change along the other leg. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-boundary-proetale-projection-comparison: the existing statement is Proper compact-support and tensor comparisons identify etale and pro-etale projection maps. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-augmented-diagram-projection-mate: the existing statement is Projection mate for an augmented coefficient diagram before taking inverse limit. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-derived-adjunction-shift: the existing statement is Canonical derived ringed-topos adjunction is shift-compatible. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-finite-level-rectangle: the existing statement is Finite-level exchange rectangle. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-formal-exact-projection-mate: the existing item combines exactness, counit-specialized naturality/shifts, triangle morphisms and unit normalization; this new lemma isolates an arbitrary-arrow argument and requires no exactness.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing statement is Coefficient normalization of the raw ordered completed exchange. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-realization-completed-mate: the existing statement is Ordered completed exchange equals the completion-unit-conjugated ordinary mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing statement is Projection-formula coherence for a square of ringed topoi. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-ringed-projection-mate-exact: the existing statement is Exactness data for the ringed-topos projection mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-weil-pbc-ringed-projection-restriction: the existing statement is Localization comparisons for the ringed projection mate. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lemma-weil-pbc-perfect-projection-formula: the existing statement is Perfect projection formula for reductions. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing statement is Operator and base-change naturality of the formula. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lemma-weil-pbc-projection-formula-tower-compatibility: the existing statement is Projection formulas form a coefficient tower. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs prop-coef-integral-dualizing: the existing statement is The integral dualizing object and its adjunction. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs prop-weil-pbc-direct-image-limits: the existing statement is Direct image, derived limits, and completeness. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs sk-def-sf-exchanges: the existing statement is Exchange and projection transformations, typed. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs thm-sf-direct-image-tor-amplitude: the existing statement is Direct image and finite Tor amplitude. It does not state the two right-action evaluation equations for arbitrary c:LK→E under bare bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-adjunction-oplax-mate: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sfb-monoidal-adjunction-mates: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-trf-adjoint-mate: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-naturality-shifts vs lem-sc-derived-monoidal-pullback-unital-shift: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-adjunction-oplax-mate: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sfb-monoidal-adjunction-mates: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-trf-adjoint-mate: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

lem-weil-pbc-tensor-arrow-mate-right-unit vs lem-sc-derived-monoidal-pullback-unital-shift: the existing node requires monoidal/derived data or compares adjoints; it does not give this arbitrary-arrow tensor-mate calculation with only the stated bifunctor data.

