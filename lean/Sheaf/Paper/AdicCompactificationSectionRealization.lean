/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.CommonAdicCompactificationSectionData


/-! # Adic compactification cohomology and extension-by-zero sections

Source: Bhatt--Scholze 6.8.14--6.8.15; Milne 18.1, 18.3(b)
(blueprint: lem-a1-adic-compactification-section-realization).

## Main statements

- `adicCompactificationSectionRealization`: existence of the normalized comparison data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Adic compactification cohomology and extension-by-zero sections, simultaneously
at finite fields and in the prescribed common-stage category. The package's equations
fix the continuous realization, coefficient units, open restrictions and scalar maps.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15, Proposition 6.8.11(3);
Milne, Definition 18.1 and Proposition 18.3(b).
(blueprint: lem-a1-adic-compactification-section-realization).

Proof plan (the DAG's nine steps, including all normalization obligations):
1. Work first at a finite field $E$. The schemes $U,T,s$ satisfy the realization hypotheses:
$s=\operatorname{Spec}k$ is Noetherian (the only ideals of $k$ are $0,k$), and
[lem-weil-pbc-finite-type-over-noetherian] applies to their structure maps. Applying
[lem-fin-finite-type-fibre-dimension-bound] over the one-point quasi-compact base $s$ bounds
their dimensions, since the unique fibre is the scheme itself. Distinguish ordinary ringed-site
extension $e_j$ for $B$-modules from the adic functor defined by the quotient tower. For an
integral representative $K$, the compactification $(j,\mathrm{id}_T)$ in
[def-weil-integral-rational-qbar-compact-support] gives $Rj_!K=\mathcal L_TJ_j\mathcal R_UK$.
Here the identity proper direct image is the identity and $J_j$ is termwise finite-level
extension. Apply [lem-sf-integral-open-reduction-comparison]: its specified system isomorphism
$r_j(K):\mathcal R_T(e_jK)\cong J_j\mathcal R_UK$ respects every quotient transition, $e_jK$ is
complete, and its map $d_j(K)$ identifies this very total limit with $e_jK$. Thus the adic and
ordinary integral extensions agree naturally, with the stated open-adjunction normalization.
This uses the strict-system isomorphism, rather than an inference that arbitrary maps agreeing
at every finite level agree in the derived category.

2. The tensor comparison of [lem-sf-open-tensor-normalization], applied on the $B$-ringed sites
with $N=E_T=B_T[1/\varpi]$, gives $E_T\otimes^L_{B_T}e_jK\cong e_j(E_U\otimes^L_{B_U}K)$. The
$E_T$-action is the balanced tensor action. Combine this with step 1 and the formula for $J$ in
[lem-per-continuous-rational-derived-realization] to obtain $J_TRj_!QK\cong e_jJ_UQK$. The open
unit identifies its restriction to $U$ with the identity. Naturality for integral maps implies
naturality for rational maps: a map $f/\varpi^n$ is sent on both sides to $\varpi^{-n}$ times
the map for $f$. Hence this is an identification of the given rational functors. The ringed
extension is sheafification of the extension-by-zero $E_T$-module presheaf, by
[lem-pur-site-restriction-module-adjunction-exact]. Thus the coefficients here are the
continuous $E_T$ of the realization theorem.

3. At the rational stage [sk-lem-sf-open-ctf] says that $Rj_!$ preserves $D^b_c$ and every
cohomological interval, without imposing a numerical integral Tor interval. In particular it
preserves the heart. Under the t-exact equivalences $J_U,J_T$, its restriction is the exact
module extension in step 2; consequently $j_!:\Sh_c(U,E)\to\Sh_c(T,E)$ is exact. This does not
assume that an arbitrary rational-heart representative is an integral sheaf with flat finite
reductions.

4. Choose the closed complement $i:Z\hookrightarrow T$ of $j$ with reduced scheme structure. The
ringed open--closed identities of [lem-weil-pbc-proetale-ringed-open-closed] give
$j^{-1}e_jJ_UF\cong J_UF$ and $i^{-1}e_jJ_UF=0$. Apply the inverse-image comparison and full
faithfulness of [lem-per-continuous-rational-derived-realization] to get $j^*j_!F\cong F$ and
$i^*j_!F=0$ in the adic hearts. A geometric point inside $U$ factors through $j$, and one
outside $U$ factors through $i$ (the ideal of $Z$ maps to zero in its residue field). The
pullback/fibre identity of [lem-per-adic-heart-pullback-fibres], applied respectively to $j$ and
$i$, gives the claimed inside fibre and zero outside fibre. The scheme $Z$ is again separated
finite type, so both pullback comparisons apply.

5. Now suppose $T$ proper, and put $b:T\to s=\operatorname{Spec}k$. For an integral
representative $K$, the compact-support definition gives
$Ra_{U!}K=R\lim_n\operatorname{Res}_nRb_{*,n}j_!K_n$. By step 1 the strict tower
$\operatorname{Res}_nj_!K_n$ is the reduction tower of $e_jK$. The completed-coefficient
direct-image comparison of [lem-pur-completed-coefficient-pushforward-comparison], applied to
$f=b$ and the derived-complete object $e_jK$ (its strict reduction system being $\mathcal
R_T(e_jK)$), therefore identifies this expression with the ordinary completed-coefficient
$Rb_*^B(e_jK)$; its $n$-th projection is $Rb_*^B$ of the reduction map followed by the
coefficient-restriction comparison. The same object is $Rb_*(Rj_!K)$ by the tower definition of
[def-weil-derived-direct-image]. All identifications are maps of strict towers, including their
projections. Rationalizing and using [lem-a1-rational-direct-image-realization] gives
$Ra_{U!}F\cong Rb_*j_!F$ and its continuous realization $Rb_*^E(e_jJ_UF)$. The cohomology
definition [def-weil-ordinary-compact-cohomology] now gives $H_c^0(U,F)\cong H^0(T,j_!F)$.

6. For any $C\in D^b_c(s,E)$, [lem-weil-point-fibre-equivalence] and the definition
[def-weil-finite-coefficient-point] identify $\operatorname{Fib}_s\mathbf1_s$ with $E[0]$: the
continuous coefficient normalization of [lem-per-continuous-rational-derived-realization] gives
$B_s(s)=C(|s|,A)=A$. Thus
$\operatorname{Hom}(\mathbf1_s,C)\cong\operatorname{Hom}_{D(E)}(E[0],\operatorname{Fib}_sC)$.
The latter is $H^0(\operatorname{Fib}_sC)$, with normalization evaluation on $1$: indeed maps
from $E[0]$ are cycles, homotopies identify cycles differing by a boundary, and $E[0]$ is
K-projective since a cycle $z$ in an acyclic vector-space complex is $dh$ and the map $1\mapsto
h$ is its null homotopy. [lem-coef-kprojective-derived-hom-bijection] makes this computation in
the homotopy category a computation in the derived category. These descriptions prove naturality
and $E$-linearity, not merely an abstract vector-space isomorphism.

7. Apply step 6 to $C=Ra_{W*}M$ for $W=U$ or $T$ and $M$ in its constructible heart. By
[def-weil-ordinary-compact-cohomology] its degree-zero fibre cohomology is $H^0(W,M)$. The
adjunction identification of [lem-a1-rational-direct-image-realization], with the pullback
comparison of [lem-per-continuous-rational-derived-realization], gives
$\operatorname{Hom}(\mathbf1_s,Ra_{W*}M)\cong
\operatorname{Hom}(La_W^*\mathbf1_s,M)\cong\operatorname{Hom}(\mathbf1_W,M)$.
The last unit identification is multiplication $E_W\otimes_{a_W^{-1}E_s}a_W^{-1}E_s\cong E_W$.
Both objects in the last Hom are in the heart, which is a full subcategory by
[def-weil-constructible-heart]. This proves the ordinary isomorphism for $U$; combined with step
5 for $M=j_!F$ it proves the compact-support isomorphism for $T$.

8. The compact-to-ordinary map for this compactification is $Rb_*j_!F\to Rb_*Rj_*F\cong
Ra_{U*}F$, where $j_!F\to Rj_*F$ is the $j^*\dashv Rj_*$-adjunct of the open-unit inverse
$j^*j_!F\cong F$. At finite level this is exactly the extension-to-direct-image comparison; step
1 identifies the realized open unit and counit, and the direct-image realization identifies the
actual ordinary units and counits. The last isomorphism is the canonical ringed derived
direct-image compositor [lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. On a
morphism $t:\mathbf1_T\to j_!F$ the adjunction formula therefore gives $\mathbf1_U\cong
j^*\mathbf1_T\xrightarrow{j^*t}j^*j_!F\cong F$. Thus steps 5--7 identify the specified
comparison with restriction. For an open $V\subset U$, restricting this expression gives
$(j^*t)|_V$ followed by the restricted open-unit inverse; the normalized open unit in
[lem-sf-open-tensor-normalization] is identity on sections. This proves compatibility with
ordinary open restriction, without assuming that compact support itself restricts functorially
to every open.

9. For a finite extension $E\subset L$, [lem-weil-finite-free-completed-scalar-comparison]
identifies completed scalar extension with ordinary derived coefficient tensor. Apply
[lem-sf-open-tensor-normalization] with the new coefficient sheaf to obtain its open-extension
comparison; on restriction to $U$ it is identity. The realization comparisons commute with this
coefficient extension by [lem-per-continuous-rational-derived-realization] and
[lem-a1-rational-direct-image-realization]. The actual ordinary-adjunction bijections commute
with it by [lem-pur-ordinary-adjunction-scalar-compatibility], and point evaluation commutes
with it by [lem-weil-point-sections-scalar-extension]. Thus each arrow of steps 5--8, including
the restriction formula, commutes with scalar extension. Its unit normalization is $1\mapsto1$,
$x\otimes1\mapsto x$, and $((x\otimes a)\otimes b)\mapsto x\otimes ab$; no assertion that
$j_!\mathbf1_U=\mathbf1_T$ is needed. Finally use [def-weil-algebraically-closed-coefficients]:
represent $F$, a morphism, or a finite comparison diagram over one common finite field, apply
the preceding formulas there, and pass to the common-stage class. Two representatives agree at a
further finite extension, where the same scalar compatibility identifies the formulas. Inverses
and compositions pass in the same way. By [lem-per-adic-heart-pullback-fibres], standard
cohomology and truncation are computed at a common finite stage; applying these to the
finite-stage cone of a represented heart morphism shows that its kernel and cokernel, and hence
exactness of $j_!$, are also computed stagewise. This proves the heart and fibre assertions as
well as the comparison assertions at $\Omega$.
-/
theorem adicCompactificationSectionRealization :
    ∃ F : AdicCompactificationSections.FiniteFamily D l hl,
      Nonempty (AdicCompactificationSections.CommonFamily D l hl Ω F) := by
  sorry

end WeilConjectures
