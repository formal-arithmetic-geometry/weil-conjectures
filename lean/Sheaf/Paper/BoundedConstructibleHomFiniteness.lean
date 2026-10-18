/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Internal Hom finiteness for finite coefficient extensions in the scheme universe

Source: Weil conjectures blueprint, main-20261015,
`sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.md`;
the node's reviewed Bhatt--Scholze proof, steps 1--8 (blueprint: lem-sfb-dc-hom-preserves).

The published finiteness class only constructs continuous coefficients from fields in
`Type 0`. This statement uses the already published universe-generalized continuous
coefficient ring for any finite normed extension in the scheme universe. The integral
coefficient ring is the closed unit ball, explicitly characterized by `hO`.
The algebraic-closure case is the imported existing
`isMonoidalClosed_boundedConstructible`, using its `algebraicClosure` coefficient instance.
No coefficient ring, derived internal Hom or constructibility notion is redefined.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The rational and integral finite-extension cases of internal Hom finiteness, without
restricting the coefficient carrier to Type 0. The subring `O` is exactly the ring of integers,
by `hO`. A `NormedAlgebra` structure supplies the topology of the extending absolute value.
`ObjectProperty.IsMonoidalClosed` means solely that internal Hom carries two objects with
the given property to an object with that property; it imposes no tensor closure condition.

Source: the node's reviewed proof from Bhatt--Scholze, Sections 3.4, 6.7 and 6.8,
steps 1--8 (blueprint: lem-sfb-dc-hom-preserves).

Proof (the integral case is steps 1--3; the rational case is steps 4--8):

1. First consider $\Lambda=\underline{\mathcal O_E}$. The only ideals of $k$ are $0$ and $k$, so
$\operatorname{Spec}k$ is Noetherian; [lem-weil-pbc-finite-type-over-noetherian] makes $X$
Noetherian. Choose a uniformizer $t$ of $A_0=\mathcal O_E$. By
[lem-weil-l-adic-extension-integers-dvr], $A=A_0/(t)$ is a finite field; its characteristic is
$\ell$, since $\ell$ belongs to the maximal ideal. By [sk-prop-sfb-qlbar-colimit-x], the actual
coefficient ring is $B=\mathcal O_{E,X}=\varprojlim_n(A_0/t^n)_X$. The bounded-constructible
hypothesis on $K$ and $L$ [sk-def-sfb-bounded-constructible] means bounded cohomology
constructible by general local finite presentations. Apply
[lem-sfb-integral-lfp-constant-model-comparison] to each cohomology sheaf of $K$ and $L$: both
complexes have bounded cohomology with finite constant local models. This invocation is the
coefficient-specific bridge, not an identification by definition. Now apply implication (1) to (2)
of [lem-sfb-integral-cohomological-adic-criterion], whose condition (1) explicitly uses finite
constant scalar models. It gives local derived $(t)$-completeness of $K,L$, in the sense used by
that criterion, and identifies $K_1=K\otimes_B^LA_X$, $L_1=L\otimes_B^LA_X$ with bounded
finite-Tor-amplitude étale complexes with constructible finite-dimensional $A$-cohomology. Hence
these reductions satisfy the explicit finite constant local model hypotheses of the finite-field
child below.

2. Set $H=R\mathcal Hom_B(K,L)$. Apply [lem-coef-integral-hom-reduction] to this $B$ and $n=1$,
with its finite-field datum taken in the characteristic $p$ of $k$, so that its hypothesis
$\ell\ne p$ is the one in force. Its statement applies to an arbitrary scheme and arbitrary
ambient complexes; it does not impose a finite-ground-field or site-perfectness hypothesis. Its
evaluation-defined comparison gives $$H\otimes_B^LA_X\xrightarrow{\sim}R\mathcal
Hom_{A_X}(K_1,L_1).$$ This is a comparison of the ambient internal Homs, not a new choice of Hom
on a constructible subcategory. The completeness clause of that lemma is not used here: it
concerns the derived-limit notion of completeness of its own definitions, whereas the criterion of
step 1 uses local derived completeness; step 3 proves the latter for $H$ directly.

3. Apply [lem-sfb-finite-field-internal-hom-finiteness] to the finite field $A$ and to $K_1,L_1$
with their scalar-constant constructible cohomology established in step 1. By step 2,
$H\otimes_B^LA_X$ is therefore bounded with finite constant local model cohomology. Apply
[sk-thm-pe-constructible-comparison] on the Noetherian (hence qcqs) scheme $X$, with the discrete
Noetherian field $A$, to obtain a bounded constructible étale complex $C$ whose pullback is this
reduction. It has finite Tor amplitude: tensor of $A$-module sheaves is exact, as is checked
locally by tensor of vector spaces and exact sheafification; consequently for a bounded complex
its derived tensor with any degree-zero module sheaf has the same cohomological support bound.
Next, $H$ is locally derived $(t)$-complete [def-weil-pbc-locally-derived-ringed-ideal-complete].
Let $U$ be an object of $X_{\mathrm{proét}}$, let $f\in(t)(U)$, and write $B_U$ for the restricted
ring. By [lem-weil-pbc-ringed-internal-hom-exact-restriction], on $X_{\mathrm{proét}}$ and on the
slice site over $U$, together with the symmetry of the derived tensor product, $$\begin{aligned}
R\mathcal Hom_{B_U}(B_U[1/f],H|_U)&\cong R\mathcal Hom_{B_U}(B_U[1/f],R\mathcal
Hom_{B_U}(K|_U,L|_U))\\ &\cong R\mathcal Hom_{B_U}(K|_U\otimes^{\mathbf L}_{B_U}B_U[1/f],L|_U)\\
&\cong R\mathcal Hom_{B_U}(K|_U,R\mathcal Hom_{B_U}(B_U[1/f],L|_U))=0, \end{aligned}$$ the last
vanishing being the local derived completeness of $L$ from step 1. Together with this completeness
of $H$, the étale complex $C$ verifies condition (2) of
[lem-sfb-integral-cohomological-adic-criterion]. Its implication (2) to (1) gives bounded
cohomology of $H$ with finite constant scalar local models. The reverse direction of
[lem-sfb-integral-lfp-constant-model-comparison] makes these cohomology sheaves constructible in
the general ring-object sense. Thus $H$ meets exactly the bounded-constructible predicate in the
conclusion [sk-def-sfb-bounded-constructible].

4. Use the ordinary unbounded layer-B derived category of [sk-def-sfb-derived-categories] and the
general local-finite-presentation predicate of [sk-def-sfb-bounded-constructible,
def-sfb-constructible-module]. For the field-coefficient comparison lemmas below, their
coefficient sheaves are $E_T=p_T^*\underline E$ and $\overline{\mathbf
Q}_{\ell,T}=p_T^*\underline{\overline{\mathbf Q}_\ell}$:
[def-weil-pbc-condensed-e-module-category] defines $p_T^*=\pi_T^{-1}\circ a^*$, with $a^*$ the
sheafified left Kan extension along $S\mapsto\operatorname{Spec}LC(S,\mathbf Z)$. This is term by
term the construction in [sk-def-sfb-pullback-from-point]. The ring $C(-,E)$ has exactly the
sections of $\underline E$; the bounded-image ring $\underline\Omega$ has exactly the sections of
the specified $\underline{\overline{\mathbf Q}_\ell}$. Hence the comparison lemmas use $E_T$ and
$\overline{\mathbf Q}_{\ell,T}$ themselves. The finite cokernel presentations coincide with
[def-sfb-locally-finitely-presented].

5. For $E_X$ and $\overline{\mathbf Q}_{\ell,X}$ coefficients, apply respectively
[lem-weil-pbc-condensed-lfp-local-triviality] and
[lem-weil-pbc-condensed-qbar-lfp-local-triviality] to each locally closed stratum of each
general-lfp constructible cohomology sheaf. Every such stratum is Noetherian because $X$ is
Noetherian. By step 4 the coefficient sheaves and finite-presentation predicates agree with those
in the two lemmas. They make the restriction pro-étale locally finite free, hence give finite
constant local models with scalar modules $E^r$ or $\overline{\mathbf Q}_\ell^r$ in the sense of
[sk-def-sfb-constructible]. Conversely a finite scalar presentation is a presentation over the
coefficient sheaf by extending its matrix; extension of scalars preserves cokernels because it is
a left adjoint [sk-def-sfb-change-of-scalars]. Thus such scalar local models meet the general-lfp
constructibility predicate. Boundedness is the same cohomological condition in both predicates.

6. For any coefficient-ring map $R\to S$ on $X_{\mathrm{proét}}$, apply
[lem-sfb-dc-hom-scalar-adjunction] in the ordinary unbounded derived categories. Write
$K_S=S\otimes_R^{\mathbf L}K$ and $U$ for restriction. The lemma supplies the natural
evaluation-normalized identification $$U R\mathcal Hom_S(K_S,N)\simeq R\mathcal Hom_R(K,UN).$$ It
also makes $U$ conservative. These conclusions will be used with $R=\mathcal O_{E,X}$, $S=E_X$,
and with $R=E_X$, $S=F_X$ or $\overline{\mathbf Q}_{\ell,X}$. The lemma requires neither
constructibility nor flatness. This cites the scalar-adjunction argument as a separate obligation
rather than repeating it inline.

7. For integral $K_0,L_0$ bounded constructible in the general-lfp sense,
[lem-sfb-integral-lfp-constant-model-comparison] applied to the cohomology of $K_0$ supplies the
finite constant local models required by [lem-sfb-constructible-internal-hom-continuity]. This
also applies to the integral representatives later furnished by the rationalization equivalence;
no stronger hypothesis on those representatives is assumed. Take a bounded-below complex
representative of $L_0$. By [sk-prop-sfb-qlbar-colimit-x], $E_X=B[1/\ell]$ is the sequential
colimit in sheaves of $B$-modules, equipped with its localization ring structure. Tensoring this
module colimit with the representative gives the termwise colimit of
$L_0\xrightarrow{\ell}L_0\xrightarrow{\ell}\cdots$. This system has a common lower bound. By
[lem-sfb-constructible-internal-hom-continuity], $$R\mathcal Hom_B(K_0,L_0)[1/\ell] \simeq
R\mathcal Hom_B(K_0,L_0[1/\ell]).$$ Here the left side is the same scalar localization of internal
Hom. The module-object category is Grothendieck abelian by [lem-sfb-modobj-grothendieck], so
filtered colimits are exact; tensoring with $B[1/\ell]$ is therefore exact, being the filtered
colimit of tensoring with the free module $B$. Step 6 identifies the right side with the
restriction of $R\mathcal Hom_{E_X}((K_0)_E,(L_0)_E)$. Hence the canonical evaluation-transpose
map $$E_X\otimes_B^L R\mathcal Hom_B(K_0,L_0)\longrightarrow R\mathcal
Hom_{E_X}((K_0)_E,(L_0)_E)$$ is an isomorphism. Indeed its restriction is precisely the continuity
map above; scalar multiplication by $\ell$ on the target is invertible, so the compatible maps
from the stages define the displayed localized map.

8. For arbitrary bounded constructible $E_X$-complexes $K,L$, apply
[def-sfb-rationalization-equivalence] with the fixed prime $\ell$, finite subextension $E$ and its
pulled-back coefficient rings. Its composite with localization is the restriction of
$E_X\otimes_B^L-$ to bounded constructible complexes. The equivalence therefore gives integral
bounded constructible representatives $K_0,L_0$ with $(K_0)_E\simeq K$ and $(L_0)_E\simeq L$: the
standard localization has the objects of its source, and the equivalence is compatible with scalar
extension. These representatives initially satisfy only the general-lfp predicate; step 7 applies
to them because it explicitly invokes the integral comparison lemma. Step 3 makes $H_0=R\mathcal
Hom_B(K_0,L_0)$ bounded constructible. By [lem-sfb-extend-scalars-bounded-constructible],
$(H_0)_E$ is bounded constructible. The evaluation-compatible comparison proved in step 7
identifies it with $R\mathcal Hom_{E_X}(K,L)$. This proves the rational finite-extension case.
-/
lemma boundedConstructibleHom_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X.left)).IsMonoidalClosed ∧
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj O) X.left)).IsMonoidalClosed := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
