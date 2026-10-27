/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

import Sheaf.Paper.IntegralFiniteTopologicalPresentation
import Sheaf.Paper.FiniteFreeScalarDerivedComparison

/-! # Assembly of the integral-to-finite perfect scalar model -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar

open CondensedRing

private theorem restrictionReflectsIsomorphisms {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (Z : Scheme.{u}) : (restriction a Z).ReflectsIsomorphisms := by
  let F : ModuleRingedComparison.internalModules Λ'.X Z ⥤
      ModuleRingedComparison.internalModules Λ.X Z :=
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
  have : F.ReflectsIsomorphisms := by
    refine ⟨?_⟩
    intro M N f hf
    have : IsIso f.hom := by
      change IsIso ((Mod.forget (condensedRingObj Λ.X Z)).map (F.map f))
      infer_instance
    have : IsIso ((Mod.forget (condensedRingObj Λ'.X Z)).map f) := by
      change IsIso f.hom
      infer_instance
    exact isIso_of_reflects_iso f (Mod.forget (condensedRingObj Λ'.X Z))
  change F.mapDerivedCategory.ReflectsIsomorphisms
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

/-- Integral-to-finite coefficient tensor and direct-image mates in a two-term perfect model.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-direct-image.proof.md, finite coefficient extensions and formal properties
(blueprint: lem-sfb-integral-finite-scalar-perfect-model).

Proof plan (the complete nine-step DAG proof):

1. By [lem-weil-l-adic-extension-integers-dvr], $O$ is a DVR domain. If $A=0$, choose $r=0$ and
the zero maps. Otherwise choose finitely many additive $O$-module generators of the finite set
$A$ and the resulting surjection $q:O^r\to A$; its formula is $q((x_j))=\sum_j a(x_j)b_j$. Put
$N=\ker q$. Apply [lem-sc-dvr-saturation-line-smith-normal-form] to $N\subseteq O^r$: in a
basis $e_1,\ldots,e_r$ of the target, $N$ has basis $d_1e_1,\ldots,d_me_m$, with $m\le r$ and
all $d_i\ne0$ (a zero basis vector is impossible). Choose $s\ge1$ with $\ell^sA=0$. Then
$\ell^se_j\in N$ for every $j$. If $m<r$, its coordinate along $e_r$ is both $\ell^s$ and zero,
impossible in the characteristic-zero domain $O$. Thus $m=r$. The inclusion of this basis
defines an injective square matrix $\phi:O^r\to O^r$ with image $N$. This constructs the
required algebraic short exact sequence without assuming that $a$ is surjective or that $A$ is
flat.

2. Give $O^r$ its product valuation topology. The matrices of the preceding basis change and
its inverse have entries in $O$, so they act continuously. In these coordinates the inverse of
$\phi:O^r\to N$ is division by $d_i$ in coordinate $i$; it is continuous because
$|d_i^{-1}(x-y)|_E=|d_i|_E^{-1}|x-y|_E$. Also $q$ is continuous by its formula and continuity
of $a$. For any profinite $S$, a continuous $v:S\to O^r$ with $qv=0$ therefore lifts uniquely
and continuously through $\phi$. For a continuous $w:S\to A$, choose one $t_b\in O^r$ above
each $b\in A$ and set $v(s)=t_{w(s)}$. Each fibre of $w$ is clopen and
$v^{-1}(U)=\bigcup_{t_b\in U}w^{-1}(b)$, so $v$ is continuous and $qv=w$. Injectivity is
pointwise. The pointwise $C(S,O)$-actions make both arrows linear and they commute with
precomposition. Thus [sk-def-sfb-condensed-ring] identifies these modules with the finite
powers of $\underline O$ and $\underline A$; [lem-pe-internal-module-sectionwise-short-exact]
turns the sectionwise short exact sequence into a short exact sequence of condensed $\underline
O$-modules. This does not use [lem-pe-profinite-sections-finite-quotient], whose ring-algebra
hypotheses would not apply to arbitrary module matrices.

3. The functor $p_Z^*=\pi_Z^{-1}a^*$ is strong symmetric monoidal, and $a^*$ is exact, by
[lem-weil-pbc-profinite-point-pullback]; the inverse image $\pi_Z^{-1}$ on abelian sheaves
carries short exact sequences to short exact sequences by
[lem-weil-pbc-site-pullback-abelian-exact]. Hence $p_Z^*$ is exact. Hence it carries this short
exact sequence to $0\to O_Z^r\xrightarrow{\phi_Z}O_Z^r\xrightarrow{q_Z}A_Z\to0$, with the same
finite-sum coordinates and action maps. For the passage to section-ring module sheaves use the
exact tensor equivalence [lem-pe-internal-section-tensor-comparison], which preserves finite
powers, acyclicity and K-flatness. Apply [lem-sfb-finite-free-mono-cokernel-kflat] to this
specified monomorphism and cokernel. It says that the specified augmentation $P_Z\to A_Z[0]$ is
a quasi-isomorphism, that its terms are flat and that $P_Z$ is K-flat. It also identifies $P_Z$
with the cone of $\phi_Z[0]$, including the augmentation from its degree-zero term.

4. Work with section-ring sheaves via [lem-pe-internal-section-tensor-comparison] and the
derived scalar adjunction equivalence [lem-sfb-internal-section-scalar-adjunction]. Let $C$
represent $K$ and choose a flat-term K-flat replacement $Q\to C$ by [lem-pc-kflat-resolution].
The native one-K-flat tensor comparison [lem-sf-ringed-derived-native-tensor] identifies
$P_Z\otimes^LK$ with $Q_{O_Z}\operatorname{Tot}(P_Z\otimes C)$ and with
$Q_{O_Z}\operatorname{Tot}(P_Z\otimes Q)$. Tensoring the augmentation $P_Z\to A_Z[0]$ with the
K-flat $Q$ gives a quasi-isomorphism to $A_Z\otimes Q$; this is preservation of
quasi-isomorphisms by tensoring with a fixed K-flat complex in
[lem-weil-pbc-total-tensor-homotopy-cone-signs]. In
[lem-pe-restricted-kflat-tensor-identification], take its coefficient tower $B\to A\to S$ to be
$O_Z\xrightarrow{1}O_Z\xrightarrow{a_Z}A_Z$. Its scalar-first computation identifies
$Q_{O_Z}(A_Z\otimes Q)$ with $\operatorname{Res}_{a_Z}T_ZK$. Composing gives the
augmentation-induced isomorphism
$\beta_{Z,K}:P_Z\otimes^LK\xrightarrow{\sim}\operatorname{Res}_{a_Z}T_ZK$. All arrows are the
specified localization/tensor comparisons; the resolving equivalence
[lem-weil-pbc-site-derived-tensor-descent] makes them natural in $K$ and independent of $Q$. In
particular we do not claim that $P_Z\otimes C\to A_Z\otimes C$ is a quasi-isomorphism for an
arbitrary $C$.

5. For $h:Z'\to Z$, the monoidal composition comparison of
[lem-weil-pbc-profinite-point-pullback] identifies $h^{-1}O_Z$ with $O_{Z'}$, $h^{-1}A_Z$ with
$A_{Z'}$, and the pulled-back maps $\phi_Z,q_Z$ with $\phi_{Z'},q_{Z'}$. Thus it identifies the
augmented complexes themselves. The canonical pullback/scalar comparison is the balancing-arrow
comparison on K-flat representatives by [lem-sfb-kflat-scalar-comparison-normalization]; in
particular it sends $1\otimes x$ to $1\otimes h^{-1}x$ and needs no flatness of $a$. Choose
$Q\to C$ as in step 4. By [lem-weil-pbc-ringed-pullback-preserves-kflat] (with $c$ the
identification $h^{-1}O_Z\cong O_{Z'}$), $h^*Q=h^{-1}Q$ is again K-flat with flat terms, so it
is a resolution of $h^*K$ usable in step 4 over $Z'$, and $h^{-1}\operatorname{Tot}(P_Z\otimes
Q)=\operatorname{Tot}(h^{-1}P_Z\otimes h^{-1}Q)$ represents the canonical tensor pullback
isomorphism $h^*(P_Z\otimes^LK)\cong P_{Z'}\otimes^Lh^*K$ of
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Naturality of tensor with respect to the
augmentation makes the square for $h^*\beta_{Z,K}$ and $\beta_{Z',h^*K}$ commute on these
representatives, hence in the derived category by [lem-weil-pbc-site-derived-tensor-descent].
These are precisely the comparisons of [det-prop-scalar-six-pullback](1). Identity and
composite $h$ obey the same square because the cited point-pullback and scalar-comparison
statements give their identity and composition coherence.

6. To compare the actual internal-module arrows with ringed-site arrows, use
[lem-pd-section-derived-pushpull-normalization] for both condensed rings $\underline
O,\underline A$. It identifies their unbounded derived geometric adjunctions, including the
counits. Use [lem-pd-section-derived-tensor-normalization] for the actual pullback tensor
isomorphism and [lem-sfb-internal-section-scalar-adjunction] for derived extension and
restriction with their units and counits. Thus it suffices to compute the arrow in section-ring
module categories. The hypotheses here are only smallness of the sites and pulled-back
coefficients; the monoidal coefficient identifications from the preceding step give the
cartesian coefficient square required for [lem-weil-pbc-ring-sheaf-change-adjunction]. That
lemma is stated for the adjunctions $Lf^*\dashv Rf_*$ of [def-weil-pbc-proetale-operations],
with $c$ the coefficient identification from the point, while the normalization above lands in
the ringed derived pullback [lem-weil-pbc-ringed-topoi-derived-pullback] and K-injective direct
image of the section model. These coincide: both inverse images are the same tensor-formula
pullback $f^{-1}(-)\otimes_{f^{-1}R_Y,c}R_X$ with the same ordinary module adjunction, exact
because $c$ is invertible, so derived termwise on every complex; both direct images are
computed on K-injective resolutions. Hence both derived adjunctions are the unique canonical
bijection of [lem-pc-pre-derived-adjoint-functors-general] induced by that one ordinary
adjunction, for $R=O$ and for $R=A$. Write $r_Z=\operatorname{Res}_{a_Z}$ and
$d:r_YRf_{*,A}\cong Rf_{*,O}r_X$ for its specified direct-image comparison.

7. Put $L=f_O^*$, $R=Rf_{*,O}$ and $B=P_Y$, so $LB=P_X$. Let $t=T_X(\varepsilon_K)c_{f,RK}$,
the $A$-adjunct defining $\gamma_{f,K}$. The adjunct-compatibility equation of
[lem-weil-pbc-ring-sheaf-change-adjunction] says that $d\,r_Y(\gamma)$ is the $O$-adjunct of
$r_X(t)b^{-1}$, where $b:r_Xf_A^*\cong Lr_Y$. Under $L\beta_{Y,RK}$, the pullback square in
step 5 identifies $r_X(c)b^{-1}L\beta_{Y,RK}$ with $\beta_{X,LRK}$ following the tensor
pullback isomorphism $L(B\otimes^LRK)\cong P_X\otimes^LLRK$. Naturality of $\beta$ for
$\varepsilon_K:LRK\to K$ now gives
$$r_X(t)b^{-1}L\beta_{Y,RK}=\beta_{X,K}(1_{P_X}\otimes\varepsilon_K)\mu,$$ where $\mu$ is that
tensor pullback isomorphism. The normalization of $c$ used here is exactly
[lem-sfb-kflat-scalar-comparison-normalization], not a freely chosen isomorphism. By the
natural adjunction bijection, the conjugate $R(\beta_{X,K}^{-1})d\,r_Y(\gamma)\beta_{Y,RK}$ is
therefore the adjunct of $(1_{P_X}\otimes\varepsilon_K)\mu$. This is the scalar-first
projection map in the statement, the symmetric form of
[lem-weil-pbc-ringed-projection-mate-exact]. The tensor symmetries and unit comparisons are the
canonical ones of [lem-sf-ringed-derived-native-tensor].

8. For the projection transformation with fixed $K$,
[lem-weil-pbc-ringed-projection-mate-exact] says that its functors in the coefficient complex
are exact, that it is a morphism of distinguished triangles including the connecting square,
and that its component at the unit $O_Y[0]$ is the identity. Finite additivity makes its
component at $O_Y^r[0]$ the sum of $r$ identities. Apply it to the cone triangle of
$\phi_Y:O_Y^r[0]\to O_Y^r[0]$, whose third object is $P_Y$ by step 3. The first two components
are isomorphisms, so [lem-sf-triangle-morphism-iso] makes its third component an isomorphism.
The scalar-first variant is its conjugate by the canonical braidings of
[lem-sf-ringed-derived-native-tensor], hence is also invertible. This is precisely the
finite-sums-and-cone argument of the unit route; it uses exactness, not commutation of $Rf_*$
with arbitrary colimits.

9. All the $\beta$ and $d$ in step 7 are isomorphisms. Step 8 consequently proves that
$r_Y(\gamma_{f,K})$ is an isomorphism. Restriction reflects isomorphisms by
[lem-weil-pbc-ring-sheaf-change-adjunction], so $\gamma_{f,K}$ is itself an isomorphism in
$D(A_Y)$. If $A=0$ all these complexes and maps are zero, and the rank-zero construction gives
the same conclusion. At no step was $K$ bounded, $A$ flat, or $f$ proper, quasi-compact or
constructible; only the prescribed small-site and continuous coefficient hypotheses were used.
-/
theorem integralFiniteScalarPerfectModel
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (a : Padic.coefficientExtensionIntegers ell E →+* A)
    (ha : @Continuous _ _ (Padic.coefficientExtensionIntegersTopology ell E) inferInstance a)
    (_hpow : ∃ n : ℕ, (ell : A) ^ n = 0) (D : ScalarSixPullbackData.{u}) :
    @PerfectModel (Padic.coefficientExtensionIntegers ell E) A
      inferInstance inferInstance (Padic.coefficientExtensionIntegersTopology ell E) inferInstance
      (by
        let := spectralNorm.normedField (Padic ell) E
        exact inferInstanceAs (IsTopologicalRing (Padic.coefficientExtensionIntegers ell E)))
      inferInstance a ha D := by
  classical
  let := Padic.coefficientExtensionIntegersTopology ell E
  let : IsTopologicalRing (Padic.coefficientExtensionIntegers ell E) := by
    let := spectralNorm.normedField (Padic ell) E
    exact inferInstanceAs (IsTopologicalRing (Padic.coefficientExtensionIntegers ell E))
  let O := Padic.coefficientExtensionIntegers ell E
  let := a.toAlgebra
  let := continuousSMul_of_algebraMap O A ha
  let : HasFiniteBiproducts (PointModules (condensed O)) := .of_hasFiniteProducts
  obtain ⟨r, q, φ, hq, hφ, hex, hmatrix, ⟨e⟩, hzero, F, G, h, t, hF, hG, ht, hS⟩ :=
    perfectModelArithmetic_of_finite_integral ell E A a ha _hpow
  refine ⟨r, q, φ, hq, hφ, hex, hmatrix, ⟨e⟩, hzero, F, G, h, t,
    hF, hG, ht, hS, ?_⟩
  obtain ⟨hflat, β, hnorm, hpull, hmate⟩ :=
    derivedAssertions_of_finite_integral_resolution D (condensedMap a ha) (ShortComplex.mk F G h) t
      hS r e e
  refine ⟨hflat, β, hnorm, hpull, hmate, ?_⟩
  intro X Y f K
  have hp := finiteFreeScalarProjection (condensed O) (ShortComplex.mk F G h) r e e f K
  refine ⟨hp, ?_⟩
  have : (restriction (condensedMap a ha) Y).ReflectsIsomorphisms :=
    restrictionReflectsIsomorphisms (condensedMap a ha) Y
  have hc : IsIso ((β Y).hom.app ((moduleObjectDerivedPushforward (condensed O).X f).obj K) ≫
      (restriction (condensedMap a ha) Y).map (gamma D (condensedMap a ha) f K) ≫
      (restrictionPush D (condensedMap a ha) f).hom.app
        ((scalarSixChange (condensedMap a ha) X).obj K) ≫
      (moduleObjectDerivedPushforward (condensed O).X f).map ((β X).inv.app K)) := by
    rw [hmate X Y f K]
    exact hp
  have : IsIso ((restriction (condensedMap a ha) Y).map
      (gamma D (condensedMap a ha) f K)) := by
    have htail := (isIso_comp_left_iff ((β Y).hom.app
      ((moduleObjectDerivedPushforward (condensed O).X f).obj K)) _).mp hc
    exact (isIso_comp_right_iff
      ((restriction (condensedMap a ha) Y).map (gamma D (condensedMap a ha) f K))
      ((restrictionPush D (condensedMap a ha) f).hom.app
        ((scalarSixChange (condensedMap a ha) X).obj K) ≫
        (moduleObjectDerivedPushforward (condensed O).X f).map ((β X).inv.app K))).mp
      (by simpa only [Category.assoc] using htail)
  exact isIso_of_reflects_iso _ (restriction (condensedMap a ha) Y)

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
