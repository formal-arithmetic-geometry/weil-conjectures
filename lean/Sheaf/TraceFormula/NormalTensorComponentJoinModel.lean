/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Sheaf.TraceFormula.ComponentQuotientIndEtale
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.TraceFormula.EtaleNormalDomainFiniteFactors
import Sheaf.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.RingTheory.EtaleNormalRing
import Sheaf.RingTheory.FilteredColimitNormalRing
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField

/-!
# Normal tensor components realized as embedded joins

Source: Huebner--Schmidt, *The tame site of a scheme*, Theorem 6.3, printed p. 13
(blueprint: lem-trf-normal-tensor-component-join-model).
-/

@[expose] public section
set_option autoImplicit false

universe u v w z

open scoped TensorProduct
open AlgebraicGeometry

namespace Algebra

/-- Normal tensor components of two ordinary henselizations are embedded joins in a
separable closure. Source: Huebner--Schmidt, *The tame site of a scheme*, Theorem 6.3,
printed p. 13 (blueprint: lem-trf-normal-tensor-component-join-model).

Proof (the nine steps of the DAG; write T = H₁ ⊗[P] H₂ and U = T/I_Z):
1. Apply [lem-trf-henselization-prime-ind-etale] to $(P,\mathfrak q_i)$: each structural map $P\to
   H_i$ is ind-etale. Base change in [lem-weil-pbc-ind-etale-stability] makes $H_1\to T$ and $H_2\to
   T$ ind-etale, and composition makes $P\to T$ ind-etale. These are the specified tensor-factor
   maps, using the algebra tensor construction of
   [lem-weil-pbc-algebra-tensor-pushout-universal-property].
2. Apply [lem-trf-component-ind-etale-local-henselian] to the chosen component $Z$: the actual
   quotient $T\to U$ is ind-etale. Compose with the maps of Step 1 using
   [lem-weil-pbc-ind-etale-stability]. Thus $P\to U$ and both $H_i\to U$ are ind-etale, proving the
   final assertion already. The component-ring clause of
   [lem-trf-affine-etale-cover-component-criterion] identifies the underlying space of
   $\operatorname{Spec}U$ with $Z$. In particular $U\ne0$ and its spectrum is connected. No
   assertion about henselianity of $U$ has been used.
3. Choose a small filtered presentation $U=\varinjlim B_\lambda$ by etale $P$-algebras, which exists
   by [def-weil-pbc-ind-etale-algebra]. Each $B_\lambda$ is a normal ring by
   [lem-weil-pbc-etale-over-normal-ring-normal]. The underlying ring diagram also has colimit $U$ by
   [lem-weil-pbc-filtered-colimit-algebras-elementwise]. Apply
   [lem-weil-pbc-filtered-colimit-normal-ring] to conclude that $U$ is a normal ring. This asserts
   normality at prime localizations, and does not yet assert that $U$ is a domain.
4. In the same presentation, suppose $a,b\in U$ satisfy $ab=0$. The elementwise colimit statement
   [lem-pc-filtered-colimit-commrings-elementwise] and filteredness give representatives
   $a_\lambda,b_\lambda$ in one stage; its equality clause lets us pass to a later stage at which
   $a_\lambda b_\lambda=0$. Apply [lem-trf-etale-normal-domain-finite-factors] to that stage to
   write it as a finite product of normal domains $C_j$. By [lem-weil-pbc-spec-clopen-idempotent],
   the only idempotents of $U$ are $0,1$: its spectrum is nonempty and connected, and these
   correspond to the empty and whole clopens. The images of the coordinate idempotents of the finite
   product are orthogonal and sum to $1$, so exactly one is $1$ and all others are $0$. If it is the
   $j$th one, the ring map from that stage to $U$ factors through $C_j$: every element of the other
   factors is its own product with an idempotent mapping to zero. In the domain $C_j$ the projected
   relation gives $a_{\lambda,j}=0$ or $b_{\lambda,j}=0$; hence $a=0$ or $b=0$. Together with
   $U\ne0$ this proves that $U$ is an integral domain.
5. Step 3 and the last sentence of [lem-weil-pbc-normal-domain-of-local-normal] show that the domain
   $U$ is integrally closed in $\operatorname{Frac}(U)$. Also each $H_i$ is a local ring by its
   henselization structure [def-weil-pbc-henselization-at-prime], and is an ind-etale $P$-algebra by
   Step 1. The local colimit theorem [lem-weil-pbc-etale-colimit-normal-local-domain], applied to
   its etale $P$-algebra presentation, therefore makes each $H_i$ a normal integral domain. Its
   hypothesis is a local colimit, not necessarily a strict henselization.
6. The maps $P\to U$ and $H_i\to U$ of Step 2 are weakly etale by
   [lem-weil-pbc-ind-etale-stability], hence flat by [def-weil-pbc-ind-etale-algebra]. For any one
   of their source domains $R$ and $0\ne r\in R$, multiplication $R\xrightarrow{r}R$ is injective.
   The definition [def-weil-pbc-flat-ring-map], with the identifications $R\otimes_RU=U$, says that
   multiplication by the image of $r$ on $U$ is injective. If that image were zero, it would kill
   $1\ne0$ in $U$. Therefore each of the three ring maps is injective. In particular the structural
   map extends to $K\hookrightarrow L=\operatorname{Frac}(U)$.
7. Put $S=P\setminus\{0\}$ and $V=K\otimes_PU=S^{-1}U$. This identification sends $(p/s)\otimes u$
   to $pu/s$, and the inverse sends $u/s$ to $(1/s)\otimes u$; the tensor relations and the
   localization fraction relation show these are inverse maps. By
   [lem-weil-pbc-ind-etale-stability], base change makes $K\to V$ weakly etale. The map $V\to L$ is
   a localization: inverting all nonzero images $u/1$ of $u\in U$ gives fractions
   $(a/s)/(b/t)=at/(sb)$, precisely all fractions of the domain $U$, and the usual
   cross-multiplication equality is the same. Thus [lem-weil-pbc-localization-ring-weakly-etale] and
   composition in [lem-weil-pbc-ind-etale-stability] make $K\to L$ weakly etale. Apply
   [lem-weil-pbc-weakly-etale-field-separable] to these fields to conclude that $L/K$ is separable
   algebraic.
8. Apply [lem-weil-pbc-separable-extension-embeds-separably-closed] to the separable algebraic field
   extension $L/K$ and the fixed separable closure $K^{\mathrm{sep}}$, which is separably closed. It
   supplies a $K$-algebra embedding $L\hookrightarrow K^{\mathrm{sep}}$. Restrict it along the
   canonical inclusion $U\hookrightarrow L$ to get the required $P$-embedding. Composing with the
   injective maps of Step 6 gives the two stated embedded copies of $H_i$.
9. Let $\jmath:U\hookrightarrow K^{\mathrm{sep}}$ be this embedding and let $J$ be the subring
   generated by the images of $H_1,H_2$ in it. The algebra tensor multiplication of
   [lem-weil-pbc-algebra-tensor-pushout-universal-property] gives $a\otimes b=(a\otimes1)(1\otimes
   b)$. Every element of $T$ is a finite sum of pure tensors, so its image under
   $T\twoheadrightarrow U\xrightarrow{\jmath}K^{\mathrm{sep}}$ lies in $J$. Surjectivity of the
   first map gives $\jmath(U)\subseteq J$. Conversely both images of $H_i$ lie in $\jmath(U)$, which
   is a subring, so $J\subseteq\jmath(U)$. This proves the claimed equality of subrings for the
   actual quotient maps.
-/
theorem normalTensorComponentJoinModel
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (q₁ q₂ : Ideal P) [q₁.IsPrime] [q₂.IsPrime]
    (H₁ : Type v) (H₂ : Type w) [CommRing H₁] [CommRing H₂]
    [Algebra (Localization.AtPrime q₁) H₁]
    [Algebra (Localization.AtPrime q₂) H₂]
    [HenselianLocalRing H₁] [HenselianLocalRing H₂]
    [Algebra P H₁] [Algebra P H₂]
    [IsScalarTower P (Localization.AtPrime q₁) H₁]
    [IsScalarTower P (Localization.AtPrime q₂) H₂]
    (hH₁ : Algebra.IsHenselizationAtPrime' P q₁ H₁)
    (hH₂ : Algebra.IsHenselizationAtPrime' P q₂ H₂)
    (Ksep : Type z) [Field Ksep] [Algebra (FractionRing P) Ksep]
    [IsSepClosure (FractionRing P) Ksep] :
    ∀ x : PrimeSpectrum (H₁ ⊗[P] H₂),
      ∃ (e : (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x) →+* Ksep),
        Function.Injective e ∧
        IsDomain (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x) ∧
        IsIntegrallyClosed (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x) ∧
        Function.Injective
          ((Ideal.Quotient.mk (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
            (algebraMap P (H₁ ⊗[P] H₂))) ∧
        Function.Injective
          ((Ideal.Quotient.mk (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
            (((Algebra.TensorProduct.includeLeft : H₁ →ₐ[P] H₁ ⊗[P] H₂).toRingHom))) ∧
        Function.Injective
          ((Ideal.Quotient.mk (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
            (((Algebra.TensorProduct.includeRight : H₂ →ₐ[P] H₁ ⊗[P] H₂).toRingHom))) ∧
        (∃ (kmap : FractionRing P →+*
            FractionRing (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x)),
          Function.Injective kmap ∧
          kmap.comp (algebraMap P (FractionRing P)) =
            (algebraMap (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x)
              (FractionRing (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x))).comp
              ((Ideal.Quotient.mk
                (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
                (algebraMap P (H₁ ⊗[P] H₂))) ∧
          @Algebra.IsAlgebraic (FractionRing P)
            (FractionRing (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x))
            _ _ (RingHom.toAlgebra kmap) ∧
          @Algebra.IsSeparable (FractionRing P)
            (FractionRing (AlgebraicGeometry.componentRing (H₁ ⊗[P] H₂) x))
            _ _ (RingHom.toAlgebra kmap)) ∧
        e.comp ( (Ideal.Quotient.mk (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
            (algebraMap P (H₁ ⊗[P] H₂))) =
          (algebraMap (FractionRing P) Ksep).comp (algebraMap P (FractionRing P)) ∧
        (Subring.closure
            (Set.range (e.comp
              ((Ideal.Quotient.mk
                (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
                ((Algebra.TensorProduct.includeLeft : H₁ →ₐ[P] H₁ ⊗[P] H₂).toRingHom))) ∪
             Set.range (e.comp
              ((Ideal.Quotient.mk
                (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
                ((Algebra.TensorProduct.includeRight :
                  H₂ →ₐ[P] H₁ ⊗[P] H₂).toRingHom)))) : Set Ksep) =
          Set.range e ∧
        RingHom.IndEtaleAcrossUniverses
          ((Ideal.Quotient.mk (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
            ((Algebra.TensorProduct.includeLeft : H₁ →ₐ[P] H₁ ⊗[P] H₂).toRingHom)) ∧
        RingHom.IndEtaleAcrossUniverses
          ((Ideal.Quotient.mk (AlgebraicGeometry.componentIdeal (H₁ ⊗[P] H₂) x)).comp
            ((Algebra.TensorProduct.includeRight : H₂ →ₐ[P] H₁ ⊗[P] H₂).toRingHom)) := by
  sorry

end Algebra
