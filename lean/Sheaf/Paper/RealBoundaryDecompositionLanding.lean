/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.HenselianResidueGaloisAction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import Mathlib.RingTheory.Localization.FractionRing
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# The local decomposition homomorphism and its subgroup inclusions

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-boundary,
d-real-boundary, decomposition homomorphism clause.
(blueprint: lem-real-boundary-decomposition-landing)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale
open scoped FintypeCatDiscrete

namespace RealSheaves

/-- The local decomposition homomorphism, with its geometric and Weil landing properties.
Source: blueprint main-20261015, d-real-boundary, decomposition homomorphism clause.
(blueprint: lem-real-boundary-decomposition-landing)

The henselization is presented at the maximal ideal of the local stalk (localizing
there does not change the stalk). Its fraction field and algebraic closure are chosen
models of the fields in the source. The residue closure is arbitrary, with compatibility
given by the chosen identification
e with the integral closure residue field, as in lem-real-henselian-residue-galois-action.
The maps a and r are
specified on every element by ha and hr, so r is precisely the residue homomorphism,
not an arbitrary homomorphism. Phi is characterized as inverse cardinality Frobenius;
the residue fields of the stalk and its ordinary henselization are canonically isomorphic.
The equation hxi specifies the canonical local generic point's factorization through U0.

The groups G0 and G are small profinite models, identified with the automorphism
fundamental groups by the continuous multiplicative equivalences e0 and eG (the
explicit toAutContinuousMulEquiv interface). This does not assume extra connectedness.

The first conclusion characterizes theta by the stated conjugation formula, expressed
on morphisms Spec Omega -> P after transporting back along gamma. The second conclusion
is membership in the image of pi1(U) under pullback and its canonical fibre identification.
The last uses MonoidHom.weilGroup, the very fibre-product definition underlying the
recorded scheme Weil group; existence of its integer coordinate is membership in the
inverse image of the Frobenius cyclic subgroup.

Proof, following the node's seven steps:
Step 1: The projection $C=C_0\times_{k_0}k\to C_0$ is surjective by surjectivity for a field
extension and its preservation under base change. Thus $C$ is nonempty, since $C_0$ is; $C$ is
connected by [d-real-setup], and its continuous surjective image $C_0$ is connected too. On
affine charts, the characterization of smooth scheme morphisms by smooth ring maps and the
smooth-ring base-change theorem show that $C$ is smooth over $k$. Finite type of $C$ follows
directly by tensoring the finitely many generators of each chart in a finite affine cover of
$C_0$. Both $C_0$ and $C$ are Noetherian by the finite-type-over-Noetherian theorem, since the
spectra of fields are Noetherian. Smooth algebras over a field have regular local rings, so
both schemes are regular. The regular-Noetherian-connected irreducibility statement therefore
makes $C_0$ and $C$ irreducible. This uses no dimension invariance under field extension.

Step 2: The open $U\subset C$ contains the chosen point $\bar u$, so it is nonempty. A nonempty
open of an irreducible space is irreducible: any two nonempty relatively open subsets are
nonempty opens of the ambient irreducible space and intersect. Thus $U$ is connected, and $U_0$
is geometrically connected. The open $U_0$ is quasi-compact because $C_0$ is Noetherian, and
locally of finite type over $k_0$ by its affine charts; hence it is of finite type. It is
separated because its diagonal is the restriction of the separated diagonal of $C_0$. These
verify the Weil-group hypotheses. Since $C_0$ is irreducible of dimension one, every nongeneric
point is closed: a further proper specialization would give a chain of length two after
adjoining the generic point. The proper closed complement $S_0$ omits the generic point, so $s$
is closed. Applying the closed-point field theorem to $C_0/k_0$ gives $e_s=[k_s:k_0]\geq1$
finite, and therefore $|k_s|=q^{e_s}$.

Step 3: For every cover $P\to U_0$, precomposition with $\operatorname{Spec}(\sigma)$ preserves
the fibre, since $\sigma$ fixes $K_s$. For a morphism of covers $h:P\to Q$, associativity gives
$h\circ a_{\sigma,P}(z)=a_{\sigma,Q}(h\circ z)$. Also
$\operatorname{Spec}(\tau)\circ\operatorname{Spec}(\sigma)=\operatorname{Spec}(\sigma\tau)$, so
$a_{\sigma,P}a_{\tau,P}=a_{\sigma\tau,P}$, with identity $a_1$ and inverse $a_{\sigma^{-1}}$.
Hence $a_\sigma$ is a natural automorphism of the local fibre functor. Conjugating its
components by the natural bijections $\gamma_P$ gives a natural automorphism of $F_{\bar u}$
and preserves products and identity. This is precisely an element
$\theta_s(\sigma)\in\pi_1(U_0,\bar u)$.

Step 4: The homomorphism is continuous in the Krull topology. A point of the finite geometric
fibre of $P$ is given by a homomorphism from the finite etale $K_s$-algebra of
$P\times_{U_0}\operatorname{Spec}K_s$ to $\overline K_s$. Choose finitely many algebra
generators; their images are algebraic over $K_s$. The subgroup fixing these finitely many
elements is open by definition of the Krull topology and fixes that point. Since the fibre is
finite, the kernel of its permutation action is a finite intersection of such open stabilizers.
Thus each component $\sigma\mapsto a_{\sigma,P}$ is continuous. Conjugation by the fixed finite
permutation $\gamma_P$ preserves continuity, so the product-induced topology in the definition
of $\operatorname{Aut}(F_{\bar u})$ proves continuity of $\theta_s$. Pullback of a cover along
$\operatorname{Spec}K_s\to U_0$ identifies its local fibre by projection. The characterization
of $f_*$ in [lem-galois-pi1-functoriality] therefore gives exactly the same permutations;
subsequent conjugation by $\gamma$ gives the displayed formula. This also proves the claimed
agreement with the functorial map.

Step 5: Apply equivariant reduction to $R=\mathcal O_{C_0,s}^h$, $K=K_s$ and $\Omega=\overline
K_s$. The henselization $H$ is henselian local by definition. To check its residue field, put
$A=\mathcal O_{C_0,s}$. The field $k_s=A/\mathfrak m_A$ is henselian: its maximal ideal is
zero, so idempotent lifting modulo that ideal is the identity. The universal property of $H$
applied to the local residue map $A\to k_s$ gives a local map $H\to k_s$ extending it. On
residue fields the composite $k_s\to\kappa(H)\to k_s$ is the identity. The second arrow is an
injective field homomorphism, and its image contains $k_s$, so these are inverse isomorphisms.
Thus $\kappa(H)=k_s$ under the structural identification. Let $k'\subset\overline K_s$ be the
elements algebraic over $k_0$. Reduction gives $t:k'\xrightarrow{\sim}\overline{k_s}$ and the
equality $\sigma|_{k'}=t^{-1}r_s(\sigma)t$. On a constant cover
$P_L=U_0\times_{k_0}\operatorname{Spec}L$, with $L/k_0$ finite, the local fibre is the set of
$k_0$-embeddings $L\to\overline K_s$, all landing in $k'$, and $a_\sigma$ is postcomposition by
$\sigma|_{k'}$. Thus this displayed equality computes the local action on every finite constant
cover directly. No identification of the chosen path with a path over $k_0$ is imposed.

Step 6: If $\sigma\in I_s$, the equality in step 5 says that $\sigma|_{k'}=1$. If $\sigma\in
W(K_s)$, write $r_s(\sigma)=\Phi_s^n$ for $n\in\mathbf Z$ and put $m=e_sn$. With
$\Phi'_0=(x\mapsto x^q)^{-1}$ on $k'$, the definition of geometric Frobenius gives
$t^{-1}\Phi_s t=(\Phi'_0)^{e_s}$, since $|k_s|=q^{e_s}$. Hence $\sigma|_{k'}=(\Phi'_0)^m$. For
each finite extension $L/k_0$, let $b_{m,L}$ be the cover automorphism
$\operatorname{id}_{U_0}\times\operatorname{Spec}((x\mapsto x^q)^{-m}|_L)$ of $P_L$. If a local
fibre point corresponds to $\lambda:L\to k'$, its image under $a_\sigma$ is
$(\Phi'_0)^m\lambda=\lambda(x\mapsto x^q)^{-m}|_L$, the image under $b_{m,L}$. Naturality of
$\gamma$ for the morphism $b_{m,L}$ therefore transports this to the same deck transformation
on the fibre at $\bar u$. At $\bar u$ it is the permutation induced by $\Phi_0^m$, where
$\Phi_0=(x\mapsto x^q)^{-1}$ on the fixed $k$. Since the arithmetic projection
$h:\pi_1(U_0,\bar u)\to\operatorname{Gal}(k/k_0)$ is defined on these constant covers, we
obtain $h(\theta_s(\sigma))=\Phi_0^{e_sn}$. For inertia the identical argument uses $b_{0,L}=1$
and gives $h(\theta_s(\sigma))=1$. All formulas hold for negative $n$ as well, using inverse
field automorphisms.

Step 7: For $\sigma\in W(K_s)$, the equality just proved puts $h(\theta_s(\sigma))$ in
$\langle\Phi_0\rangle$, so the inverse-image definition of the Weil group gives
$\theta_s(\sigma)\in W(U_0,\bar u)$, of degree $e_sn$. In particular if $\sigma\in I_s$, its
image has trivial arithmetic projection, belongs to the Weil group, and has degree zero. The
exact Weil degree sequence identifies its degree-zero kernel with the image of $\pi_1(U,\bar
u)$. Therefore $\theta_s(I_s)\subseteq\pi_1(U,\bar u)$, and $\theta_s(W(K_s))\subseteq
W(U_0,\bar u)$ as asserted.
-/
theorem exists_boundary_decomposition_landing
    (D : Setup.{u, v}) (C₀ : Scheme.{u}) [C₀.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀) (hS : (U₀ : Set C₀)ᶜ.Finite)
    (s : C₀) (hs : s ∉ U₀)
    (H : Type u) [CommRing H] [HenselianLocalRing H] [IsDomain H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    [Algebra (C₀.presheaf.stalk s) H]
    [IsScalarTower (C₀.presheaf.stalk s)
      (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    (hH : Algebra.IsHenselizationAtPrime' (C₀.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s)) H)
    (K : Type u) [Field K] [Algebra H K] [IsFractionRing H K]
    [Algebra (C₀.presheaf.stalk s) K] [IsScalarTower (C₀.presheaf.stalk s) H K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra H Ω] [IsScalarTower H K Ω]
    [IsLocalRing (integralClosure H Ω)]
    [IsLocalHom (algebraMap H (integralClosure H Ω))]
    [IsAlgClosure (IsLocalRing.ResidueField H)
      (IsLocalRing.ResidueField (integralClosure H Ω))]
    (a : (Ω ≃ₐ[K] Ω) →* (integralClosure H Ω ≃ₐ[H] integralClosure H Ω))
    (ha : ∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure H Ω), (a σ b : Ω) = σ (b : Ω))
    (Ωr : Type w) [Field Ωr] [Algebra (IsLocalRing.ResidueField H) Ωr]
    [IsAlgClosure (IsLocalRing.ResidueField H) Ωr]
    (e : IsLocalRing.ResidueField (integralClosure H Ω) ≃ₐ[IsLocalRing.ResidueField H] Ωr)
    (r : (Ω ≃ₐ[K] Ω) →* (Ωr ≃ₐ[IsLocalRing.ResidueField H] Ωr))
    (hr : ∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure H Ω),
      r σ (e (IsLocalRing.residue (integralClosure H Ω) b)) =
        e (IsLocalRing.residue (integralClosure H Ω) (a σ b)))
    (Φ : Ωr ≃ₐ[IsLocalRing.ResidueField H] Ωr)
    (hΦ : ∀ x : Ωr,
      Φ.symm x = x ^ Nat.card (C₀.residueField s))
    (ξ : Spec (.of K) ⟶ U₀.toScheme)
    (hξ : ξ ≫ U₀.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (C₀.presheaf.stalk s) K)) ≫
        C₀.fromSpecStalk s)
    (Ωu : Type u) [Field Ωu] [IsSepClosed Ωu]
    (b : Spec (.of Ωu) ⟶ D.geometricCurve U₀.toScheme)
    (G₀ G : Type u) [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
    [CompactSpace G₀] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (e₀ : G₀ ≃ₜ* Aut (fiber (b ≫ CategoryTheory.Limits.pullback.fst
      (U₀.toScheme ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))
    (eG : G ≃ₜ* Aut (fiber b))
    (γ : fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ) ≅
      fiber (b ≫ CategoryTheory.Limits.pullback.fst (U₀.toScheme ↘ Spec (.of D.k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) :
    ∃ θ : (Ω ≃ₐ[K] Ω) →* G₀,
      Continuous θ ∧
      (∀ (σ : Ω ≃ₐ[K] Ω) (P : U₀.toScheme.FiniteEtale)
          (z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ)).obj P),
        (γ.inv.app P ((e₀ (θ σ)).hom.app P (γ.hom.app P z))).left =
          Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, σ ∈ r.ker →
        ∃ g : G,
          ∀ (P : U₀.toScheme.FiniteEtale)
            (z : (fiber b).obj ((AlgebraicGeometry.Scheme.FiniteEtale.pullback
              (CategoryTheory.Limits.pullback.fst (U₀.toScheme ↘ Spec (.of D.k₀))
                (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).obj P)),
            (e₀ (θ σ)).hom.app P ((pullbackFiberIso _ b).hom.app P z) =
              (pullbackFiberIso _ b).hom.app P
                ((eG g).hom.app ((AlgebraicGeometry.Scheme.FiniteEtale.pullback
                  (CategoryTheory.Limits.pullback.fst (U₀.toScheme ↘ Spec (.of D.k₀))
                    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).obj P) z)) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, (∃ n : ℤ, r σ = Φ ^ n) →
        ∃ m : ℤ, (e₀ (θ σ), Multiplicative.ofAdd m) ∈
          (constantCoverAction (U₀.toScheme ↘ Spec (.of D.k₀))
            (b ≫ CategoryTheory.Limits.pullback.fst (U₀.toScheme ↘ Spec (.of D.k₀))
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
            (Aut (fiber (b ≫ CategoryTheory.Limits.pullback.fst
              (U₀.toScheme ↘ Spec (.of D.k₀))
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))))).weilGroup
            (geometricFrobenius (U₀.toScheme ↘ Spec (.of D.k₀))
              (b ≫ CategoryTheory.Limits.pullback.fst (U₀.toScheme ↘ Spec (.of D.k₀))
                (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))) := by
  sorry

end RealSheaves
