/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
/-!
# Affine charts of universally exact sequences modulo powers
Source: Stacks Project, Divisors, Tag 080W, opening affine reduction and
universal injectivity modulo powers
(blueprint: lem-trf-universal-exact-affine-power-reduction).
Affine opens are presented by open immersions from spectra. The quotient sequence
below is over the quotient ring; its equivalences with the actual submodule quotients
and its squares with both arrows specify the quotient maps, not just the objects.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Limits

/-- Restrict a base-changed module to its affine chart, using tensor pullback.
Source: Stacks, Tags 080W and 01I9
(blueprint: lem-trf-universal-exact-affine-power-reduction). -/
noncomputable def universalExactAffineChart {X S B : Scheme.{u}}
    (f : X ⟶ S) (t : B ⟶ S) (C : CommRingCat.{u})
    (z : Spec C ⟶ CategoryTheory.Limits.pullback f t) : X.Modules ⥤ (Spec C).Modules :=
  tensorPullback (pullback.fst f t) ⋙ tensorPullback z

/-- Sections of the restricted, base-changed module on the affine chart.
Source: Stacks, Tags 080W and 01IB
(blueprint: lem-trf-universal-exact-affine-power-reduction). -/
noncomputable def universalExactAffineSections {X S B : Scheme.{u}}
    (f : X ⟶ S) (t : B ⟶ S) (C : CommRingCat.{u})
    (z : Spec C ⟶ CategoryTheory.Limits.pullback f t) : X.Modules ⥤ ModuleCat.{u} C :=
  universalExactAffineChart f t C z ⋙ moduleSpecΓFunctor

/-- The canonical composition comparison from direct pullback to restriction of the
base-changed chart module. It is fixed by the section-normalized adjunctions.
Source: Stacks, Tags 0097 and 080W
(blueprint: lem-trf-universal-exact-affine-power-reduction). -/
noncomputable def universalExactAffineChartComposition {X S B T : Scheme.{u}}
    (f : X ⟶ S) (t : B ⟶ S) (C : CommRingCat.{u})
    (z : Spec C ⟶ CategoryTheory.Limits.pullback f t) (q : T ⟶ Spec C) :
    tensorPullback (q ≫ (z ≫ pullback.fst f t)) ≅
      universalExactAffineChart f t C z ⋙ tensorPullback q :=
  tensorPullbackSectionComp q (z ≫ pullback.fst f t) ≪≫
    Functor.isoWhiskerRight (tensorPullbackSectionComp z (pullback.fst f t)) (tensorPullback q)

/-- The quotient-ring test scheme's map to the original base.
Source: Stacks, Tag 080W
(blueprint: lem-trf-universal-exact-affine-power-reduction). -/
noncomputable def universalExactPowerTest {S B : Scheme.{u}} (t : B ⟶ S)
    (A : CommRingCat.{u}) (v : Spec A ⟶ B) (a : A) (n : ℕ) :
    Spec (.of (A ⧸ Ideal.span {a ^ n})) ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ n}))) ≫ v ≫ t

set_option maxHeartbeats 800000 in
-- The full statement elaborates three normalized comparisons and both sequence maps.
/-- A universally short exact quasi-coherent sequence is short exact on every affine
base-change chart, canonically agrees with its tilde sequence, and is injective
modulo every power of a base scalar. The quotient-ring and quotient-module
comparisons include their formulas and both sequence arrows.
Source: Stacks Project, Divisors, Tag 080W; Schemes, Tags 01IB, 01IC, 01I9,
01JQ and 01JY (blueprint: lem-trf-universal-exact-affine-power-reduction).
Proof:
1. Apply the universal hypothesis to B. Pullback preserves quasi-coherence
   (lem-weil-pbc-module-pullback-quasi-coherent). The affine adjunction counits
   (lem-weil-pbc-affine-tilde-gamma-adjunction) are isomorphisms; their naturality
   gives the two displayed squares.
2. On the affine chart, quasi-coherent images and cokernels have their sectionwise
   descriptions (lem-weil-pbc-quasi-coherent-module-cokernel-image). Thus the first
   section map is injective, the middle kernel is its image, and the last is surjective.
3. For n, base change the open chart along Spec(A/(a^n)). Fibre-product pasting
   identifies its ambient scheme with X times_S Spec(A/(a^n)); open immersions
   are stable under base change (lem-weil-pbc-open-immersion-base-change).
4. The affine fibre-product formula (lem-weil-pbc-fibre-product-affine-spectra)
   and c tensor r-bar -> class(c*r) give C tensor_A A/(a^n) = C/(alpha^n).
   The inverse is class(c) -> c tensor 1, well defined because alpha^n tensor 1=0.
5. Tensor-pullback composition identifies the restricted original sequence with
   the pullback of the chart sequence. Pull back its counits and use the natural
   tilde comparison (lem-weil-pbc-tilde-pullback-base-change).
6. The quotient tensor equivalence (lem-weil-pbc-tensor-over-quotient-ring) sends
   c-bar tensor m to class(c*m), with inverse class(m) -> 1 tensor m.
   Naturality gives precisely the quotient maps induced by both original arrows.
7. Apply universal exactness to the test scheme and step 2 to its affine open.
   The quotient first arrow is injective. Its kernel criterion is exactly the
   divisibility implication, and conversely that implication kills its kernel.
   For n=0 both quotients and the test scheme are zero or empty. Neither affine
   f nor flatness of C over A was used. -/
theorem universalExact_affine_power_reduction
    {X S B : Scheme.{u}} (f : X ⟶ S) (t : B ⟶ S)
    (F : ShortComplex X.Modules)
    [F.X₁.IsQuasicoherent] [F.X₂.IsQuasicoherent] [F.X₃.IsQuasicoherent]
    (hF : F.ShortExact)
    (hbase : ∀ (T : Scheme.{u}) (s : T ⟶ S),
      ∃ h : (tensorPullback (pullback.fst f s)).map F.f ≫
          (tensorPullback (pullback.fst f s)).map F.g = 0,
        (ShortComplex.mk ((tensorPullback (pullback.fst f s)).map F.f)
          ((tensorPullback (pullback.fst f s)).map F.g) h).ShortExact)
    (A C : CommRingCat.{u}) [Algebra A C]
    (v : Spec A ⟶ B) [IsOpenImmersion v]
    (z : Spec C ⟶ CategoryTheory.Limits.pullback f t) [IsOpenImmersion z]
    (hz : z ≫ pullback.snd f t =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ v) (a : A) :
    ((tensorPullback (pullback.fst f t)).obj F.X₁).IsQuasicoherent ∧
    ((tensorPullback (pullback.fst f t)).obj F.X₂).IsQuasicoherent ∧
    ((tensorPullback (pullback.fst f t)).obj F.X₃).IsQuasicoherent ∧
    IsIso ((universalExactAffineChart f t C z).obj F.X₁).fromTildeΓ ∧
    IsIso ((universalExactAffineChart f t C z).obj F.X₂).fromTildeΓ ∧
    IsIso ((universalExactAffineChart f t C z).obj F.X₃).fromTildeΓ ∧
    (tilde.functor C).map ((universalExactAffineSections f t C z).map F.f) ≫
        ((universalExactAffineChart f t C z).obj F.X₂).fromTildeΓ =
      ((universalExactAffineChart f t C z).obj F.X₁).fromTildeΓ ≫
        (universalExactAffineChart f t C z).map F.f ∧
    (tilde.functor C).map ((universalExactAffineSections f t C z).map F.g) ≫
        ((universalExactAffineChart f t C z).obj F.X₃).fromTildeΓ =
      ((universalExactAffineChart f t C z).obj F.X₂).fromTildeΓ ≫
        (universalExactAffineChart f t C z).map F.g ∧
    Function.Injective ((universalExactAffineSections f t C z).map F.f) ∧
    Function.Exact ((universalExactAffineSections f t C z).map F.f)
      ((universalExactAffineSections f t C z).map F.g) ∧
    Function.Surjective ((universalExactAffineSections f t C z).map F.g) ∧
    ∀ n : ℕ,
      ∃ (ρ : (A ⧸ Ideal.span {a ^ n}) →+*
          (C ⧸ Ideal.span {(algebraMap A C a) ^ n}))
        (e : (C ⊗[A] (A ⧸ Ideal.span {a ^ n})) ≃+*
          (C ⧸ Ideal.span {(algebraMap A C a) ^ n}))
        (eZ : CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ n})))) ≅
          Spec (.of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})))
        (w : Spec (.of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) ⟶
          CategoryTheory.Limits.pullback f (universalExactPowerTest t A v a n)),
      (∀ r : A, ρ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap A C r)) ∧
      (∀ (c : C) (r : A), e (c ⊗ₜ[A] Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (c * algebraMap A C r)) ∧
      eZ.inv ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span {(algebraMap A C a) ^ n}))) ∧
      eZ.inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ρ) ∧
      IsOpenImmersion w ∧
      w ≫ pullback.fst f (universalExactPowerTest t A v a n) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span {(algebraMap A C a) ^ n}))) ≫ z ≫ pullback.fst f t ∧
      w ≫ pullback.snd f (universalExactPowerTest t A v a n) =
        Spec.map (CommRingCat.ofHom ρ) ∧
      ∃ Q : ShortComplex
          (ModuleCat.{u} (C ⧸ Ideal.span {(algebraMap A C a) ^ n})),
        Q.ShortExact ∧
        ∃ e₁ : ((ModuleCat.restrictScalars (Ideal.Quotient.mk
              (Ideal.span {(algebraMap A C a) ^ n}))).obj Q.X₁) ≃ₗ[C]
            ((universalExactAffineSections f t C z).obj F.X₁) ⧸
              ((Ideal.span {(algebraMap A C a) ^ n}) •
                (⊤ : Submodule C ((universalExactAffineSections f t C z).obj F.X₁))),
        ∃ e₂ : ((ModuleCat.restrictScalars (Ideal.Quotient.mk
              (Ideal.span {(algebraMap A C a) ^ n}))).obj Q.X₂) ≃ₗ[C]
            ((universalExactAffineSections f t C z).obj F.X₂) ⧸
              ((Ideal.span {(algebraMap A C a) ^ n}) •
                (⊤ : Submodule C ((universalExactAffineSections f t C z).obj F.X₂))),
        ∃ e₃ : ((ModuleCat.restrictScalars (Ideal.Quotient.mk
              (Ideal.span {(algebraMap A C a) ^ n}))).obj Q.X₃) ≃ₗ[C]
            ((universalExactAffineSections f t C z).obj F.X₃) ⧸
              ((Ideal.span {(algebraMap A C a) ^ n}) •
                (⊤ : Submodule C ((universalExactAffineSections f t C z).obj F.X₃))),
        (∀ m : (universalExactAffineSections f t C z).obj F.X₁,
          e₂ (Q.f (e₁.symm (Submodule.Quotient.mk m))) =
            Submodule.Quotient.mk ((universalExactAffineSections f t C z).map F.f m)) ∧
        (∀ m : (universalExactAffineSections f t C z).obj F.X₂,
          e₃ (Q.g (e₂.symm (Submodule.Quotient.mk m))) =
            Submodule.Quotient.mk ((universalExactAffineSections f t C z).map F.g m)) ∧
        ∃ l₁ : (ModuleCat.extendScalars
            (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))).obj
            ((universalExactAffineSections f t C z).obj F.X₁) ≅ Q.X₁,
        ∃ l₂ : (ModuleCat.extendScalars
            (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))).obj
            ((universalExactAffineSections f t C z).obj F.X₂) ≅ Q.X₂,
        ∃ l₃ : (ModuleCat.extendScalars
            (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))).obj
            ((universalExactAffineSections f t C z).obj F.X₃) ≅ Q.X₃,
        ∃ ψ₁ : tilde (R := .of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) Q.X₁ ≅
            (tensorPullback ((Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n})))) ≫
              (z ≫ pullback.fst f t))).obj F.X₁,
        ∃ ψ₂ : tilde (R := .of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) Q.X₂ ≅
            (tensorPullback ((Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n})))) ≫
              (z ≫ pullback.fst f t))).obj F.X₂,
        ∃ ψ₃ : tilde (R := .of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) Q.X₃ ≅
            (tensorPullback ((Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n})))) ≫
              (z ≫ pullback.fst f t))).obj F.X₃,
        (∀ (c : C) (m : (universalExactAffineSections f t C z).obj F.X₁),
          e₁ (l₁.hom (Ideal.Quotient.mk _ c ⊗ₜ[C,
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))] m)) =
            Submodule.Quotient.mk (c • m)) ∧
        (∀ (c : C) (m : (universalExactAffineSections f t C z).obj F.X₂),
          e₂ (l₂.hom (Ideal.Quotient.mk _ c ⊗ₜ[C,
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))] m)) =
            Submodule.Quotient.mk (c • m)) ∧
        (∀ (c : C) (m : (universalExactAffineSections f t C z).obj F.X₃),
          e₃ (l₃.hom (Ideal.Quotient.mk _ c ⊗ₜ[C,
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))] m)) =
            Submodule.Quotient.mk (c • m)) ∧
        (∀ m : (universalExactAffineSections f t C z).obj F.X₁,
          ((tensorPullback
            (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))).obj
              ((universalExactAffineChart f t C z).obj F.X₁)).presheaf.map
            (homOfLE le_top).op
              ((ψ₁.hom ≫ (universalExactAffineChartComposition f t C z
                (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))).hom.app F.X₁).app ⊤
                (tilde.toOpen (R := .of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) Q.X₁ ⊤
                (l₁.hom ((1 : C ⧸ Ideal.span {(algebraMap A C a) ^ n}) ⊗ₜ[C,
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))] m)))) =
          tensorPullbackSection (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))
            ((universalExactAffineChart f t C z).obj F.X₁) ⊤ m) ∧
        (∀ m : (universalExactAffineSections f t C z).obj F.X₂,
          ((tensorPullback
            (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))).obj
              ((universalExactAffineChart f t C z).obj F.X₂)).presheaf.map
            (homOfLE le_top).op
              ((ψ₂.hom ≫ (universalExactAffineChartComposition f t C z
                (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))).hom.app F.X₂).app ⊤
                (tilde.toOpen (R := .of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) Q.X₂ ⊤
                (l₂.hom ((1 : C ⧸ Ideal.span {(algebraMap A C a) ^ n}) ⊗ₜ[C,
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))] m)))) =
          tensorPullbackSection (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))
            ((universalExactAffineChart f t C z).obj F.X₂) ⊤ m) ∧
        (∀ m : (universalExactAffineSections f t C z).obj F.X₃,
          ((tensorPullback
            (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))).obj
              ((universalExactAffineChart f t C z).obj F.X₃)).presheaf.map
            (homOfLE le_top).op
              ((ψ₃.hom ≫ (universalExactAffineChartComposition f t C z
                (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))).hom.app F.X₃).app ⊤
                (tilde.toOpen (R := .of (C ⧸ Ideal.span {(algebraMap A C a) ^ n})) Q.X₃ ⊤
                (l₃.hom ((1 : C ⧸ Ideal.span {(algebraMap A C a) ^ n}) ⊗ₜ[C,
                  (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))] m)))) =
          tensorPullbackSection (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n}))))
            ((universalExactAffineChart f t C z).obj F.X₃) ⊤ m) ∧
        (tilde.functor (.of (C ⧸ Ideal.span {(algebraMap A C a) ^ n}))).map Q.f ≫ ψ₂.hom =
          ψ₁.hom ≫ (tensorPullback ((Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n})))) ≫
            (z ≫ pullback.fst f t))).map F.f ∧
        (tilde.functor (.of (C ⧸ Ideal.span {(algebraMap A C a) ^ n}))).map Q.g ≫ ψ₃.hom =
          ψ₂.hom ≫ (tensorPullback ((Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span {(algebraMap A C a) ^ n})))) ≫
            (z ≫ pullback.fst f t))).map F.g ∧
        Function.Injective (fun x ↦ e₂ (Q.f (e₁.symm x))) ∧
        (∀ m : (universalExactAffineSections f t C z).obj F.X₁,
          (∃ x : (universalExactAffineSections f t C z).obj F.X₂,
            (algebraMap A C a) ^ n • x =
              (universalExactAffineSections f t C z).map F.f m) →
          ∃ y : (universalExactAffineSections f t C z).obj F.X₁,
            (algebraMap A C a) ^ n • y = m) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
