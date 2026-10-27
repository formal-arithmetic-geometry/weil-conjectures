/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.InvariantLocalCurvePencils
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Sheaf.AlgebraicGeometry.FiniteNormalRelativeCurveModel
import Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.FieldTheory.SeparableDegree

/-! # Equivariant constant extension preserving local pencils

Source: de Jong, *Families of curves and alterations* (1997), §§3.2--3.5, pp.605--606.
(blueprint: lem-sfb-equivariant-pencil-constant-preparation)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2048

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Existential proposition for the constant-extension preparation, retaining all canonical maps.
`FractionRing` names the tensor field without choosing another field structure on its ring.
The compatible-pair realization and injectivity identify `H₀` with precisely the displayed
fibre-product group, including the kernel of a nonfaithful original action. The field actions
are left actions; the corresponding scheme maps use their inverses.

Source: de Jong §§3.2--3.5, pp.605--606.
(blueprint: lem-sfb-equivariant-pencil-constant-preparation) -/
def EquivariantPencilConstantPreparation
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (pS : S ⟶ Spec (.of k)) [LocallyOfFiniteType pS] [QuasiCompact pS]
    (f : X ⟶ S)
    [Algebra S.functionField X.functionField]
    (H : Type v) [Group H] (ρX : H →* Aut X) (ρS : H →* Aut S)
    (aK : H →* RingAut S.functionField) (aF : H →* RingAut X.functionField)
    (M : Closeds (pullback (C := Scheme.{u}) f S.fromSpecFunctionField)) (ell : ℕ) : Prop :=
  ∃ (B : Subfield S.functionField),
  ∃ (_fixedBase : ∀ x : S.functionField, x ∈ B ↔ ∀ h : H, aK h x = x),
  ∃ (E₀ : Type u),
  ∃ (_ : Field E₀),
  ∃ (_ : Algebra S.functionField E₀),
  ∃ (_ : FiniteDimensional S.functionField E₀),
  ∃ (_ : Algebra.IsSeparable S.functionField E₀),
  ∃ (K₀ : Type u),
  ∃ (_ : Field K₀),
  ∃ (_ : Algebra S.functionField K₀),
  ∃ (_ : Algebra E₀ K₀),
  ∃ (_ : IsScalarTower S.functionField E₀ K₀),
  ∃ (_ : FiniteDimensional E₀ K₀),
  ∃ (_ : Algebra B K₀),
  ∃ (_ : IsScalarTower B S.functionField K₀),
  ∃ (_ : FiniteDimensional B K₀),
  ∃ (_ : IsGalois B K₀),
  ∃ (commonClosureE : E₀ →ₐ[S.functionField] AlgebraicClosure S.functionField),
  ∃ (commonClosureK : K₀ →ₐ[S.functionField] AlgebraicClosure S.functionField),
  ∃ (_commonClosure : ∀ x : E₀, commonClosureK (algebraMap E₀ K₀ x) = commonClosureE x),
  ∃ (root : K₀),
  ∃ (_primitiveRoot : IsPrimitiveRoot root ell),
  ∃ (_positiveDimension : 0 < topologicalKrullDim S →
    Function.Bijective (algebraMap S.functionField E₀)),
  ∃ (H₀ : Type (max u v)),
  ∃ (_ : Group H₀),
  ∃ (_ : Finite H₀),
  ∃ (projection : H₀ →* H),
  ∃ (fieldAction : H₀ →* (K₀ ≃ₐ[B] K₀)),
  ∃ (_pairs_injective : Function.Injective (fun a : H₀ ↦ (projection a, fieldAction a))),
  ∃ (_pairs_compatible : ∀ (a : H₀) (x : S.functionField),
    fieldAction a (algebraMap S.functionField K₀ x) =
      algebraMap S.functionField K₀ (aK (projection a) x)),
  ∃ (_pairs_exhaustive : ∀ (h : H) (σ : K₀ ≃ₐ[B] K₀),
    (∀ x : S.functionField, σ (algebraMap S.functionField K₀ x) =
      algebraMap S.functionField K₀ (aK h x)) →
    ∃ a : H₀, projection a = h ∧ fieldAction a = σ),
  ∃ (_projection_surjective : Function.Surjective projection),
  ∃ (_kernel_constants : ∀ z : K₀,
    (∀ a : projection.ker, fieldAction a.val z = z) ↔
      z ∈ Set.range (algebraMap S.functionField K₀)),
  ∃ (_ : IsDomain (X.functionField ⊗[S.functionField] K₀)),
  ∃ (_tensorField : IsField (X.functionField ⊗[S.functionField] K₀)),
  ∃ (_finiteTensor : FiniteDimensional X.functionField
    (FractionRing (X.functionField ⊗[S.functionField] K₀))),
  ∃ (_separableTensor : Algebra.IsSeparable X.functionField
    (FractionRing (X.functionField ⊗[S.functionField] K₀))),
  ∃ (tensorAction : H₀ →* RingAut (FractionRing (X.functionField ⊗[S.functionField] K₀))),
  ∃ (_tensorAction_pure : ∀ (a : H₀) (z : X.functionField) (c : K₀),
    tensorAction a
      (algebraMap (X.functionField ⊗[S.functionField] K₀) _ (z ⊗ₜ c)) =
    algebraMap (X.functionField ⊗[S.functionField] K₀) _
      (aF (projection a) z ⊗ₜ (fieldAction a c))),
  ∃ (_kernel_functionField : ∀ z : FractionRing (X.functionField ⊗[S.functionField] K₀),
    (∀ a : projection.ker, tensorAction a.val z = z) ↔
      z ∈ Set.range (algebraMap X.functionField
        (FractionRing (X.functionField ⊗[S.functionField] K₀)))),
  ∃ (_ : IsIntegral (S.normalizationIn K₀)),
  ∃ (_ : IsIntegral
    (X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)))),
  ∃ (_normalS : ∀ s : S.normalizationIn K₀,
    IsDomain ((S.normalizationIn K₀).presheaf.stalk s) ∧
      IsIntegrallyClosed ((S.normalizationIn K₀).presheaf.stalk s)),
  ∃ (_normalX : ∀ x : X.normalizationIn
      (FractionRing (X.functionField ⊗[S.functionField] K₀)),
    IsDomain ((X.normalizationIn
      (FractionRing (X.functionField ⊗[S.functionField] K₀))).presheaf.stalk x) ∧
    IsIntegrallyClosed ((X.normalizationIn
      (FractionRing (X.functionField ⊗[S.functionField] K₀))).presheaf.stalk x)),
  ∃ (_projectiveS : IsHProjective (S.fromNormalizationIn K₀ ≫ pS)),
  ∃ (_finiteTypeS : LocallyOfFiniteType (S.fromNormalizationIn K₀ ≫ pS)),
  ∃ (_quasiCompactS : QuasiCompact (S.fromNormalizationIn K₀ ≫ pS)),
  ∃ (_finiteS : IsFinite (S.fromNormalizationIn K₀)),
  ∃ (_surjectiveS : Surjective (S.fromNormalizationIn K₀)),
  ∃ (_finiteTypeX : LocallyOfFiniteType
    (X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) ≫ f ≫ pS)),
  ∃ (_quasiCompactX : QuasiCompact
    (X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) ≫ f ≫ pS)),
  ∃ (q : X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) ⟶
    S.normalizationIn K₀),
  ∃ (_q_over : q ≫ S.fromNormalizationIn K₀ =
    X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) ≫ f),
  ∃ (_q_generic : (X.fromSpecOfAlgebraFunctionField
      (FractionRing (X.functionField ⊗[S.functionField] K₀))).toNormalization ≫ q =
    Spec.map (CommRingCat.ofHom (invariantPencilConstantMap S.functionField X.functionField K₀)) ≫
      (S.fromSpecOfAlgebraFunctionField K₀).toNormalization),
  ∃ (_projectiveX : IsHProjective q),
  ∃ (_pureFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S.normalizationIn K₀), (pullback (C := Scheme.{u}) q
      s).IsPureDimension 1),
  ∃ (modelComparison : X.normalizationIn
      (FractionRing (X.functionField ⊗[S.functionField] K₀)) ⟶
    pullback (C := Scheme.{u}) f (S.fromNormalizationIn K₀)),
  ∃ (_modelComparison_fst : modelComparison ≫ pullback.fst f (S.fromNormalizationIn K₀) =
    X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀))),
  ∃ (_modelComparison_snd : modelComparison ≫ pullback.snd f (S.fromNormalizationIn K₀) = q),
  ∃ (_finiteComparison : IsFinite modelComparison),
  ∃ (_surjectiveComparison : Surjective modelComparison),
  ∃ (genericComparison : pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField
      K₀).toNormalization ≅
    pullback (C := Scheme.{u}) (pullback.snd f S.fromSpecFunctionField)
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField K₀)))),
  ∃ (_genericComparison_base : genericComparison.hom ≫
    pullback.snd (pullback.snd f S.fromSpecFunctionField)
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField K₀))) =
    pullback.snd q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization),
  ∃ (_genericComparison_X : genericComparison.hom ≫
    pullback.fst (pullback.snd f S.fromSpecFunctionField)
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField K₀))) ≫
        pullback.fst f S.fromSpecFunctionField =
    pullback.fst q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization ≫
      X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀))),
  ∃ (actionX : H₀ →* Aut
    (X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)))),
  ∃ (actionS : H₀ →* Aut (S.normalizationIn K₀)),
  ∃ (_actionX_over : ∀ a : H₀, (actionX a).hom ≫
      X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) =
    X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) ≫
      (ρX (projection a)).hom),
  ∃ (_actionS_over : ∀ a : H₀, (actionS a).hom ≫ S.fromNormalizationIn K₀ =
    S.fromNormalizationIn K₀ ≫ (ρS (projection a)).hom),
  ∃ (_actionX_generic : ∀ a : H₀, (X.fromSpecOfAlgebraFunctionField
      (FractionRing (X.functionField ⊗[S.functionField] K₀))).toNormalization ≫
        (actionX a).hom =
    Spec.map (CommRingCat.ofHom (tensorAction a⁻¹).toRingHom) ≫
      (X.fromSpecOfAlgebraFunctionField
        (FractionRing (X.functionField ⊗[S.functionField] K₀))).toNormalization),
  ∃ (_actionS_generic : ∀ a : H₀,
    (S.fromSpecOfAlgebraFunctionField K₀).toNormalization ≫ (actionS a).hom =
      Spec.map (CommRingCat.ofHom (fieldAction a⁻¹).toRingHom) ≫
        (S.fromSpecOfAlgebraFunctionField K₀).toNormalization),
  ∃ (_action_q : ∀ a : H₀, (actionX a).hom ≫ q = q ≫ (actionS a).hom),
  ∃ (actionComparison : H₀ →* Aut (pullback (C := Scheme.{u}) f (S.fromNormalizationIn K₀))),
  ∃ (_actionComparison_fst : ∀ a : H₀,
    (actionComparison a).hom ≫ pullback.fst f (S.fromNormalizationIn K₀) =
      pullback.fst f (S.fromNormalizationIn K₀) ≫ (ρX (projection a)).hom),
  ∃ (_actionComparison_snd : ∀ a : H₀,
    (actionComparison a).hom ≫ pullback.snd f (S.fromNormalizationIn K₀) =
      pullback.snd f (S.fromNormalizationIn K₀) ≫ (actionS a).hom),
  ∃ (_action_modelComparison : ∀ a : H₀, (actionX a).hom ≫ modelComparison =
    modelComparison ≫ (actionComparison a).hom),
  ∃ (_uniqueActions : ∀
      (τX : H₀ →* Aut
        (X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀))))
      (τS : H₀ →* Aut (S.normalizationIn K₀)),
    (∀ a : H₀, (X.fromSpecOfAlgebraFunctionField
        (FractionRing (X.functionField ⊗[S.functionField] K₀))).toNormalization ≫
          (τX a).hom =
      Spec.map (CommRingCat.ofHom (tensorAction a⁻¹).toRingHom) ≫
        (X.fromSpecOfAlgebraFunctionField
          (FractionRing (X.functionField ⊗[S.functionField] K₀))).toNormalization) →
    (∀ a : H₀, (S.fromSpecOfAlgebraFunctionField K₀).toNormalization ≫ (τS a).hom =
      Spec.map (CommRingCat.ofHom (fieldAction a⁻¹).toRingHom) ≫
        (S.fromSpecOfAlgebraFunctionField K₀).toNormalization) →
    τX = actionX ∧ τS = actionS),
  ∃ (_ : IsDomain (X.functionField ⊗[S.functionField] E₀)),
  ∃ (qE : X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] E₀)) ⟶
    S.normalizationIn E₀),
  ∃ (_qE_over : qE ≫ S.fromNormalizationIn E₀ =
    X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] E₀)) ≫ f),
  ∃ (_qE_generic : (X.fromSpecOfAlgebraFunctionField
      (FractionRing (X.functionField ⊗[S.functionField] E₀))).toNormalization ≫ qE =
    Spec.map (CommRingCat.ofHom (invariantPencilConstantMap S.functionField X.functionField E₀)) ≫
      (S.fromSpecOfAlgebraFunctionField E₀).toNormalization),
  ∃ (sE : S.normalizationIn K₀ ⟶ S.normalizationIn E₀),
  ∃ (_sE_over : sE ≫ S.fromNormalizationIn E₀ = S.fromNormalizationIn K₀),
  ∃ (_sE_generic : (S.fromSpecOfAlgebraFunctionField K₀).toNormalization ≫ sE =
    Spec.map (CommRingCat.ofHom (algebraMap E₀ K₀)) ≫
      (S.fromSpecOfAlgebraFunctionField E₀).toNormalization),
  ∃ (xE : X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀)) ⟶
    X.normalizationIn (FractionRing (X.functionField ⊗[S.functionField] E₀))),
  ∃ (_xE_over : xE ≫ X.fromNormalizationIn
      (FractionRing (X.functionField ⊗[S.functionField] E₀)) =
    X.fromNormalizationIn (FractionRing (X.functionField ⊗[S.functionField] K₀))),
  ∃ (_xE_base : xE ≫ qE = q ≫ sE),
  ∃ (_finiteXE : IsFinite xE),
  ∃ (r : ℕ),
  ∃ (V : Fin r → (S.normalizationIn E₀).Opens),
  ∃ (_coverE : (⨆ i : Fin r, V i) = ⊤),
  ∃ (_affineE : ∀ i : Fin r, IsAffineOpen (V i)),
  ∃ (_oneOpen : topologicalKrullDim S = 0 → r = 1),
  ∃ (_coverK : (⨆ i : Fin r, sE ⁻¹ᵁ V i) = ⊤),
  ∃ (_affineK : ∀ i : Fin r, IsAffineOpen (sE ⁻¹ᵁ V i)),
  ∃ (pencilE : ∀ i : Fin r, pullback (C := Scheme.{u}) qE (V i).ι ⟶ ProjectiveLine (V i).toScheme),
  ∃ (_pencilE_over : ∀ i : Fin r, pencilE i ≫ ProjectiveLine (V i).toScheme ↘ (V i).toScheme =
    pullback.snd qE (V i).ι),
  ∃ (_pencilE_finite : ∀ i : Fin r, IsFinite (pencilE i)),
  ∃ (_pencilE_surjective : ∀ i : Fin r, Surjective (pencilE i)),
  ∃ (localComparison : ∀ i : Fin r, pullback (C := Scheme.{u}) q (sE ⁻¹ᵁ V i).ι ⟶ pullback (C :=
      Scheme.{u}) qE (V i).ι),
  ∃ (_localComparison_fst : ∀ i : Fin r,
    localComparison i ≫ pullback.fst qE (V i).ι = pullback.fst q (sE ⁻¹ᵁ V i).ι ≫ xE),
  ∃ (_localComparison_snd : ∀ i : Fin r, localComparison i ≫ pullback.snd qE (V i).ι =
    pullback.snd q (sE ⁻¹ᵁ V i).ι ≫ sE.resLE (V i) (sE ⁻¹ᵁ V i) le_rfl),
  ∃ (pencilK : ∀ i : Fin r, pullback (C := Scheme.{u}) q (sE ⁻¹ᵁ V i).ι ⟶ ProjectiveLine (sE ⁻¹ᵁ
      V i).toScheme),
  ∃ (_pencilK_over : ∀ i : Fin r,
    pencilK i ≫ ProjectiveLine (sE ⁻¹ᵁ V i).toScheme ↘ (sE ⁻¹ᵁ V i).toScheme =
      pullback.snd q (sE ⁻¹ᵁ V i).ι),
  ∃ (_inducedPencil : ∀ i : Fin r, pencilK i ≫ ProjectiveSpace.map (ULift.{u} (Fin 2))
      (sE.resLE (V i) (sE ⁻¹ᵁ V i) le_rfl) = localComparison i ≫ pencilE i),
  ∃ (_pencilK_finite : ∀ i : Fin r, IsFinite (pencilK i)),
  ∃ (_pencilK_surjective : ∀ i : Fin r, Surjective (pencilK i)),
  ∃ (M₀ : Closeds (pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField
      K₀).toNormalization)),
  ∃ (_markingPreimage : M₀ = M.preimage
    (genericComparison.hom ≫ pullback.fst (pullback.snd f S.fromSpecFunctionField)
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField K₀)))).continuous),
  ∃ (_markingFinite : IsFinite ((Scheme.IdealSheafData.vanishingIdeal M₀).subschemeι ≫
    pullback.snd q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization)),
  ∃ (_markingEtale : Etale ((Scheme.IdealSheafData.vanishingIdeal M₀).subschemeι ≫
    pullback.snd q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization)),
  ∃ (_markingStable : ∀ (a : H₀)
      (x y : pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization),
    (actionX a).hom (pullback.fst q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization x) =
      pullback.fst q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization y →
    (x ∈ M₀ ↔ y ∈ M₀)),
  ∀ i : Fin r,
    ∃ (e : Spec (.of K₀) ⟶ (sE ⁻¹ᵁ V i).toScheme)
      (φ : pullback (C := Scheme.{u}) (pullback.snd q (sE ⁻¹ᵁ V i).ι) e ⟶ ProjectiveLine (Spec
      (.of K₀)))
      (c : pullback (C := Scheme.{u}) (pullback.snd q (sE ⁻¹ᵁ V i).ι) e ⟶
        pullback (C := Scheme.{u}) q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization),
      e ≫ (sE ⁻¹ᵁ V i).ι = (S.fromSpecOfAlgebraFunctionField K₀).toNormalization ∧
      φ ≫ ProjectiveLine (Spec (.of K₀)) ↘ Spec (.of K₀) =
        pullback.snd (pullback.snd q (sE ⁻¹ᵁ V i).ι) e ∧
      φ ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) e =
        pullback.fst (pullback.snd q (sE ⁻¹ᵁ V i).ι) e ≫ pencilK i ∧
      c ≫ pullback.fst q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization =
        pullback.fst (pullback.snd q (sE ⁻¹ᵁ V i).ι) e ≫ pullback.fst q (sE ⁻¹ᵁ V i).ι ∧
      c ≫ pullback.snd q (S.fromSpecOfAlgebraFunctionField K₀).toNormalization =
        pullback.snd (pullback.snd q (sE ⁻¹ᵁ V i).ι) e ∧
      (∃ W : (ProjectiveLine (Spec (.of K₀))).Opens,
        Nonempty W ∧ Etale (pullback.snd φ W.ι)) ∧
      (∀ j : Fin 3,
        IsFinite (pullback.snd φ (invariantPencilSpecialPoint (Spec (.of K₀)) j)) ∧
        Etale (pullback.snd φ (invariantPencilSpecialPoint (Spec (.of K₀)) j)) ∧
        IsReduced (pullback (C := Scheme.{u}) φ (invariantPencilSpecialPoint (Spec (.of K₀)) j))) ∧
      ∀ z : pullback (C := Scheme.{u}) (pullback.snd q (sE ⁻¹ᵁ V i).ι) e,
        (∃ j : Fin 3, φ z ∈ Set.range (invariantPencilSpecialPoint (Spec (.of K₀)) j)) →
          c z ∉ M₀

/-- The equivariant constant-extension and local-pencil preparation.
Source: de Jong §§3.2--3.5, pp.605--606.
(blueprint: lem-sfb-equivariant-pencil-constant-preparation)

Proof:
1. Apply invariant-local-curve-pencils with the trivial group. It gives E₀ and its affine
   pencils, E₀=K in positive dimension and one open in dimension zero. Apply the
   constant-extension clause of finite-normal-relative-curve-model to E₀/K.
2. In a separable closure adjoin a root of 1+T+...+T^(ell-1). Differentiating
   (T-1)q=T^ell-1 shows q is separable since ell is invertible. The root has order ell;
   simple-algebraic-extension-power-basis and separable-permanence give a finite separable
   extension of K containing E₀ and this root.
3. Apply finite-semilinear-field-envelope in its separable case. The compatible-pair
   group surjects onto H, K₀/B is finite Galois and its kernel fixes precisely K. The
   intermediate-base separability lemma and algebraically-closed embedding lemma put the
   tower in a common algebraic closure.
4. The constant-extension clause of finite-normal-relative-curve-model gives the tensor
   field, finite separability, normal models, projectivity, pure fibres and the generic
   scalar-extension identification.
5. Balancing of the tensor action follows from agreement on K; inverse and composition
   hold on pure tensors. Functoriality and uniqueness of the normal-model construction
   extend it, including semilinear actions, and make all four maps equivariant.
6. Apply tensor-kernel-inseparable-invariants with the kernel acting trivially on F and
   fixing K on the constant side. Its identity purely inseparable cases give F₀^A₀=F.
7. Apply the relative-model theorem to K₀/E₀. Composition of finite surjections and
   finite-normal-cover-normalization identify its models with X₀,S₀. Base change and
   compose the pencils. Finite base-change and composition give finite surjections;
   inverse images of affine opens are affine and still cover.
8. On generic fibres these are scalar extensions of the old pencils. Etale and finite
   base change preserve their special fibres and the marking; etale fibres over a field
   are reduced. Empty intersections stay empty and the diagonal action preserves M₀.
-/
theorem exists_equivariant_pencil_constant_preparation
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (pS : S ⟶ Spec (.of k)) [IsHProjective pS]
    [LocallyOfFiniteType pS] [QuasiCompact pS]
    (hnormal : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (f : X ⟶ S) [IsHProjective f]
    [LocallyOfFiniteType (f ≫ pS)] [QuasiCompact (f ≫ pS)]
    (hpure : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      (pullback (C := Scheme.{u}) f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (M : Closeds (pullback (C := Scheme.{u}) f S.fromSpecFunctionField))
    (hMfinite : IsFinite ((Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField))
    (hMetale : Etale ((Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField))
    (H : Type v) [Group H] [Finite H]
    (ρk : H →* Aut (Spec (.of k))) (ρX : H →* Aut X) (ρS : H →* Aut S)
    (hk : ∀ h : H, (ρS h).hom ≫ pS = pS ≫ (ρk h).hom)
    (hX : ∀ h : H, (ρX h).hom ≫ f = f ≫ (ρS h).hom)
    (hMstable : ∀ (h : H) (x y : pullback (C := Scheme.{u}) f S.fromSpecFunctionField),
      (ρX h).hom (pullback.fst f S.fromSpecFunctionField x) =
        pullback.fst f S.fromSpecFunctionField y → (x ∈ M ↔ y ∈ M))
    (ell : ℕ) (hell : Nat.Prime ell) (hell5 : 5 ≤ ell) (hellchar : ringChar k ≠ ell) :
    ∃ (_ : Algebra S.functionField X.functionField)
      (aK : H →* RingAut S.functionField) (aF : H →* RingAut X.functionField),
      (Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)) ≫
        S.fromSpecFunctionField = X.fromSpecFunctionField ≫ f) ∧
      (∀ (h : H) (z : S.functionField), aK h z =
        (Scheme.functionFieldAut (ρS h⁻¹)).hom z) ∧
      (∀ (h : H) (z : X.functionField), aF h z =
        (Scheme.functionFieldAut (ρX h⁻¹)).hom z) ∧
      EquivariantPencilConstantPreparation k S X pS f H ρX ρS aK aF M ell := by
  sorry

end AlgebraicGeometry
