/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardConstantSectionsTensor
public import Sheaf.Paper.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.ExternalSectionsComponents
import WeilConjectures.AlgebraicGeometry.PicardConstantTensorBalancedSections

/-! # The ordinary external section map on constant tensor coefficients

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Elaborating section modules across scalar restriction and the pullback needs this budget.
/-- Scalar extension and tensor balance lift the external section map to an O_Y-linear
presheaf morphism. Its component is bijective exactly when the corresponding k-linear
external section component is bijective.
Source: Stacks Project, Varieties, Tag 0BED, affine-open degree-zero calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).

Proof: At any open V, identity-functor presheaf pullback is extension of scalars.
The balanced map (a tensor s) tensor t maps to s tensor (a*t), with inverse
s tensor t mapping to (1 tensor s) tensor t. These formulas give an isomorphism
of underlying k-modules between the constant coefficient tensor object at V and
Gamma(X,F) tensor_k G(V), with O_Y(V) acting on the second factor.
Compose this isomorphism with externalSectionsComponent. Multiplication on tensor
sections and O_Y-linearity of the second projection's adjunction unit prove
O_Y(V)-linearity of the composite. Naturality of scalar extension and the proved
externalSectionsComponent_naturality show that these composites form a morphism
of presheaves of modules. The k-action on the direct image agrees with the action
through the first projection because the pullback square commutes. Consequently
its underlying component is the external section component composed with a
bijection, proving the displayed equivalence. This construction uses no affine,
compactness or quasi-coherence hypothesis. Empty opens and zero coefficients
are covered by the same mutually inverse balanced maps. -/
theorem exists_external_constant_sections_tensor_map
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    ∃ φ : picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G ⟶
      ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
        (externalCupCoefficients f g F G)).val,
      ∀ V : Y.Opens, Function.Bijective (φ.app (op V)) ↔
        Function.Bijective (externalSectionsComponent f g F G V) := by
  classical
  let e := picardConstantTensorBalancedSections k Y g (scalarObj f F (op ⊤)) G
  have he := picardConstantTensorBalancedSections_smul k Y g (scalarObj f F (op ⊤)) G
  have hn := @picardConstantTensorBalancedSections_map k _ Y g (scalarObj f F (op ⊤)) G
  let P := picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G
  let T := ((RingedSpace.moduleDirectImage
    (pullback.snd f g).toLRSHom.toShHom).obj (externalCupCoefficients f g F G)).val
  have hs (V : Y.Opens) (a : Γ(Y, V)) (s : scalarObj f F (op ⊤))
      (t : scalarObj g G (op V)) :
      externalSectionsComponent f g F G V
          (TensorProduct.tmul k s
            (show scalarObj g G (op V) from a • (show G.val.obj (op V) from t))) =
        (show T.obj (op V) from a •
          (show T.obj (op V) from
            externalSectionsComponent f g F G V (TensorProduct.tmul k s t))) := by
    change tmulSection
        (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V) s)
        (scalarUnitSection g (pullback.snd f g) G V (a • (show G.val.obj (op V) from t))) =
      ((pullback.snd f g).app V).hom a • tmulSection _ _
    change tmulSection
        (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V) s)
        (((Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G).app
          V (a • (show G.val.obj (op V) from t))) = _
    rw [Hom.app_smul]
    exact tmulSection_smul (((pullback.snd f g).app V).hom a)
      (scalarPullbackGlobalSection f (pullback.fst f g) F (pullback.snd f g ⁻¹ᵁ V) s)
      (scalarUnitSection g (pullback.snd f g) G V t)
  let φ : P ⟶ T :=
    { app := fun V ↦ ModuleCat.ofHom (X := P.obj V) (Y := T.obj V)
        { toFun := fun x ↦ externalSectionsComponent f g F G V.unop (e V.unop x)
          map_add' := by intros; simp
          map_smul' := by
            intro a x
            obtain ⟨z, rfl⟩ := (e V.unop).symm.surjective x
            induction z using TensorProduct.induction_on with
            | zero => simp
            | tmul s t =>
              rw [he]
              simpa only [AddEquiv.apply_symm_apply, RingHom.id_apply] using hs V.unop a s t
            | add z z' hz hz' => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hz hz' }
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        ext x
        change externalSectionsComponent f g F G V.unop (e V.unop (P.map i x)) = _
        rw [hn]
        exact congrArg (fun q ↦ q (e U.unop x))
          (externalSectionsComponent_naturality f g F G i) }
  refine ⟨φ, fun V ↦ ?_⟩
  change Function.Bijective (fun x ↦ externalSectionsComponent f g F G V (e V x)) ↔ _
  exact (e V).bijective.of_comp_iff (externalSectionsComponent f g F G V)


end AlgebraicGeometry.Scheme.Modules
