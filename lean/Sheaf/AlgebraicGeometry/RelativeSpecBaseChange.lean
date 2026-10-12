/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Relative Spec commutes with base change

Source: Stacks Project, Constructions, Lemma 01LX (spec-properties), clause (2),
and Section 01LQ (blueprint: lem-weil-pbc-relative-spec-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Relative Spec commutes with arbitrary base change. An affine morphism with an algebra
identification is a relative spectrum by the anti-equivalence of
`lem-weil-pbc-affine-morphism-relative-spec`. Multiplications and units below are fixed on
sections, and the two transport equations specify the induced pullback algebra structure.
The section formula for gamma specifies its adjoint, not an arbitrary algebra isomorphism.
The final formula specifies the unique canonical comparison over the new base.
Source: Stacks Project, Constructions, Lemma 01LX (2), Section 01LQ
(blueprint: lem-weil-pbc-relative-spec-base-change).
Proof:
1. The relative spectrum map is affine; affine morphisms remain affine under base change
   (lem-weil-pbc-affine-morphism-permanence). Its structure-sheaf pushforward is quasi-coherent
   (lem-weil-pbc-affine-morphism-relative-spec (1)).
2. Apply lem-weil-pbc-affine-pushforward-base-change to the structure sheaf. Compose the
   invertible base change map with the structure-sheaf pullback identification. Its adjoint
   is the pushforward of g-prime sharp (lem-weil-pbc-module-base-change-map-algebra).
3. Transport along alpha. Naturality of lem-weil-pbc-module-pullback-tensor and the unit
   identification give exactly the displayed multiplication and unit equations. The algebra
   axioms hold by transport of the sectionwise ring structure, and the underlying module is
   quasi-coherent by lem-weil-pbc-module-pullback-quasi-coherent. Adjoint naturality gives
   the displayed formula on the image of the adjunction unit.
4. Apply the fully faithful anti-equivalence of lem-weil-pbc-affine-morphism-relative-spec
   (3) over S-prime to alpha-prime composed with gamma inverse. It gives a unique comparison
   over S-prime. The inverse algebra map gives an inverse scheme map; faithfulness identifies
   their composites with the identities. Thus the canonical comparison is an isomorphism. -/
theorem relative_spec_base_change
    (S S' : Scheme.{u}) (g : S' ⟶ S)
    (A : S.CommAlgebraSheaf) [(A.toModule : S.Modules).IsQuasicoherent]
    (μ : (SheafOfModules.monoidalCategory S.sheaf).tensorObj A.toModule A.toModule ⟶
      A.toModule)
    (e : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶ (A.toModule : S.Modules))
    (hμ : ∀ (V : S.Opens) (a b : A.right.obj.obj (op V)),
      μ.val.app (op V) (tmulSection (M := A.toModule) (N := A.toModule) (U := V) a b) = a * b)
    (he : ∀ (V : S.Opens) (r : Γ(S, V)), e.val.app (op V) r = A.hom.hom.app (op V) r)
    (X : Scheme.{u}) (π : X ⟶ S) [IsAffineHom π]
    (α : A ≅ Under.mk (⟨π.c⟩ : Scheme.sheaf _ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj (Scheme.sheaf _)))
    (X' : Scheme.{u}) (π' : X' ⟶ S') (g' : X' ⟶ X)
    (sq : IsPullback g' π' π g) :
    IsAffineHom π' ∧
    ∃ (A' : S'.CommAlgebraSheaf)
      (hA' : (A'.toModule : S'.Modules) ≅ (tensorPullback g).obj (A.toModule : S.Modules))
      (μ' : (SheafOfModules.monoidalCategory S'.sheaf).tensorObj A'.toModule A'.toModule ⟶
        A'.toModule)
      (e' : (SheafOfModules.unit S'.ringCatSheaf : S'.Modules) ⟶ (A'.toModule : S'.Modules))
      (γ : A' ≅ Under.mk (⟨π'.c⟩ : Scheme.sheaf _ ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} π'.base).obj (Scheme.sheaf _))),
      (A'.toModule : S'.Modules).IsQuasicoherent ∧
      (∀ (W : S'.Opens) (a b : A'.right.obj.obj (op W)),
        μ'.val.app (op W)
          (tmulSection (M := A'.toModule) (N := A'.toModule) (U := W) a b) = a * b) ∧
      (∀ (W : S'.Opens) (r : Γ(S', W)), e'.val.app (op W) r = A'.hom.hom.app (op W) r) ∧
      (tensorPullback g).map μ =
        (Classical.choose (module_pullback_tensor g)
          (A.toModule : S.Modules) (A.toModule : S.Modules)).hom ≫
          (SheafOfModules.monoidalCategory S'.sheaf).tensorHom hA'.inv hA'.inv ≫ μ' ≫ hA'.hom ∧
      (tensorPullback g).map e ≫ hA'.inv = tensorPullbackObjUnitToUnit g ≫ e' ∧
      (∀ (V : S.Opens) (a : A.right.obj.obj (op V)),
        γ.hom.right.hom.app (op (g ⁻¹ᵁ V))
          (hA'.inv.val.app (op (g ⁻¹ᵁ V))
            (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
              (A.toModule : S.Modules)).val.app (op V) a)) =
          g'.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ (g ⁻¹ᵁ V))
            (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])
            (α.hom.right.hom.app (op V) a)) ∧
      (∀ (Y : Scheme.{u}) (ρ : Y ⟶ S'), IsAffineHom ρ →
        ∀ (α' : A' ≅ Under.mk (⟨ρ.c⟩ : Scheme.sheaf _ ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} ρ.base).obj (Scheme.sheaf _))),
        ∃ (Φ : Y ⟶ X') (hΦ : Φ ≫ π' = ρ),
          (∀ (W : S'.Opens),
            Φ.appLE (π' ⁻¹ᵁ W) (ρ ⁻¹ᵁ W)
              (by rw [← Scheme.Hom.comp_preimage, hΦ]) =
              γ.inv.right.hom.app (op W) ≫ α'.hom.right.hom.app (op W)) ∧
          IsIso Φ ∧
          ∀ (Ψ : Y ⟶ X') (hΨ : Ψ ≫ π' = ρ),
            (∀ (W : S'.Opens),
              Ψ.appLE (π' ⁻¹ᵁ W) (ρ ⁻¹ᵁ W)
                (by rw [← Scheme.Hom.comp_preimage, hΨ]) =
                γ.inv.right.hom.app (op W) ≫ α'.hom.right.hom.app (op W)) → Ψ = Φ) := by
  sorry

end AlgebraicGeometry
