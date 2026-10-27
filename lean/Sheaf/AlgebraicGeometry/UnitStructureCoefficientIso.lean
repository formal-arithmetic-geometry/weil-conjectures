/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation

/-! # The canonical additive coordinates of the coherent unit coefficient -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Tensor pullback carries multiplication to multiplication by the pulled-back function.
Source: Stacks Project, Tag 0096.
(blueprint: new-unit-structure-coefficient-iso).
Proof: apply the tensor pullback adjunction, use naturality of its unit, and use
that multiplication by a base function on pushforward is multiplication by its pullback. -/
theorem tensorPullback_map_smulHom {A B : Scheme.{u}} (g : A ⟶ B)
    (M : B.Modules) (r : Γ(B, ⊤)) :
    (tensorPullback g).map (M.smulHom r) =
      ((tensorPullback g).obj M).smulHom (g.appTop r) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom]
  erw [← adj.unit.naturality (M.smulHom r)]
  exact smulHom_naturality _ _

/-- The canonical coherent coefficient map has its prescribed tensor-section components.
Source: Stacks Project, Tags 03DW and 03P2.
(blueprint: new-unit-structure-coefficient-iso).
Proof: lift the defining section formula of the coherent comparison map. -/
theorem coherentEtaleMap_app {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) (U : X.Etale) :
    (coherentEtaleMap M N φ).hom.app (op U) =
      AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤) := by
  exact congrArg AddCommGrpCat.uliftFunctor.map
    ((Classical.choose_spec (etale_zariski_qcoh_comparison X)).1 M N φ U)

/-- A coherent multiplication map acts on tensor sections by the pulled-back scalar.
Source: Stacks Project, Tags 0096 and 03P2.
(blueprint: new-unit-structure-coefficient-iso).
Proof: use the coefficient-map section formula and pullback of multiplication. -/
theorem coherentEtaleMap_smulHom_app {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (r : Γ(X, ⊤)) (U : X.Etale)
    (x : (liftedCoherentEtaleSheaf M).obj.obj (op U)) :
    (coherentEtaleMap M M (M.smulHom r)).hom.app (op U) x =
      ULift.up (U.hom.appTop r • @id Γ((tensorPullback U.hom).obj M, ⊤) x.down) := by
  rw [coherentEtaleMap_app, tensorPullback_map_smulHom]
  exact congrArg ULift.up (smulHom_app_top_apply _ _ x.down)

/-- The associated coherent unit sheaf is the actual additive structure sheaf.
Every component is the adjoint structure-module map on top sections, lifted once.
Source: Stacks Project, Tags 0096, 01CA and 03DR.
(blueprint: new-unit-structure-coefficient-iso). -/
def unitStructureCoefficientIso (X : Scheme.{u}) :
    liftedCoherentEtaleSheaf (SheafOfModules.unit X.ringCatSheaf) ≅ X.etaleAdditiveSheaf := by
  have hi (U : X.Etaleᵒᵖ) : IsIso (tensorPullbackObjUnitToUnit U.unop.hom) :=
    (tensorPullbackObjUnitToUnit_isIso U.unop.hom).1
  let c : etaleTensorSectionsPresheaf (SheafOfModules.unit X.ringCatSheaf) ≅
      X.etaleStructurePresheaf ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat :=
    NatIso.ofComponents (fun U ↦ asIso ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤))
      (by
        intro U V g
        apply ConcreteCategory.hom_ext
        intro x
        exact etaleTensorUnitRestriction_equation g.unop x)
  exact (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight c AddCommGrpCat.uliftFunctor.{u + 1, u})

/-- The coefficient isomorphism uses the actual adjoint structure map on sections.
Source: Stacks Project, Tags 0096, 01CA and 03DR.
(blueprint: new-unit-structure-coefficient-iso).
Proof: this is the component of the explicit presheaf isomorphism used in the definition. -/
theorem unitStructureCoefficientIso_hom_app (X : Scheme.{u}) (U : X.Etale)
    (x : (liftedCoherentEtaleSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op U)) :
    (unitStructureCoefficientIso X).hom.hom.app (op U) x =
      ULift.up (@id Γ(U.left, ⊤) ((tensorPullbackObjUnitToUnit U.hom).app ⊤ x.down)) := by
  rfl

end
end AlgebraicGeometry.Scheme.Modules
