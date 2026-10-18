module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Tensor quotient epimorphism

Source: Bhatt--Scholze, *Pro-étale topology*, Proposition 6.8.4(1), p. 59
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Naturality of the sectionwise extension--restriction unit.
Source: Stacks, Modules on Sites, Tag 03EK
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism).
Proof: the extension--restriction unit sends `m` to `1 ⊗ m`. The restriction map
on the tensor presheaf restricts both factors, and ring restrictions preserve `1`.
Consequently both composites send `m` to `1 ⊗ (m restricted along f)`.
Equality on elements gives equality of these linear maps. -/
theorem integralTensorQuotientPresheafUnit_naturality
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.val.map f ≫
        (ModuleCat.restrictScalars
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).obj.map f).hom).map
          ((ModuleCat.ExtendRestrictScalarsAdj.unit ((q.hom.app V).hom)).app
            (F.val.obj V)) =
      (ModuleCat.ExtendRestrictScalarsAdj.unit ((q.hom.app U).hom)).app
          (F.val.obj U) ≫
        ((PresheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom).obj
            (changeOfRingsPresheaf q F)).map f := by
  sorry

/-- The sectionwise unit into the tensor presheaf, with components `m ↦ 1 ⊗ m`.
Source: Stacks, Modules on Sites, Tag 03EK
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism). -/
noncomputable def integralTensorQuotientPresheafUnit
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    F.val ⟶ (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom).obj
      (changeOfRingsPresheaf q F) where
  app U := (ModuleCat.ExtendRestrictScalarsAdj.unit
    ((q.hom.app U).hom)).app (F.val.obj U)
  naturality f := integralTensorQuotientPresheafUnit_naturality q F f

/-- The canonical unit into the sheafified tensor quotient: compose `m ↦ 1 ⊗ m`
with the module-sheafification unit and restrict the target scalars along `q`.
Source: Stacks, Modules on Sites, Tags 03CY and 03EK
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism). -/
noncomputable def integralTensorQuotientUnit
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    F ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map q)).obj (changeOfRings q F) where
  val := integralTensorQuotientPresheafUnit q F ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
        (changeOfRingsPresheaf q F))

/-- If a sheaf map of commutative rings is locally surjective, then the scalar-extension
unit is locally surjective and epic as a map of sheaves of modules.

Source: Bhatt--Scholze, *Pro-étale topology*, Proposition 6.8.4(1), p. 59
(blueprint: lem-sfb-integral-tensor-quotient-epimorphism).
Proof: sections of the sheafified tensor product are locally represented by finite sums of
pure tensors; local surjectivity of `q` lifts their finitely many coefficients on a common
refinement, so each local section is `1 ⊗ m`. Right cancellation follows from the sheaf
uniqueness axiom. -/
theorem integral_tensor_quotient_epimorphism
    {R₀ R : Sheaf J CommRingCat.{u}} (q : R₀ ⟶ R)
    (hq : Presheaf.IsLocallySurjective J
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map q).hom)
    (F : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀)) :
    Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R₀).obj).map
          (integralTensorQuotientUnit q F).val) ∧
      Epi (integralTensorQuotientUnit q F) := by
  sorry

end SheafOfModules
