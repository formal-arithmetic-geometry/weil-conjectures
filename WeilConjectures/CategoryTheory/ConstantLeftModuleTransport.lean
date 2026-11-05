/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Exact inverse image for constant left-module sheaves

Source: Stacks Project, Sites, Proposition 00YV (2), (5), (6), its fixed-ring
scalar-endomorphism proof, and Section 00XZ; Derived Categories, Tag 015F
(auxiliary; not a blueprint node).

The lift is characterized by its underlying-set comparison, addition and scalar
endomorphisms, and the original geometric adjunction unit. Comparisons have a
normalization equation and uniqueness; arbitrary unrelated functors are never compared.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
namespace ConstantLeftModuleInverseImage

/-- Forget the abelian group structure.
Source: Stacks, 00YV (2) (auxiliary; not a blueprint node). -/
abbrev U {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
  sheafCompose J (forget AddCommGrpCat.{u})

end ConstantLeftModuleInverseImage
open ConstantLeftModuleInverseImage

/-! The coefficient comparison is natural in the constant type. Binary operations
are compared after the isomorphism from the constant sheaf on pairs. -/
section CoefficientConstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
variable (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
variable (adj : L ⊣ R) [PreservesFiniteLimits L]
private def pointTerminal : IsTerminal ((constantSheaf J (Type u)).obj PUnit.{u+1}) := by
  exact (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type u)) _
private def pointComparison :
    L.obj ((constantSheaf J (Type u)).obj PUnit.{u+1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u+1} :=
  ((pointTerminal J).isTerminalObj L _).uniqueUpToIso (pointTerminal K)
private def globalComparison : R ⋙ Sheaf.Γ J (Type u) ≅ Sheaf.Γ K (Type u) := by
  exact Functor.isoWhiskerLeft R (Sheaf.ΓNatIsoCoyoneda J PUnit.{u+1}) ≪≫
    (adj.compCoyonedaIso.app (op ((constantSheaf J (Type u)).obj PUnit.{u+1}))).symm ≪≫
    coyoneda.mapIso (pointComparison J K L).symm.op ≪≫
    (Sheaf.ΓNatIsoCoyoneda K PUnit.{u+1}).symm
private def constantComparison :
    constantSheaf J (Type u) ⋙ L ≅ constantSheaf K (Type u) :=
  (((constantSheafΓAdj J (Type u)).comp adj).ofNatIsoRight
    (globalComparison J K L R adj)).leftAdjointUniq (constantSheafΓAdj K (Type u))

variable (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]

omit [HasWeakSheafify J RingCat.{u}] in
private theorem constantMap_unit (X Y : Type u) (f : X → Y) (T : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type u)).map (TypeCat.ofHom f)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app T x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app T (f x) := by
  exact (congrArg (fun g ↦ g.app T x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

open ConstantLeftModuleInverseImage
end CoefficientConstruction

/-! Lift left exact functors to abelian sheaves sectionwise, transport the constant
scalar endomorphisms, and extend them along ring sheafification. -/
section TransportConstruction
set_option linter.unusedSimpArgs false
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

variable {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
  {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
  (F : A ⥤ Sheaf K (Type u)) [PreservesFiniteLimits F]

section AbelianAdjunction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
private instance forgetAbLimits : PreservesFiniteLimits (U J) := by
  have : PreservesFiniteLimits (U J ⋙ sheafToPresheaf J (Type u)) := by
    change PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))

private instance abBiproducts : HasFiniteBiproducts (Sheaf J AddCommGrpCat.{u}) :=
  .of_hasFiniteProducts

variable (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  [PreservesFiniteLimits L] [PreservesFiniteLimits R]
  (adj : L ⊣ R)

end AbelianAdjunction

section ModuleAction
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]

variable (B : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u}) [B.Additive]

variable [HasWeakSheafify K RingCat.{u}]
  (B' : Sheaf K AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}) [B'.Additive]
  (a : B ⊣ B')

end ModuleAction
section Assembly
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
  [HasWeakSheafify K RingCat.{u}]
  (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : L ⊣ R) (hL : PreservesFiniteLimits L)

end Assembly

end TransportConstruction

end CategoryTheory
