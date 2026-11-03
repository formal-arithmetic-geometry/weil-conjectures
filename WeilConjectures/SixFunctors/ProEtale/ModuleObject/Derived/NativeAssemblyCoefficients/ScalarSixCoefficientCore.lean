/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

/-! # Native scalar change and its pullback mate

The existing scalar coefficient definitions, moved verbatim from ScalarSixDefinitions
so the ambient three-operation datum does not import locally closed extension theory.
Source: current blueprint coefficient-change definitions and pullback mate.
(blueprint: def-sfb-scalar-six-coefficient-interfaces).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u u₁ u₂ v₁ v₂

-- B3 (def-sf-native-assembly-coefficient-core): native namespace, kept beside G2's
-- coefficient interfaces (G2 b05dffb11058 had replaced the module body).
section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeAssemblyCoefficients

/-- Bundled parameters for commutative condensed coefficients.
Source: blueprint coefficient change (blueprint: det-prop-scalar-six-pullback). -/
abbrev ScalarSixRing := CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Expose the left functor already specified by an adjunction. This avoids rebuilding
its K-flat tensor instances when specializing the published scalar adjunction.
Source: blueprint coefficient change (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixAdjunctionLeft {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (_adj : F ⊣ G) : C ⥤ D := F

/-- Ordinary unbounded derived scalar extension, using the published coefficient map
and the left functor of its derived adjunction (definitionally L(Ext)).
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
def scalarSixChange {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X) :=
  scalarSixAdjunctionLeft (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))

/-- Exact inverse image applied termwise. This is canonically the total derived pullback.
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixPull (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  D((f)^*⟦Λ.X⟧)

/-- The canonical non-flat pullback comparison, the scalar-adjunction mate of the
identity-on-underlying-sheaves restriction comparison `derivedComapUpperStarIso`.
Source: blueprint proof (1), steps 1--2 (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixPullHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull Λ f ⋙ scalarSixChange a X ⟶
      scalarSixChange a Y ⋙ scalarSixPull Λ' f :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)

/-- The ordinary, exact inverse-image compositor, localized termwise.
Source: blueprint clause (1) (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixPullComp (Λ : ScalarSixRing.{u}) {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ W) :
    scalarSixPull Λ (f ≫ g) ≅ scalarSixPull Λ g ⋙ scalarSixPull Λ f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ.X f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The tensor associator, fixed as the conjugate of transitivity of exact restriction.
On K-flat representatives its formula is c tensor (b tensor m) to cb tensor m.
Source: blueprint proof (3), step 7 (blueprint: det-prop-scalar-six-pullback). -/
abbrev scalarSixTower {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (X : Scheme.{u}) :
    scalarSixChange a X ⋙ scalarSixChange b X ≅ scalarSixChange (a ≫ b) X :=
  (conjugateIsoEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X))
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X)))).symm
    (Functor.mapDerivedCategoryNatIso
        (Mod.comapCongr (coefficientMap_comp (Λ := Λ.X) (Λ' := Λ'.X) (Λ'' := Λ''.X)
          a.hom.hom b.hom.hom X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapComp _ _ ) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)

/-- Clause (1), with its canonical normalization, and the inverse-image square of (3).
All coefficient maps are allowed, including non-flat maps.
Source: blueprint clauses (1), (3) (blueprint: det-prop-scalar-six-pullback). -/
structure ScalarSixPullbackData where
  theta : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y),
    scalarSixPull Λ f ⋙ scalarSixChange a X ≅ scalarSixChange a Y ⋙ scalarSixPull Λ' f
  thetaNormalization : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y), (theta a f).hom = scalarSixPullHom a f
  composition : ∀ {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)),
    (theta a (f ≫ g)).hom.app K ≫
        (scalarSixPullComp Λ' f g).hom.app ((scalarSixChange a W).obj K) =
      (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app K) ≫
        (theta a f).hom.app ((scalarSixPull Λ g).obj K) ≫
          (scalarSixPull Λ' f).map ((theta a g).hom.app K)
  tower : ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
    (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj K) ≫
        (theta (a ≫ b) f).hom.app K =
      (scalarSixChange b X).map ((theta a f).hom.app K) ≫
        (theta b f).hom.app ((scalarSixChange a Y).obj K) ≫
          (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app K)


/-- The canonical strong monoidal structure on the existing scalar-change functor.
Its inverse tensorator is the K-flat derived tensor comparison; the unit comparison
is scalar extension of the regular module. This uses no flatness hypothesis on the map.
Source: blueprint det-prop-scalar-six-tensor-hom (1)
(blueprint: def-sf-native-assembly-coefficient-core). -/
noncomputable instance scalarSixChangeMonoidal {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (X : Scheme.{u}) : (scalarSixChange a X).Monoidal :=
  letI := Mod.extendScalarsMonoidal
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  (Mod.extendScalars
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).leftDerivedFunctorMonoidal

/-- The natural tensor comparison on all unbounded derived objects. Its naturality,
associativity and both unit coherences are the fields of `scalarSixChangeMonoidal`.
Source: blueprint det-prop-scalar-six-tensor-hom (1)
(blueprint: def-sf-native-assembly-coefficient-core). -/
def scalarSixTensorIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a X).obj (K ⊗ M) ≅
      (scalarSixChange a X).obj K ⊗ (scalarSixChange a X).obj M :=
  (Functor.Monoidal.μIso (scalarSixChange a X) K M).symm


end AlgebraicGeometry.ProEtale.CondensedRing.NativeAssemblyCoefficients

end

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
