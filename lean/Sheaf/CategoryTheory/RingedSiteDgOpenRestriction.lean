module

public import Sheaf.CategoryTheory.RingedSiteDgModules
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal

/-! # Open restriction for sheaf dg modules

Source: Stacks Project, sdga.tex, restriction to opens and Tags 0FTF, 0FTR
(blueprint: def-sfb-ringed-site-dg-open-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

/-- Slice sites retain the same size bound.
Source: Stacks sdga, conventions (blueprint: def-sfb-ringed-site-dg-open-restriction). -/
instance overSmall (U : C) : EssentiallySmall.{u} (Over U) :=
  inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 C) U))

variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Restrict the actual coefficient complexes to the slice site.
Source: Stacks sdga, restriction to opens
(blueprint: def-sfb-ringed-site-dg-open-restriction). -/
def overComplex (U : C) : Complex O ⥤ Complex (O.over U) :=
  letI := module_overFunctor_preservesZero
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) U
  (SheafOfModules.overFunctor
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) U).mapHomologicalComplex
      (.up ℤ)

set_option maxHeartbeats 600000 in
-- Sectionwise slice comparisons elaborate many sheaf-tensor transports.
/-- Restriction of an algebra and its modules, characterized on every section of
its underlying complexes, including the multiplication and action. No arbitrary
change of dg action is permitted. Source: Stacks sdga, restriction to opens
(blueprint: def-sfb-ringed-site-dg-open-restriction). -/
structure OpenRestriction (U : C) (A : Algebra O) (AU : Algebra (O.over U)) where
  algebraIso : AU.X ≅ (overComplex.{c, v, u} (O := O) U).obj A.X
  multiplication (p q : ℤ) (V : (Over U)ᵒᵖ)
      (a : (AU.X.X p).val.obj V) (b : (AU.X.X q).val.obj V) :
    (algebraIso.hom.f (p + q)).val.app V (multiplySection AU p q V a b) =
      multiplySection A p q (Opposite.op V.unop.left)
        ((algebraIso.hom.f p).val.app V a) ((algebraIso.hom.f q).val.app V b)
  module : Module A ⥤ Module AU
  underlyingIso : module ⋙ underlying AU ≅ underlying A ⋙ overComplex.{c, v, u} (O := O) U
  action (M : Module A) (p q : ℤ) (V : (Over U)ᵒᵖ)
      (m : (((underlying AU).obj (module.obj M)).X p).val.obj V)
      (a : (AU.X.X q).val.obj V) :
    ((underlyingIso.hom.app M).f (p + q)).val.app V
        (actionSection (module.obj M) p q V m a) =
      actionSection M p q (Opposite.op V.unop.left)
        (((underlyingIso.hom.app M).f p).val.app V m) ((algebraIso.hom.f q).val.app V a)
  derived : Derived A ⥤ Derived AU
  derivedIso : Q A ⋙ derived ≅ module ⋙ Q AU

/-- Open compatibility of the scalar adjunction, including its unit and action counit.
The restriction comparison is the literal one: `moduleIso` is the identity of underlying
restricted complexes (`moduleIso_underlying`), and `restrictionIso_eq` fixes the derived
comparison at every localized module as the transport of `moduleIso` through the given
localization factorizations. The unit and counit squares then fix the extension comparison
as its mate. Source: Stacks sdga, Tags 0FSH, 0FTF, 0FTR
(blueprint: def-sfb-ringed-site-dg-open-restriction). -/
structure OpenCompatibility {A B : Algebra O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] (s : ScalarModel φ)
    (U : C) (AU BU : Algebra (O.over U)) (φU : AU ⟶ BU)
    [DerivedStructure AU] [DerivedStructure BU] (sU : ScalarModel φU) where
  source : OpenRestriction U A AU
  target : OpenRestriction U B BU
  map_eq : φU.hom ≫ target.algebraIso.hom = source.algebraIso.hom ≫
    (overComplex.{c, v, u} (O := O) U).map φ.hom
  moduleIso : RingedSiteDg.restriction φ ⋙ source.module ≅
    target.module ⋙ RingedSiteDg.restriction φU
  moduleIso_underlying (N : Module B) :
    (underlying AU).map (moduleIso.hom.app N) =
      source.underlyingIso.hom.app ((RingedSiteDg.restriction φ).obj N) ≫
        target.underlyingIso.inv.app N
  restrictionIso : s.restriction ⋙ source.derived ≅ target.derived ⋙ sU.restriction
  restrictionIso_eq (N : Module B) :
    restrictionIso.hom.app ((Q B).obj N) =
      source.derived.map (s.restrictionIso.hom.app N) ≫
        source.derivedIso.hom.app ((RingedSiteDg.restriction φ).obj N) ≫
        (Q AU).map (moduleIso.hom.app N) ≫
        sU.restrictionIso.inv.app (target.module.obj N) ≫
        sU.restriction.map (target.derivedIso.inv.app N)
  extensionIso : s.extension ⋙ target.derived ≅ source.derived ⋙ sU.extension
  unit (M : Derived A) :
    source.derived.map (s.adjunction.unit.app M) ≫
      restrictionIso.hom.app (s.extension.obj M) ≫
      sU.restriction.map (extensionIso.hom.app M) =
        sU.adjunction.unit.app (source.derived.obj M)
  counit (N : Derived B) :
    (extensionIso.inv.app (s.restriction.obj N)) ≫
      target.derived.map (s.adjunction.counit.app N) =
        sU.extension.map (restrictionIso.hom.app N) ≫
          sU.adjunction.counit.app (target.derived.obj N)

/-- An open restriction of a fixed normalized scalar system, with no existence assumed.
Source: Stacks sdga, restriction to opens and 0FTR
(blueprint: def-sfb-ringed-site-dg-open-restriction). -/
structure OpenScalarSystem {A B : Algebra O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] (s : ScalarModel φ) (U : C) where
  sourceAlgebra : Algebra (O.over U)
  targetAlgebra : Algebra (O.over U)
  map : sourceAlgebra ⟶ targetAlgebra
  [sourceStructure : DerivedStructure sourceAlgebra]
  [targetStructure : DerivedStructure targetAlgebra]
  model : ScalarModel map
  compatibility : OpenCompatibility φ s U sourceAlgebra targetAlgebra map model

end CategoryTheory.RingedSiteDg
