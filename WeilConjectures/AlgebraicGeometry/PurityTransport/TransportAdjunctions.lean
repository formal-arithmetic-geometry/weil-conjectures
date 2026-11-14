/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Smooth purity on the condensed finite-Tor categories
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- The actual object property defining Dctf, reusing its recorded owner. -/
abbrev property (c : Coefficient ell) (X : Scheme.{u}) :
    ObjectProperty (c.derived ell X) :=
  constantModelBoundedConstructible (c.obj ell) X ⊓
    (fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)

/-- The same localizing closure on which the published Brown adjoint is defined. -/
abbrev localizing (c : Coefficient ell) (X : Scheme.{u}) :=
  localizingClosureProEtale (c.obj ell) X

/-- The canonical full inclusion into the localizing constructible closure.
Only its object-membership proof uses the closure universal property. -/
def inclusion (c : Coefficient ell) (X : Scheme.{u}) :
    c.ctf ell X ⥤ (localizing ell c X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- The compact-support functor is precisely Rp_* j_!, with its membership
proof supplied separately; neither its objects nor its maps are chosen. -/
def support (c : Coefficient ell) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (compactification : Compactification f)
    (preserves : ∀ K, property ell c X K → property ell c Y
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) compactification).obj K)) :
    c.ctf ell X ⥤ c.ctf ell Y :=
  (property ell c Y).lift
    ((property ell c X).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) compactification)
    (fun K ↦ preserves K.obj K.property)

/-- Restrict the literal twisted and shifted inverse image to Dctf. -/
def source (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (preserves : ∀ K, property ell c Y K → property ell c X
      ((c.smoothSource ell f d).obj K)) : c.ctf ell Y ⥤ c.ctf ell X :=
  (property ell c X).lift ((property ell c Y).ι ⋙ c.smoothSource ell f d)
    (fun K ↦ preserves K.obj K.property)

/-- The exceptional inverse image is the restriction of the actual localizing
right adjoint, through the canonical full inclusion. -/
def exceptional (c : Coefficient ell) {X Y : Scheme.{u}}
    (G : (localizing ell c Y).FullSubcategory ⥤ (localizing ell c X).FullSubcategory)
    (preserves : ∀ K : c.ctf ell Y,
      property ell c X (G.obj ((inclusion ell c Y).obj K)).obj) :
    c.ctf ell Y ⥤ c.ctf ell X :=
  (property ell c X).lift
    (inclusion ell c Y ⋙ G ⋙ (localizing ell c X).ι) preserves

/-- The counit equation selecting gamma, in Lean's diagrammatic order. -/
def CounitCompatible {A B : Type (u + 2)} [Category A] [Category B]
    {F : A ⥤ B} {J G : B ⥤ A} (a : F ⊣ J) (b : F ⊣ G)
    (gamma : J ≅ G) : Prop :=
  ∀ K : B, F.map (gamma.hom.app K) ≫ b.counit.app K = a.counit.app K

end AlgebraicGeometry.ProEtale.PurityTransport
