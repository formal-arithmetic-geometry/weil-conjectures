/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Unbounded derived direct image on ringed spaces

Source: Stacks Project, Cohomology, Section 20.28 (Tag 079V), construction preceding
Tag 079W (blueprint: def-pc-ringed-spaces-derived-direct-image).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The Grothendieck structure on module sheaves on the small site of opens.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
instance moduleGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X)

/-- Specialization of Mathlib's module pushforward to a ringed-space morphism.
Its sections on V are the sections on the inverse image of V, with scalar action
through g-sharp, and its map on morphisms is the component on that inverse image.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
def moduleDirectImage {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    SheafOfModules.{u} (moduleRings X) ⥤ SheafOfModules.{u} (moduleRings Y) :=
  SheafOfModules.pushforward (F := Opens.map g.hom.base)
    (R := moduleRings X) (S := moduleRings Y)
    ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩

/-- Module direct image is additive, hence its termwise action carries homotopies
and homotopy equivalences to homotopies and homotopy equivalences.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: sums and zero maps of module sheaves are computed on sections. Direct image
uses exactly the same maps on inverse-image opens, so preserves these operations. -/
theorem moduleDirectImage_additive_proof {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    (moduleDirectImage g).Additive := by
  constructor
  intro M N f h
  ext
  rfl

/-- Additivity of module direct image. Source: Stacks, Tag 079V
(blueprint: def-pc-ringed-spaces-derived-direct-image). -/
instance moduleDirectImage_additive {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    (moduleDirectImage g).Additive := moduleDirectImage_additive_proof g

variable {X Y : RingedSpace.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]

/-- Resolve functorially, apply direct image termwise, and localize on the target.
The resolution functor and its natural quasi-isomorphism are the existing
`CochainComplex.kInjectiveResolutionFunctor` and `toKInjectiveResolution`.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
def resolvedModuleDirectImage (g : X ⟶ Y) :
    CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) :=
  CochainComplex.kInjectiveResolutionFunctor.{u} (SheafOfModules.{u} (moduleRings X)) ⋙
    (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

-- Keep the original source-derived-category parameter for compatibility.
set_option linter.unusedSectionVars false in
/-- Resolved direct image inverts quasi-isomorphisms.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: naturality of the resolution map and two-out-of-three show that I(s) is a
quasi-isomorphism when s is one. Both its endpoints are K-injective. By
`CochainComplex.IsKInjective.quasiIso_iff` (lem-weil-pbc-kinjective-hom-derived),
I(s) is a homotopy equivalence. Additive direct image preserves this equivalence,
and the target localization therefore sends it to an isomorphism. -/
theorem resolvedModuleDirectImage_inverts (g : X ⟶ Y) :
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (moduleRings X))
      (ComplexShape.up ℤ)).IsInvertedBy (resolvedModuleDirectImage g) := by
  intro K L s hs
  let C := SheafOfModules.{u} (moduleRings X)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  have : QuasiIso s := hs
  have : QuasiIso (η.app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
  have : QuasiIso (η.app L) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C L).2
  have : QuasiIso (η.app K ≫ I.map s) := by
    rw [← η.naturality s]
    dsimp
    infer_instance
  have : QuasiIso (I.map s) := quasiIso_of_comp_left (η.app K) (I.map s)
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (I.map s)).mp inferInstance
  have : QuasiIso (((moduleDirectImage g).mapHomologicalComplex (.up ℤ)).map
      (I.map s)) := by
    rw [← he]
    exact (moduleDirectImage g).mapHomotopyEquiv e |>.quasiIso_hom
  change IsIso (DerivedCategory.Q.map
    (((moduleDirectImage g).mapHomologicalComplex (.up ℤ)).map (I.map s)))
  infer_instance

/-- The unbounded derived direct image: the right derived functor
`CategoryTheory.Functor.rightDerivedFunctor` (the landed unbounded right derived functor
of an additive functor on a category with K-injective resolutions) of the module direct
image. It is computed by K-injective resolutions: its unit is an isomorphism on every
K-injective complex. The K-injective resolutions come from `moduleGrothendieckAbelian`.
Source: Stacks, Tag 079V, preceding Tag 079W
(blueprint: def-pc-ringed-spaces-derived-direct-image). -/
abbrev derivedModuleDirectImage (g : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) :=
  (moduleDirectImage g).rightDerivedFunctor

/-- The defining comparison: Q followed by Rg-star is isomorphic to the functorial
K-injective resolution followed by termwise g-star and Q, so Rg-star(QK) = Q(g-star I(K))
and Rg-star(Q f) = Q(g-star I(f)) up to this natural isomorphism.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: the unit of the right derived functor is an isomorphism on the K-injective
complexes I(K); compose it with Rg-star applied to the inverse of Q of the natural
quasi-isomorphism K to I(K), which is natural in K. -/
theorem derivedModuleDirectImageFactorization (g : X ⟶ Y) :
    Nonempty (DerivedCategory.Q ⋙ derivedModuleDirectImage g ≅ resolvedModuleDirectImage g) := by
  let C := SheafOfModules.{u} (moduleRings X)
  let D := SheafOfModules.{u} (moduleRings Y)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let H := HomotopyCategory.quotient C (.up ℤ)
  let F := moduleDirectImage g
  let α := Functor.whiskerLeft (I ⋙ H) F.rightDerivedFunctorUnit
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    dsimp [α, H]
    infer_instance
  have : IsIso (Functor.whiskerRight η DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    have : QuasiIso (η.app K) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
    change IsIso (DerivedCategory.Q.map (η.app K))
    infer_instance
  exact ⟨Functor.isoWhiskerRight (asIso (Functor.whiskerRight η DerivedCategory.Q))
      F.rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm
        F.rightDerivedFunctor) ≪≫
    (asIso α).symm ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft (I ⋙ F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D)⟩

/-- Any K-injective resolution computes the same derived direct image.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: the bijection `CochainComplex.IsKInjective.Qh_map_bijective` lifts the
isomorphism QI(K) to QJ to a homotopy class I(K) to J. Its representative is a
quasi-isomorphism and therefore a homotopy equivalence by `quasiIso_iff`.
Apply additive direct image and Q, and compose with the defining factorization
(equivalently: the unit of the right derived functor is an isomorphism at J). -/
theorem derivedModuleDirectImage_computed_by_resolution (g : X ⟶ Y)
    {K J : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ}
    (s : K ⟶ J) [QuasiIso s] [J.IsKInjective] :
    Nonempty ((derivedModuleDirectImage g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) := by
  exact ⟨(moduleDirectImage g).rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map s)) ≪≫
    (moduleDirectImage g).rightDerivedFunctorObjQIso J⟩

end AlgebraicGeometry.RingedSpace
