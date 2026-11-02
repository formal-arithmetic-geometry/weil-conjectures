/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.DeligneLaumon.FiniteFieldDatum.CondensedFiniteEtaleLissePushforward

/-! # Native condensed derived Weil framework

Source: the latest blueprint, def-weil-weil-sheaf-complex (Weil modules and complexes),
prop-functor-package clauses 2--3, def-fix-six-functor-datum clauses 1--2, and
lem-zl-morphism-open-closed-reduction.proof Part 1.
(blueprint: def-sf-native-weil-derived-framework)

All categories below are the recorded native condensed module categories. The operations
are constructed from their actual module functors and the canonical Frobenius comparisons.
The ambient derived category is localized before imposing bounded constructibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC vC uD vD wC wD wF wH

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Module objects over the pulled-back condensed coefficient on a scheme.
Source: coefficient/category conventions (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilModuleCategory
    (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell) (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (WeilCoefficient.ab c) T)

/-- The fixed-pair category of Weil modules on a geometric fibre.
Source: coefficient/category conventions (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilModulePairCategory
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :=
  condensedWeilModules (WeilCoefficient.ab c)
    (D.geometricFrobenius Y₀).hom

/-- The derived category of Weil modules on a geometric fibre.
Source: coefficient/category conventions (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilDerivedPairCategory
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :=
  DerivedCategory (nativeWeilModulePairCategory D ell c Y₀)

/-- Exact forgetting from the ambient ordinary derived category of Weil modules.
Source: forgetful functor clause (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilDerivedForget
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :=
  (condensedWeilModuleForget (WeilCoefficient.ab c)
    (D.geometricFrobenius Y₀).hom).mapDerivedCategory

/-- The induced Frobenius structure on a forgotten derived Weil object.
Source: theta_K clause (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilDerivedStructure
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :=
  condensedWeilDerivedStructure (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom

section Operations

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (gX : Aut X) (gY : Aut Y) (f : X ⟶ Y)
  (sq : CommSq gX.hom f f gY.hom)

/-- Pullback along an automorphism, with inverse the pullback along its inverse.
The composition and coefficient identifications are the native ones.
Source: Weil-lift convention (blueprint: def-sf-native-weil-derived-framework). -/
def nativeWeilFrobeniusEquivalence {T : Scheme.{u}} (g : Aut T) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ≌
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) :=
  CategoryTheory.Equivalence.mk (CondensedRing.upperStar Λ g.hom) (CondensedRing.upperStar Λ g.inv)
    ((CondensedRing.upperStarId Λ T).symm ≪≫
      CondensedRing.upperStarCongr Λ g.inv_hom_id.symm ≪≫
      CondensedRing.upperStarComp Λ g.inv g.hom)
    ((CondensedRing.upperStarComp Λ g.hom g.inv).symm ≪≫
      CondensedRing.upperStarCongr Λ g.hom_inv_id ≪≫ CondensedRing.upperStarId Λ T)

/-- Canonical Weil lift of the actual condensed module inverse image. Its structure is
`c_G` followed by `G.mapIso theta`; its maps are the underlying module pullbacks.
Source: displayed lift formula (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilModulePullback :
    condensedWeilModules Λ gY.hom ⥤ condensedWeilModules Λ gX.hom :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison Λ sq).symm

/-- Canonical Weil lift of the actual condensed module direct image. The exchange
isomorphism is the mate of pullback composition along the Frobenius square. For
horizontal automorphisms this is equivalently direct-image composition using
`g^* = (g⁻¹)_*`.
Source: displayed lift formula (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilModuleDirectImage :
    condensedWeilModules Λ gX.hom ⥤ condensedWeilModules Λ gY.hom :=
  Endofunctor.IsoAlgebra.mapOfNatIso (asIso (CondensedRing.lowerStarBaseChange Λ sq))

/-- The extension-by-zero reindexing comparison. It is the conjugate of the canonical
comparison of the right adjoints along the inverse automorphisms; thus no arbitrary
comparison or additional descent datum is supplied.
Source: open-extension lift convention (blueprint: def-sf-native-weil-derived-framework). -/
def nativeWeilOpenComparison [IsOpenImmersion f] :
    CondensedRing.openImmersionLowerShriek Λ f ⋙ CondensedRing.upperStar Λ gY.hom ≅
      CondensedRing.upperStar Λ gX.hom ⋙ CondensedRing.openImmersionLowerShriek Λ f :=
  (conjugateIsoEquiv
    ((nativeWeilFrobeniusEquivalence Λ gX).toAdjunction.comp
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ f))
    ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ f).comp
      (nativeWeilFrobeniusEquivalence Λ gY).toAdjunction)).symm
    (CondensedRing.upperStarSquareComparison Λ sq.horiz_inv).symm

/-- Canonical Weil lift of exact condensed extension by zero.
Source: displayed lift formula (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilModuleOpenExtension [IsOpenImmersion f] :
    condensedWeilModules Λ gX.hom ⥤ condensedWeilModules Λ gY.hom :=
  Endofunctor.IsoAlgebra.mapOfNatIso (nativeWeilOpenComparison Λ gX gY f sq)

/-- Ambient Weil pullback is termwise pullback, followed by ordinary localization.
Source: ambient operations (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilAmbientPullback :
    DerivedCategory (condensedWeilModules Λ gY.hom) ⥤
      DerivedCategory (condensedWeilModules Λ gX.hom) :=
  (nativeWeilModulePullback Λ gX gY f sq).mapDerivedCategory

/-- Ambient Weil open extension is termwise exact extension, followed by localization.
Source: ambient operations (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilAmbientOpenExtension [IsOpenImmersion f] :
    DerivedCategory (condensedWeilModules Λ gX.hom) ⥤
      DerivedCategory (condensedWeilModules Λ gY.hom) :=
  (nativeWeilModuleOpenExtension Λ gX gY f sq).mapDerivedCategory

end Operations

/-- K-injective resolutions, in the arbitrary-quasi-isomorphism format used for total
right derivation. Source: K-injective paragraph and its recorded Grothendieck
K-injective dependency (blueprint: def-sf-native-weil-derived-framework).

Proof: for each K, apply `HasKInjectiveResolutions.exists_isKInjective K`. It supplies
I, the K-injective instance, a map s, its monomorphism instance, and its quasi-isomorphism
instance. Retain I, s, K-injectivity and the quasi-isomorphism, dropping only the
monomorphism condition. The Grothendieck instances provide the hypothesis in every use. -/
theorem nativeWeilResolutions (C : Type uC) [Category.{vC} C] [Abelian C]
    [Abelian.HasKInjectiveResolutions C] :
    ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s := by
  sorry

section DerivedDirectImage

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (gX : Aut X) (gY : Aut Y) (f : X ⟶ Y)
  (sq : CommSq gX.hom f f gY.hom)

/-- Total right derivation of the actual lifted direct image, using K-injectives in
Weil modules, rather than in a strict pair category of already derived modules.
Source: ambient direct image (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilAmbientDirectImage :
    DerivedCategory (condensedWeilModules Λ gX.hom) ⥤
      DerivedCategory (condensedWeilModules Λ gY.hom) :=
  (nativeWeilModuleDirectImage Λ gX gY f sq).rightDerivedFunctorOfQuasiIsoResolutions
    (nativeWeilResolutions _)

/-- Exact pullback forgets to the termwise condensed operation through the canonical
composition comparison of localized functors.
Source: exact forgetting clause (blueprint: def-sf-native-weil-derived-framework). -/
def nativeWeilPullbackForget :
    nativeWeilAmbientPullback Λ gX gY f sq ⋙
        (condensedWeilModuleForget Λ gX.hom).mapDerivedCategory ≅
      (condensedWeilModuleForget Λ gY.hom).mapDerivedCategory ⋙
        (CondensedRing.upperStar Λ f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
      (CondensedRing.upperStarSquareComparison Λ sq).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Exact open extension forgets to the termwise condensed operation.
Source: exact forgetting clause (blueprint: def-sf-native-weil-derived-framework). -/
def nativeWeilOpenExtensionForget [IsOpenImmersion f] :
    nativeWeilAmbientOpenExtension Λ gX gY f sq ⋙
        (condensedWeilModuleForget Λ gY.hom).mapDerivedCategory ≅
      (condensedWeilModuleForget Λ gX.hom).mapDerivedCategory ⋙
        (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
      (nativeWeilOpenComparison Λ gX gY f sq)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end DerivedDirectImage

section FiniteField

variable (D : FiniteFieldDatum.{u})
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The geometric base change of a finite-field morphism commutes with geometric Galois
Frobenius. Source: Frobenius-square clause of the framework and the geometric Galois
Frobenius definition (blueprint: def-sf-native-weil-derived-framework).

Proof: expand the geometric fibre as the pullback over `Spec k₀`. Its map leaves the
closure coordinate unchanged, while Galois Frobenius leaves the model coordinate
unchanged and applies the inverse field Frobenius on the closure coordinate. The two
composites therefore have equal projections to the model and to `Spec k`; the pullback
universal property equates them. The argument includes empty schemes and identity maps. -/
theorem nativeWeilGeometricSquare (h₀ : X₀ ⟶ Y₀) :
    CommSq (D.geometricFrobenius X₀).hom (D.geometricFiberMap h₀)
      (D.geometricFiberMap h₀) (D.geometricFrobenius Y₀).hom := by
  sorry

/-- Geometric base change preserves the open-immersion hypothesis by the recorded
base-change stability of that morphism property.
Source: open-extension clause (blueprint: def-sf-native-weil-derived-framework). -/
instance nativeWeilGeometricOpen (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :
    IsOpenImmersion (D.geometricFiberMap j₀) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

/-- Weil inverse image for the geometric base change of a finite-field morphism.
Source: ambient operations (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilPullback (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (h₀ : X₀ ⟶ Y₀) :=
  nativeWeilAmbientPullback (WeilCoefficient.ab c)
    (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀)
    (D.geometricFiberMap h₀) (nativeWeilGeometricSquare D h₀)

/-- Weil total direct image for the geometric base change of a finite-field morphism.
Source: ambient operations (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilDirectImage (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (h₀ : X₀ ⟶ Y₀) :=
  nativeWeilAmbientDirectImage (WeilCoefficient.ab c)
    (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀)
    (D.geometricFiberMap h₀) (nativeWeilGeometricSquare D h₀)

/-- Weil extension by zero for a finite-field open immersion, computed termwise.
Source: ambient operations (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilOpenExtension (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (j₀ : X₀ ⟶ Y₀) [IsOpenImmersion j₀.left] :=
  letI := nativeWeilGeometricOpen D j₀
  nativeWeilAmbientOpenExtension (WeilCoefficient.ab c)
    (D.geometricFrobenius X₀) (D.geometricFrobenius Y₀)
    (D.geometricFiberMap j₀) (nativeWeilGeometricSquare D j₀)

/-- Regard the compactifying scheme as a finite-field scheme using its proper map.
Source: chosen compactification clause (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilCompactificationModel (h₀ : X₀ ⟶ Y₀)
    (c₀ : Compactification h₀.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c₀.g ≫ Y₀.hom)

/-- The compactification's open map respects the finite-field structure morphisms.
Source: compactification factorization (blueprint: def-sf-native-weil-derived-framework).

Proof: reassociate c₀.i followed by c₀.g followed by Y₀.hom, replace c₀.i followed
by c₀.g with h₀.left using c₀.comm, and apply the over-morphism equation h₀.w.
This requires no separatedness of either model over the finite field. -/
theorem nativeWeilCompactificationOpenOver (h₀ : X₀ ⟶ Y₀)
    (c₀ : Compactification h₀.left) :
    c₀.i ≫ (c₀.g ≫ Y₀.hom) = X₀.hom := by
  sorry

/-- The open map of a compactification as a map over the finite field.
Source: compactification factorization (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilCompactificationOpen (h₀ : X₀ ⟶ Y₀)
    (c₀ : Compactification h₀.left) :
    X₀ ⟶ nativeWeilCompactificationModel D h₀ c₀ :=
  Over.homMk c₀.i (nativeWeilCompactificationOpenOver D h₀ c₀)

/-- The proper map of a compactification as a map over the finite field.
Source: compactification factorization (blueprint: def-sf-native-weil-derived-framework). -/
abbrev nativeWeilCompactificationProper (h₀ : X₀ ⟶ Y₀)
    (c₀ : Compactification h₀.left) :
    nativeWeilCompactificationModel D h₀ c₀ ⟶ Y₀ :=
  Over.homMk c₀.g

/-- Ambient compact support for the chosen compactification: exact Weil open extension
FIRST, then total right-derived Weil proper direct image. The middle Frobenius is the
geometric Galois Frobenius on the same finite-field compactification model.
Source: displayed compact-support formula (blueprint: def-sf-native-weil-derived-framework). -/
def nativeWeilCompactSupport (ell : ℕ) [Fact ell.Prime] (c : WeilCoefficient ell)
    (h₀ : X₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    nativeWeilDerivedPairCategory D ell c X₀ ⥤ nativeWeilDerivedPairCategory D ell c Y₀ :=
  nativeWeilOpenExtension D ell c (nativeWeilCompactificationOpen D h₀ c₀) ⋙
    nativeWeilDirectImage D ell c (nativeWeilCompactificationProper D h₀ c₀)

end FiniteField
end WeilConjectures
