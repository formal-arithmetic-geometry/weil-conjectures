/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Composition comparison for the standing exceptional inverse images

Source: main-20261015 blueprint, sec-smooth-purity/sk-prop-sp-composition,
pur9-def-upper-shriek-composition.md (blueprint: pur9-def-upper-shriek-composition).
The comparison is the transpose of the canonical compact-support compositor followed
by the standing counit. The relative adjunctions use the canonical comparison;
no right adjoint on the ambient pro-etale category is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The standing Hom bijection, written using the named canonical compact-support
comparison of thm-sf-ambient-adjoint-class. A retained etale-origin representative is
used only to compute the uniquely determined transpose: conjugate by its isomorphism,
apply the fixed compact-support comparison, the comparison adjunction, the ordinary
etale adjunction, and fully faithful comparison pullback, in that order.
Source: blueprint thm-sf-ambient-adjoint-class, clause (2), as used in the definition
of c_{g,f,L} (blueprint: pur9-def-upper-shriek-composition). -/
def standingExceptionalHomEquiv (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K ⟶ L) ≃
      (K ⟶ (rightDerivedUpperShriek Λ f).obj L) :=
  let A := ModuleCat.{u + 1} Λ
  let K' := Classical.choose hK
  let hK' := (Classical.choose_spec hK).1
  let e := Classical.choice (Classical.choose_spec hK).2
  let νX := (comparisonUpperStar A X).mapDerivedCategory
  let RνY := (comparisonLowerStar A Y).rightDerivedFunctor
  let M := (Etale.rightDerivedUpperShriek Λ f).obj (RνY.obj L)
  let pullback : (K' ⟶ M) ≃ (νX.obj K' ⟶ νX.obj M) :=
    Equiv.ofBijective (fun a ↦ νX.map a)
      (bijective_comparisonUpperStar_mapDerivedCategory_map K' M
        (plus_etaleRightDerivedUpperShriek_obj f hL))
  let changeSource := ((rightDerivedLowerShriek A f).mapIso e).symm.homFromEquiv
  let compare := ((fixedCompactSupportComparisonIso Λ
    (HasCompactification.compactification f)).app ⟨K', hK'⟩).homFromEquiv
  changeSource.trans (compare.trans (((derivedComparisonAdjunction A Y).homEquiv _ L).trans
    (((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv K' (RνY.obj L)).trans
      (pullback.trans e.homFromEquiv))))

/-- Successive standing Hom transpose through g and then f.
Source: definition of c in the composition section
(blueprint: pur9-def-upper-shriek-composition). -/
def standingCompositeHomTranspose (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [CompactSpace Y] [CompactSpace Z]
    {M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X M)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.plus K)
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj M) ⟶ K) :
    M ⟶ (rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj K) :=
  ((standingExceptionalHomEquiv Λ g (hM.rightDerivedLowerShriek_obj f) hK).trans
    (standingExceptionalHomEquiv Λ f hM (plus_rightDerivedUpperShriek_obj g hK))) a

/-- Extend an isomorphism component by zero outside its full object domain.
Source: the domain conventions for the composition mate
(blueprint: pur9-def-upper-shriek-composition). -/
def standingExtendIsoComponent {C E : Type*} [Category C] [Category E] [HasZeroMorphisms E]
    (P : ObjectProperty C) (F G : C ⥤ E) (α : P.ι ⋙ F ≅ P.ι ⋙ G)
    (M : C) : F.obj M ⟶ G.obj M :=
  open Classical in
  if hM : P M then α.hom.app ⟨M, hM⟩ else 0

/-- The standing counit, extended by zero off the bounded-below domain.
Source: inverse standing Hom image of the identity
(blueprint: pur9-def-upper-shriek-composition). -/
def standingExceptionalCounit (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      ((rightDerivedUpperShriek Λ f).obj K) ⟶ K :=
  open Classical in
  if hK : _root_.DerivedCategory.TStructure.t.plus K then
    (standingExceptionalHomEquiv Λ f
      (plusEtaleOrigin_rightDerivedUpperShriek_obj f hK) hK).symm (𝟙 _)
  else 0

/-- The specified compact-support compositor, with explicit zero extension.
Source: canonical origin composition
(blueprint: pur9-def-upper-shriek-composition). -/
def standingCompactSupportCompositor (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj M) ⟶
        (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g)).obj M :=
  standingExtendIsoComponent
    (C := _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (E := _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (f ≫ g))
    (originCompositionAmbient Λ f g) M

/-- The standing exceptional composition mate, extended by zero off its domain.
Source: successive transpose of compositor followed by the counit
(blueprint: pur9-def-upper-shriek-composition). -/
def standingExceptionalCompositionAmbient (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))) :
    (rightDerivedUpperShriek Λ (f ≫ g)).obj K ⟶
      (rightDerivedUpperShriek Λ f).obj ((rightDerivedUpperShriek Λ g).obj K) :=
  open Classical in
  if hK : _root_.DerivedCategory.TStructure.t.plus K then
    standingCompositeHomTranspose Λ f g
      (plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hK) hK
      (standingCompactSupportCompositor Λ f g ((rightDerivedUpperShriek Λ (f ≫ g)).obj K) ≫
        standingExceptionalCounit Λ (f ≫ g) K)
  else 0

/-- The morphism c_{g,f,L} for the finite-level standing choices. The counit for gf
is its standing Hom bijection applied inversely to the identity. Apply alpha at
K=(gf)^!L, compose with that counit, transpose first through g and then through f.
This order is exactly Adjunction.comp_homEquiv for def-weil-pbc-composite-adjunction.
The output is a morphism (gf)^!L to f^!g^!L in the ambient small pro-etale derived
category, written in rightDerivedUpperShriek form (isomorphic to the recorded
sfFiniteExceptionalAt functor values at the chosen compactifications, both being right
adjoints of the etale compact-support pushforward).
Source: main-20261015 blueprint, sk-prop-sp-composition, definition of c_{g,f,L}
(blueprint: pur9-def-upper-shriek-composition). -/
def standingExceptionalComposition (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of P.field.k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
    (S ↘ Spec (.of P.field.k))
  fun (L : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} P.Coefficient) S) ↦
    standingExceptionalCompositionAmbient P.Coefficient f g L.obj

end AlgebraicGeometry.ProEtale
