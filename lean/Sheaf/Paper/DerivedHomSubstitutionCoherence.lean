/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Substitution in derived internal Hom

Source: blueprint main-20261015, thm-sf-verdier-exchange proof Steps 2--3;
Stacks Project, Tags 0A8X, 08J7 and 08J9
(blueprint: lem-sf-derived-hom-substitution-coherence).

The auxiliary formulas assemble the recorded operations. They do not replace them
with independently supplied Hom functors or coefficient arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b a' b' d e c v r w x y x' y'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection
namespace WeilConjectures.DerivedHomSubstitution

/-- Restrict the recorded partial Hom to its finite-Tor input domain, retaining its
actual output category. Source: blueprint proof Step 2
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def hom {B : Type a} [Category.{b} B] {P : ObjectProperty B}
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (A : SixFunctorClosedDomain P Q H) : P.FullSubcategoryᵒᵖ × P.FullSubcategory ⥤ B :=
  sixFunctorDomainHom P Q H A.homPermitted A.homDomain ⋙ P.ι

/-- The actual contravariant functor J_U. Source: blueprint proof Step 2
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def functor {B : Type a} [Category.{b} B] {Y : Type d} [Category.{e} Y]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} (A : SixFunctorClosedDomain P Q H)
    (R : B ⥤ Y) (U : P.FullSubcategory) : P.FullSubcategoryᵒᵖ ⥤ Y :=
  (Functor.curry.obj (hom A)).flip.obj U ⋙ R

/-- Postcomposition by c, followed by actual direct image, as a natural isomorphism.
Source: blueprint proof Step 2 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def substitution {B : Type a} [Category.{b} B] {Y : Type d} [Category.{e} Y]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} (A : SixFunctorClosedDomain P Q H)
    (R : B ⥤ Y) {U V : P.FullSubcategory} (c : U ≅ V) :
    functor A R U ≅ functor A R V :=
  Functor.isoWhiskerRight ((Functor.curry.obj (hom A)).flip.mapIso c) R

/-- The evaluation-transpose comparison, rather than an arbitrarily supplied Hom map.
Source: Stacks 08J9 and blueprint coefficient paragraph
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def homComparison {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {P : ObjectProperty B} {P' : ObjectProperty B'}
    {Q : ObjectProperty (Bᵒᵖ × B)} {Q' : ObjectProperty (B'ᵒᵖ × B')}
    {H : Q.FullSubcategory ⥤ B} {H' : Q'.FullSubcategory ⥤ B'}
    {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
    {T : B ⥤ B'} (C : SixFunctorClosedChange A A' T) (M U : P.FullSubcategory) :
    T.obj ((hom A).obj (op M, U)) ⟶
      (hom A').obj (op ((sixFunctorDomainChange P P' T C.domain).obj M),
        (sixFunctorDomainChange P P' T C.domain).obj U) :=
  P'.ι.map (A'.closed.transpose _ _ _
    ((C.comparison.tensor.inv.app
        ((sixFunctorDomainHom P Q H A.homPermitted A.homDomain).obj (op M, U), M)) ≫
      (sixFunctorDomainChange P P' T C.domain).map (A.closed.evaluation M U)))

/-- The displayed sigma for u, using the specified ordinary-direct-image mate gamma.
Source: blueprint proof Step 3 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def sigma {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {Y : Type d} [Category.{e} Y] {Y' : Type c} [Category.{v} Y']
    {P : ObjectProperty B} {P' : ObjectProperty B'}
    {Q : ObjectProperty (Bᵒᵖ × B)} {Q' : ObjectProperty (B'ᵒᵖ × B')}
    {H : Q.FullSubcategory ⥤ B} {H' : Q'.FullSubcategory ⥤ B'}
    {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
    {T : B ⥤ B'} {TY : Y ⥤ Y'} (C : SixFunctorClosedChange A A' T)
    (R : B ⥤ Y) (R' : B' ⥤ Y') (gamma : R ⋙ TY ⟶ T ⋙ R')
    (M U : P.FullSubcategory) (U' : P'.FullSubcategory)
    (u : (sixFunctorDomainChange P P' T C.domain).obj U ≅ U') :
    TY.obj ((functor A R U).obj (op M)) ⟶
      (functor A' R' U').obj
        (op ((sixFunctorDomainChange P P' T C.domain).obj M)) :=
  gamma.app ((hom A).obj (op M, U)) ≫ R'.map
    (homComparison C M U ≫ (hom A').map (Prod.mkHom (𝟙 _) u.hom))

/-- The coefficient square, with the actual input/output categories of the stage.
This is a formula, not an extra compatibility hypothesis. Source: the displayed
coefficient equation (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def CoefficientSquare {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type a} [∀ X, Category.{b} (B X)]
    {B' : SixFunctorSpace D → Type a'} [∀ X, Category.{b'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' T)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {P : ObjectProperty (B X)} {P' : ObjectProperty (B' X)}
    {Q : ObjectProperty ((B X)ᵒᵖ × B X)} {Q' : ObjectProperty ((B' X)ᵒᵖ × B' X)}
    {H : Q.FullSubcategory ⥤ B X} {H' : Q'.FullSubcategory ⥤ B' X}
    {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
    (CC : SixFunctorClosedChange A A' (T X)) : Prop :=
  ∀ (M U V : P.FullSubcategory) (c : U ≅ V)
    (U' V' : P'.FullSubcategory)
    (u : (sixFunctorDomainChange P P' (T X) CC.domain).obj U ≅ U')
    (v : (sixFunctorDomainChange P P' (T X) CC.domain).obj V ≅ V')
    (c' : U' ≅ V'),
    ((sixFunctorDomainChange P P' (T X) CC.domain).map c.hom ≫ v.hom =
      u.hom ≫ c'.hom) →
    (T Y).map ((substitution A (S.direct f) c).hom.app (op M)) ≫
        sigma CC (S.direct f) (S'.direct f) (C.directAdjunction f).right.hom M V V' v =
      sigma CC (S.direct f) (S'.direct f) (C.directAdjunction f).right.hom M U U' u ≫
        (substitution A' (S'.direct f) c').hom.app
          (op ((sixFunctorDomainChange P P' (T X) CC.domain).obj M))


/-- Source-shift components, allowing an explicitly identified shifted source N.
Using N and e avoids requiring a second choice of shift on a full subcategory.
Source: the signed-shift paragraph
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftFamily {B : Type a} [Category.{b} B] [HasShift B ℤ]
    {Y : Type d} [Category.{e} Y] [HasShift Y ℤ]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} (A : SixFunctorClosedDomain P Q H) (R : B ⥤ Y) :=
  ∀ (M N U : P.FullSubcategory) (r : ℤ), (N.obj ≅ M.obj⟦r⟧) →
    ((functor A R U).obj (op N) ≅ ((functor A R U).obj (op M))⟦-r⟧)

/-- The displayed signed source-shift square. Source: blueprint proof Step 3
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftSquare {B : Type a} [Category.{b} B] [HasShift B ℤ]
    {Y : Type d} [Category.{e} Y] [HasShift Y ℤ]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} {A : SixFunctorClosedDomain P Q H} {R : B ⥤ Y}
    (s : ShiftFamily A R) : Prop :=
  ∀ (M N U V : P.FullSubcategory) (c : U ≅ V) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧),
    (substitution A R c).hom.app (op N) ≫ (s M N V r e).hom =
      (s M N U r e).hom ≫ ((substitution A R c).hom.app (op M))⟦-r⟧'

/-- Realize J in the actual ambient ringed-site derived category.
Source: the ambient-realization convention
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def realization {B : Type a} [Category.{b} B] {Y : Type d} [Category.{e} Y]
    {AX : Type x} [Category.{y} AX] {AY : Type x'} [Category.{y'} AY]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} {A : SixFunctorClosedDomain P Q H}
    (R : B ⥤ Y) (FX : B ⥤ AX) (FY : Y ⥤ AY) (R0 : AX ⥤ AY)
    {HA : AXᵒᵖ × AX ⥤ AX}
    (h : ∀ M U : P.FullSubcategory,
      FX.obj ((hom A).obj (op M, U)) ≅ HA.obj (op (FX.obj M.obj), FX.obj U.obj))
    (d : R ⋙ FY ≅ FX ⋙ R0) (M U : P.FullSubcategory) :
    FY.obj ((functor A R U).obj (op M)) ≅
      R0.obj (HA.obj (op (FX.obj M.obj), FX.obj U.obj)) :=
  d.app ((hom A).obj (op M, U)) ≪≫ R0.mapIso (h M U)

/-- The canonical signed comparison: realize, use the fixed signed Hom shift and
ordinary right-derived direct-image shift, and lift through the full inclusion.
Source: Stacks 0A8X, 08JA; blueprint signed-shift paragraph
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def realizedShift {B : Type a} [Category.{b} B] [HasShift B ℤ]
    {Y : Type d} [Category.{e} Y] [HasShift Y ℤ]
    {AX : Type x} [Category.{y} AX] [HasShift AX ℤ]
    {AY : Type x'} [Category.{y'} AY] [HasShift AY ℤ]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} {A : SixFunctorClosedDomain P Q H}
    (R : B ⥤ Y) (FX : B ⥤ AX) (FY : Y ⥤ AY) (R0 : AX ⥤ AY)
    [FX.CommShift ℤ] [FY.CommShift ℤ] [R0.CommShift ℤ] [FY.Full] [FY.Faithful]
    {HA : AXᵒᵖ × AX ⥤ AX}
    (h : ∀ M U : P.FullSubcategory,
      FX.obj ((hom A).obj (op M, U)) ≅ HA.obj (op (FX.obj M.obj), FX.obj U.obj))
    (d : R ⋙ FY ≅ FX ⋙ R0)
    (t : ∀ (M : AX) (r : ℤ),
      (Prod.sectR (op M) AX ⋙ HA) ⋙ shiftFunctor AX (-r) ≅
        Prod.sectR (op (M⟦r⟧)) AX ⋙ HA) : ShiftFamily A R :=
  fun M N U r e ↦ FY.preimageIso
    (realization R FX FY R0 h d N U ≪≫
      R0.mapIso (HA.mapIso
        (((FX.mapIso e ≪≫ (FX.commShiftIso r).app M.obj).symm.op).prod
          (Iso.refl (FX.obj U.obj)))) ≪≫
      R0.mapIso ((t (FX.obj M.obj) r).symm.app (FX.obj U.obj)) ≪≫
      (R0.commShiftIso (-r)).app (HA.obj (op (FX.obj M.obj), FX.obj U.obj)) ≪≫
      (shiftFunctor AY (-r)).mapIso (realization R FX FY R0 h d M U).symm ≪≫
      ((FY.commShiftIso (-r)).app ((functor A R U).obj (op M))).symm)

/-- Identity-target version of sigma. Source: the coefficient paragraph
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def baseSigma {B : Type a} [Category.{b} B] {B' : Type a'} [Category.{b'} B']
    {Y : Type d} [Category.{e} Y] {Y' : Type c} [Category.{v} Y']
    {P : ObjectProperty B} {P' : ObjectProperty B'}
    {Q : ObjectProperty (Bᵒᵖ × B)} {Q' : ObjectProperty (B'ᵒᵖ × B')}
    {H : Q.FullSubcategory ⥤ B} {H' : Q'.FullSubcategory ⥤ B'}
    {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
    {T : B ⥤ B'} {TY : Y ⥤ Y'} (C : SixFunctorClosedChange A A' T)
    (R : B ⥤ Y) (R' : B' ⥤ Y') (gamma : R ⋙ TY ⟶ T ⋙ R')
    (M U : P.FullSubcategory) :=
  sigma C R R' gamma M U ((sixFunctorDomainChange P P' T C.domain).obj U) (Iso.refl _)

/-- Descent normalization of a field-stage source shift. It is precisely the
coefficient image of the already fixed integral or finite-stage shift, conjugated
by the specified sigma and by coefficient shift commutation.
Source: rationalization/common-stage conventions
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftTransport {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type a} [catB : ∀ X, Category.{b} (B X)]
    [shiftB : ∀ X, HasShift (B X) ℤ]
    {B' : SixFunctorSpace D → Type a'} [catB' : ∀ X, Category.{b'} (B' X)]
    [shiftB' : ∀ X, HasShift (B' X) ℤ]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B' X} [commT : ∀ X, (T X).CommShift ℤ]
    (C : SixFunctorCoefficientComparison S S' T)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {P : ObjectProperty (B X)} {P' : ObjectProperty (B' X)}
    {Q : ObjectProperty ((B X)ᵒᵖ × B X)} {Q' : ObjectProperty ((B' X)ᵒᵖ × B' X)}
    {H : Q.FullSubcategory ⥤ B X} {H' : Q'.FullSubcategory ⥤ B' X}
    {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
    (CC : SixFunctorClosedChange A A' (T X))
    (s : ShiftFamily A (S.direct f)) (s' : ShiftFamily A' (S'.direct f)) : Prop :=
  ∀ (M N U : P.FullSubcategory) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧),
    (T Y).map (s M N U r e).hom ≫
        ((T Y).commShiftIso (-r)).hom.app ((functor A (S.direct f) U).obj (op M)) ≫
        (baseSigma CC (S.direct f) (S'.direct f)
          (C.directAdjunction f).right.hom M U)⟦-r⟧' =
      baseSigma CC (S.direct f) (S'.direct f)
          (C.directAdjunction f).right.hom N U ≫
        (s' ((sixFunctorDomainChange P P' (T X) CC.domain).obj M)
          ((sixFunctorDomainChange P P' (T X) CC.domain).obj N)
          ((sixFunctorDomainChange P P' (T X) CC.domain).obj U) r
          ((T X).mapIso e ≪≫ ((T X).commShiftIso r).app M.obj)).hom


/-- Naturality in both Hom variables fixes transport to any identified shifted source,
including rational arrows with denominators and common-stage arrows.
Source: naturality of the signed comparison in proof Step 3
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def ShiftNaturality {B : Type a} [Category.{b} B] [HasShift B ℤ]
    {Y : Type d} [Category.{e} Y] [HasShift Y ℤ]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} {A : SixFunctorClosedDomain P Q H} {R : B ⥤ Y}
    (s : ShiftFamily A R) : Prop :=
  (∀ (M N U V : P.FullSubcategory) (c : U ⟶ V) (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧),
    R.map ((hom A).map (Prod.mkHom (𝟙 (op N)) c)) ≫ (s M N V r e).hom =
      (s M N U r e).hom ≫ (R.map ((hom A).map (Prod.mkHom (𝟙 (op M)) c)))⟦-r⟧') ∧
  (∀ (M N M' N' U : P.FullSubcategory) (a : M ⟶ M') (b : N ⟶ N')
    (r : ℤ) (e : N.obj ≅ M.obj⟦r⟧) (e' : N'.obj ≅ M'.obj⟦r⟧),
    (P.ι.map b ≫ e'.hom = e.hom ≫ (P.ι.map a)⟦r⟧') →
    (functor A R U).map b.op ≫ (s M N U r e).hom =
      (s M' N' U r e').hom ≫ ((functor A R U).map a.op)⟦-r⟧')

/-- The formal coefficient square for any allowed comparison with the displayed
closed-model and adjunction interfaces. In particular this also applies to an
allowed realization comparison; h is still the evaluation transpose.
Source: blueprint proof Step 3; Stacks 08J9
(blueprint: lem-sf-derived-hom-substitution-coherence).

Proof: uncurry h_(M,V) T(H(1,c)) and H'(1,Tc) h_(M,U). Naturality of the tensor
comparison and evaluation makes both equal T(c) T(ev) mu. Transposition is
injective, so the two Hom maps agree. Postcompose by H'(1,v), use T(c) v = u c',
and apply R'. Naturality of the specified direct-image mate gamma pastes this
with the direct-image square, giving sigma_V T(j_c) = j_c' sigma_U.
Neither h nor sigma is inverted in this calculation. For completed coefficients
this is an equation in the completed category itself. Rationalization and
common-stage images preserve the calculation, canceling adjacent endpoint maps. -/
theorem coefficient_square {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type a} [∀ X, Category.{b} (B X)]
    {B' : SixFunctorSpace D → Type a'} [∀ X, Category.{b'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {T : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' T)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    {P : ObjectProperty (B X)} {P' : ObjectProperty (B' X)}
    {Q : ObjectProperty ((B X)ᵒᵖ × B X)} {Q' : ObjectProperty ((B' X)ᵒᵖ × B' X)}
    {H : Q.FullSubcategory ⥤ B X} {H' : Q'.FullSubcategory ⥤ B' X}
    {A : SixFunctorClosedDomain P Q H} {A' : SixFunctorClosedDomain P' Q' H'}
    (CC : SixFunctorClosedChange A A' (T X)) : CoefficientSquare C f CC := by
  sorry

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The finite-level signed comparison, lifted from the fixed ordinary ringed-site
normalization. Source: finite case of the signed-shift paragraph
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def finiteShift (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    ShiftFamily (S.finiteClosed X) (S.finite.direct f) :=
  realizedShift (S.finite.direct f)
    (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
    (proEtaleConstantDerivedDirectImage f.hom.left (Padic.coefficientExtensionRing C.l E n))
    (fun M U ↦ (S.finiteModelComparison X).comparison.hom.app (op M, U))
    (S.finiteDirectImage f)
    (CategoryTheory.RingedHomUniverses.sourceShift (ProEt.topology X.obj.left)
      ((constantSheaf (ProEt.topology X.obj.left) CommRingCat.{u+1}).obj
        (.of (ULift.{u+1, u} (Padic.coefficientExtensionRing C.l E n)))))

/-- The completed integral signed comparison for any recorded integral closed model.
The direct image is realized by the actual completed right-derived functor.
Source: integral case of the signed-shift paragraph
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def integralShift (S : SixFunctorHigherOperations D C E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (A : SixFunctorClosedDomain
      (fun K : sfIntegralConstructibleCategory C.l E X.obj.left ↦
        finiteTorConstructibleIntegral C.l E X.obj.left K.obj)
      (constructibleIntegralHomPairs C.l E X.obj.left)
      (constructibleIntegralHom C.l E X.obj.left))
    (N : sixFunctorRingedModel.{u, u+1, u} (ProEt.topology X.obj.left)
      (completedIntegralCommRingSheafUnrestricted C.l E X.obj.left))
    (a : SixFunctorAmbientClosedModel A N.closed N.symmetric
      (sfIntegralConstructible C.l E X.obj.left).ι) :
    ShiftFamily A (S.integral.direct f) :=
  realizedShift (S.integral.direct f)
    (sfIntegralConstructible C.l E X.obj.left).ι
    (sfIntegralConstructible C.l E Y.obj.left).ι
    (sfCompletedDerivedDirectImage C.l E f.hom.left)
    (fun M U ↦ a.comparison.hom.app (op M, U)) (S.integralDirectImage f)
    (CategoryTheory.RingedHomUniverses.sourceShift (ProEt.topology X.obj.left)
      (completedIntegralCommRingSheafUnrestricted C.l E X.obj.left))

/-- The original datum's completed comparison. Source: integral signed-shift clause
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def completedShift (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    ShiftFamily (S.integralClosed X) (S.higher.integral.direct f) :=
  integralShift S.higher f (S.integralClosed X) (S.integralModel X)
    (S.integralModelComparison X)

/-- The same completed comparison at a finite subfield of the fixed algebraic closure.
Source: common finite-stage convention
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def stageCompletedShift (S : SixFunctorDatum D C E n hn)
    (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    ShiftFamily (S.coefficientClosedModels E₀ X).integral
      ((S.closure.coefficientStages E₀).integral.direct f) :=
  integralShift (S.closure.coefficientStages E₀) f
    (S.coefficientClosedModels E₀ X).integral (S.coefficientClosedModels E₀ X).model
    (S.coefficientClosedModels E₀ X).realization

/-- The field comparisons to be descended, including every common finite stage.
These fields are isomorphisms; their normalization, not an arbitrary choice,
is imposed by FieldNormalization below. Source: field-stage convention
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
structure FieldShifts (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) where
  rational : ShiftFamily (S.rationalClosed X) (S.higher.rational.direct f)
  stage : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    ShiftFamily (S.coefficientClosedModels E₀ X).rational
      ((S.closure.coefficientStages E₀).rational.direct f)
  closure : ShiftFamily (S.commonClosed X) (S.closure.commonStage.direct f)

/-- Field comparisons are exactly the rationalized and common-stage images of the
fixed completed comparisons, with canonical endpoint comparisons inserted.
Source: final paragraph and proof Step 7
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def FieldNormalization (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (s : FieldShifts S f) : Prop :=
  ShiftTransport S.higher.rationalization f (S.rationalClosedComparison X)
    (completedShift S f) s.rational ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    ShiftTransport (D := D)
      (catB := fun _ ↦ inferInstance) (catB' := fun _ ↦ inferInstance)
      (shiftB := fun _ ↦ inferInstance) (shiftB' := fun _ ↦ inferInstance)
      (B := fun X ↦ sfIntegralConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (B' := fun X ↦ sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (T := fun Z ↦ sfRationalConstructibleLocalization C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
      (commT := fun Z ↦ sfRationalLocalizationCommShift C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Z.obj.left)
      (S.closure.coefficientStages E₀).rationalization f
      (S.coefficientClosedModels E₀ X).rationalization (stageCompletedShift S E₀ f)
      (s.stage E₀)) ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    ShiftTransport (D := D)
      (catB := fun _ ↦ inferInstance) (catB' := fun _ ↦ inferInstance)
      (shiftB := fun _ ↦ inferInstance) (shiftB' := fun _ ↦ inferInstance)
      (B := fun X ↦ sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (B' := fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (T := fun Z ↦ GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀)
      (commT := fun Z ↦
        GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := C.l) (Ω := C.Qbar) (Y := Z.obj.left) E₀)
      (S.closure.commonStageComparison E₀) f
      (S.commonClosedComparison E₀ X) (s.stage E₀) s.closure) ∧
  ShiftNaturality s.rational ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar, ShiftNaturality (s.stage E₀)) ∧
  ShiftNaturality s.closure

/-- The allowed A5 squares on the actual operations: completed reduction,
rationalization, scalar extension, and passage to the algebraic closure. Each h
is formed by evaluation-transposition; each gamma is the specified adjunction
comparison, hence the pullback mate. Source: the coefficient clause and proof
Steps 4--7 (blueprint: lem-sf-derived-hom-substitution-coherence). -/
def CoefficientCoherence (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) : Prop :=
  CoefficientSquare S.higher.rationalization f (S.rationalClosedComparison X) ∧
  (∀ m : ℕ, CoefficientSquare (S.integralNormalization.reduction m) f
    (S.reductionClosedComparison m X)) ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    CoefficientSquare
      (B := fun X ↦ sfIntegralConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (B' := fun X ↦ sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (S.closure.coefficientStages E₀).rationalization f
      (S.coefficientClosedModels E₀ X).rationalization) ∧
  (∀ (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L),
    CoefficientSquare
      (B := fun X ↦ sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (B' := fun X ↦ sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left)
      (S.closure.coefficientTransition h) f (S.coefficientClosedComparison E₀ L h X)) ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    CoefficientSquare
      (B := fun X ↦ sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left)
      (B' := fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (S.closure.commonStageComparison E₀) f (S.commonClosedComparison E₀ X))

/-- Derived internal-Hom substitution, with the signed shifts and specified A5 maps.

Source: blueprint main-20261015, thm-sf-verdier-exchange proof Steps 2--3;
Stacks 0A8X, 08J7, 08J9
(blueprint: lem-sf-derived-hom-substitution-coherence).

Proof:
1. The recorded Hom and direct image are functors. Their restriction to finite-Tor
inputs gives J. Postcomposition with c and c inverse gives the natural isomorphism
`substitution`; its components are exactly R(H(1,c)).
2. On complexes reindex a degree-d Hom family with multiplier (-1)^(r*d).
The ratio of consecutive signs is (-1)^r, so this is a chain isomorphism for
both positive and negative r. Postcomposition commutes with reindexing and the
scalar. The normalized source shift of the ringed-site Hom is its localization
(lem-weil-pbc-ringed-internal-hom-exact-restriction and
lem-pur-derived-internal-hom-shift-left). Compose its inverse with the natural
ordinary direct-image shift comparison. This proves the finite and completed
squares for the stipulated comparisons, including their ambient realizations.
3. The recorded integral residue-Tor equality (lem-coef-integral-residue-tor)
identifies integral constructibility and integral finite-Tor constructibility.
Thus the normalization covers all underlying objects of each rational stage.
Rationalize these natural comparisons in the recorded raw scalar localization.
Its underlying objects are unchanged; its arrows are localized integral arrows.
Naturality determines the comparisons on all such arrows. At the algebraic closure
represent the finite collection of objects and arrows at a common finite field.
Adjacent endpoint comparisons cancel in composition. These constructions give
FieldNormalization and determine the field families uniquely; they retain
naturality in arbitrary source identifications and in both Hom variables.
4. Uncurry h_(M,V) T(H(1,c)) and H'(1,Tc) h_(M,U), using the recorded closed
adjunction (lem-sf-ringed-derived-closed-symmetric-monoidal and
def-coef-ringed-tensor-hom-model). Naturality of the tensor comparison and
H evaluation identifies both uncurries with T(c) T(ev_(M,U)) mu. Injectivity of
transposition proves equality, without assuming an ambient h invertible.
5. Postcompose by H'(1,v). The equation T(c) v = u c' identifies this with
H'(1,c') H'(1,u) h_(M,U).
6. Apply naturality of the specified direct-image mate gamma to H(1,c), then
apply R' to Step 5 and reassociate. This is exactly CoefficientSquare.
7. At integral coefficients all equations hold in the actual completed category;
no equality is inferred just from finite reductions. Rationalization preserves
the equations. Common-stage composition cancels endpoint comparisons, giving
the field equations. Only the A5 comparison domains have been used. -/
theorem coherence (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    ShiftSquare (finiteShift S f) ∧ ShiftSquare (completedShift S f) ∧
      (∃! s : FieldShifts S f, FieldNormalization S f s ∧
        ShiftSquare s.rational ∧
        (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar, ShiftSquare (s.stage E₀)) ∧
        ShiftSquare s.closure) ∧ CoefficientCoherence S f := by
  sorry

/-- The specified field comparisons, selected from their uniquely normalized
construction. The existence theorem determines the entire family, not merely
its isomorphism class. Source: field-stage signed-shift convention
(blueprint: lem-sf-derived-hom-substitution-coherence). -/
def fieldShifts (S : SixFunctorDatum D C E n hn)
    {X Y : SixFunctorSpace D} [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] : FieldShifts S f :=
  (coherence S f).2.2.1.exists.choose

end WeilConjectures.DerivedHomSubstitution
