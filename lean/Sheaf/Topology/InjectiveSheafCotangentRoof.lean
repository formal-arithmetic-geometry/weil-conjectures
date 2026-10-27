/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Topology.StandardSheafCotangentFlatModel
public import Sheaf.RingTheory.InjectiveStandardResolutionQuotients
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.SiteModuleSliceSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.CategoryTheory.Sites.SheafifiedDifferentialsCokernel

/-!
# The injective sheaf cotangent sequence and its canonical roof

Source: Stacks Project, cotangent.tex, Tags 08SD, 08SE and 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof).

The quotient algebras are pushouts, hence degreewise sheaf tensor products.
Presentations below retain the sectionwise quotient resolutions and every
universal differential. No complementary variables enter any construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial
open Algebra.CotangentResolution

namespace TopCat.SheafCotangent

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- Canonical ring sheafification on the essentially small open site.
Source: Stacks 00W1 (blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
instance injectiveRingSheafify (T : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology T) CommRingCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u, u + 1, u}
    (Opens.grothendieckTopology T) CommRingCat.{u}

/-- Colimits of ring sheaves, via their site presentation. Source: Stacks 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
instance injectiveRingSheafPushouts (T : TopCat.{u}) :
    HasColimitsOfShape WalkingSpan (T.Sheaf CommRingCat.{u}) :=
  inferInstanceAs (HasColimitsOfShape WalkingSpan
    (CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}))

/-- The standard square from `B/A` to `C/A`. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveTargetSquare {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) : Arrow.mk f ⟶ Arrow.mk (f ≫ j) :=
  Arrow.homMk' (𝟙 A) j (Category.id_comp (f ≫ j))

/-- The standard square changing the base from `A` to `B`. Source: Stacks 08SE
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveBaseSquare {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) : Arrow.mk (f ≫ j) ⟶ Arrow.mk j :=
  Arrow.homMk' f (𝟙 E) ((Category.comp_id (f ≫ j)).trans rfl)

/-- The canonical standard polynomial arrow. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectivePolynomialMap (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) :=
  (F.functoriality.polynomial (v := 𝟙 T)
    (f := Arrow.mk f) (g := Arrow.mk (f ≫ j)) (injectiveTargetSquare f j)).map

/-- The actual simplicial sheaf tensor product `Q ⊗_P B`.
Functor-category pushouts are computed degreewise. Source: Stacks 08SD, 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveQuotient (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) : SimplicialObject (T.Sheaf CommRingCat.{u}) :=
  pushout (injectivePolynomialMap C S F f j)
    (S.sheaves T (Arrow.mk f)).standard.augmentation

/-- The universal arrow from `Q` to its tensor quotient. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveQuotientLeft (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) :=
  pushout.inl (injectivePolynomialMap C S F f j)
    (S.sheaves T (Arrow.mk f)).standard.augmentation

/-- The universal base-ring arrow into the quotient. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveQuotientRight (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) :=
  pushout.inr (injectivePolynomialMap C S F f j)
    (S.sheaves T (Arrow.mk f)).standard.augmentation

/-- The sectionwise square using precisely the chosen section arrows.
Source: Stacks 08SD (blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveSectionSquare {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) (V : (Opens T)ᵒᵖ) :
    sectionArrow (Arrow.mk f) V ⟶ sectionArrow (Arrow.mk (f ≫ j)) V :=
  Arrow.homMk' (𝟙 (A.obj.obj V)) (j.hom.app V) (Category.id_comp _)

/-- The sectionwise tensor quotient, before sheafification. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveSectionQuotient (C : Coherence.{u}) {T : TopCat.{u}}
    {A B E : T.Sheaf CommRingCat.{u}} (f : A ⟶ B) (j : B ⟶ E)
    (V : (Opens T)ᵒᵖ) : Augmentation (sectionArrow (Arrow.mk j) V) :=
  quotientAugmentation (f.hom.app V) (j.hom.app V)
    (C.standard (sectionArrow (Arrow.mk f) V))
    (C.standard (sectionArrow (Arrow.mk (f ≫ j)) V))
    (C.standardMap (f := Arrow.mk (f.hom.app V))
      (g := Arrow.mk (f.hom.app V ≫ j.hom.app V)) (injectiveSectionSquare f j V))

/-- The sectionwise universal quotient arrow. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveSectionLeft (C : Coherence.{u}) {T : TopCat.{u}}
    {A B E : T.Sheaf CommRingCat.{u}} (f : A ⟶ B) (j : B ⟶ E)
    (V : (Opens T)ᵒᵖ) :
    (C.standard (sectionArrow (Arrow.mk (f ≫ j)) V)).algebra ⟶
      (injectiveSectionQuotient C f j V).algebra :=
  pushout.inl
    (C.standardMap (f := Arrow.mk (f.hom.app V))
      (g := Arrow.mk (f.hom.app V ≫ j.hom.app V)) (injectiveSectionSquare f j V)).map
    (C.standard (sectionArrow (Arrow.mk f) V)).augmentation

/-- A pure quotient tensor, in sectionwise standard coordinates. Source: Stacks 08SD
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveQuotientTensor (C : Coherence.{u}) {T : TopCat.{u}}
    {A B E : T.Sheaf CommRingCat.{u}} (f : A ⟶ B) (j : B ⟶ E)
    (V : (Opens T)ᵒᵖ) (n : ℕ) (p : standardTerm (sectionArrow (Arrow.mk (f ≫ j)) V) n)
    (b : B.obj.obj V) : (injectiveSectionQuotient C f j V).algebra.obj (op ⦋n⦌) :=
  ((injectiveSectionLeft C f j V).app (op ⦋n⦌)
    (eqToHom ((C.standard_spec (sectionArrow (Arrow.mk (f ≫ j)) V)).1 n).symm p)) *
      (injectiveSectionQuotient C f j V).base.app (op ⦋n⦌) b

/-- The sheaf quotient with its augmentation and its sheafified sectionwise tensor
presentation. The coordinate restriction formula fixes the presheaf maps, and the
unit formula fixes the sheafification isomorphism. Source: Stacks 08SD, 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
structure InjectiveQuotientModel (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) where
  augmentation : injectiveQuotient C S F f j ⟶ (SimplicialObject.const _).obj E
  augmentation_left :
    injectiveQuotientLeft C S F f j ≫ augmentation =
      (S.sheaves T (Arrow.mk (f ≫ j))).standard.augmentation
  augmentation_right : injectiveQuotientRight C S F f j ≫ augmentation =
    (SimplicialObject.const _).map j
  presheaf : ℕ → T.Presheaf CommRingCat.{u}
  coordinate : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ),
    (presheaf n).obj V ≅ (injectiveSectionQuotient C f j V).algebra.obj (op ⦋n⦌)
  restriction : ∀ (n : ℕ) {V W : (Opens T)ᵒᵖ} (r : V ⟶ W)
    (p : standardTerm (sectionArrow (Arrow.mk (f ≫ j)) V) n) (b : B.obj.obj V),
    (coordinate n W).hom ((presheaf n).map r
      ((coordinate n V).inv (injectiveQuotientTensor C f j V n p b))) =
        injectiveQuotientTensor C f j W n
          (standardSquareMap (restrictionSquare (Arrow.mk (f ≫ j)) r) n p) (B.obj.map r b)
  sheafification : ∀ n : ℕ,
    (presheafToSheaf (Opens.grothendieckTopology T) CommRingCat).obj (presheaf n) ≅
      (injectiveQuotient C S F f j).obj (op ⦋n⦌)
  tensor_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ)
    (p : standardTerm (sectionArrow (Arrow.mk (f ≫ j)) V) n) (b : B.obj.obj V),
    (sheafification n).hom.hom.app V
      ((toSheafify (Opens.grothendieckTopology T) (presheaf n)).app V
        ((coordinate n V).inv (injectiveQuotientTensor C f j V n p b))) =
      ((injectiveQuotientLeft C S F f j).app (op ⦋n⦌)).hom.app V
        (polynomialSection ((S.sheaves T (Arrow.mk (f ≫ j))).standard.polynomial n)
          ((S.sheaves T (Arrow.mk (f ≫ j))).standard.algebraIso n) V p) *
            ((injectiveQuotientRight C S F f j).app (op ⦋n⦌)).hom.app V b
  polynomial_resolution : ∀ V : (Opens T)ᵒᵖ,
    IsPolynomialResolution (injectiveSectionQuotient C f j V)

/-- The actual alternating additive augmentation of the sheaf quotient.
Source: Stacks 08SZ (blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def injectiveQuotientAugmentation {C : Coherence.{u}} {S : Comparison C}
    {F : FlatFunctorialModel C S} {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    {f : A ⟶ B} {j : B ⟶ E} (M : InjectiveQuotientModel C S F f j) :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (⟨injectiveQuotient C S F f j ⋙
          sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat),
        (sheafCompose (Opens.grothendieckTopology T)
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj E,
        Functor.whiskerRight M.augmentation
          (sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))⟩))
    ComplexShape.embeddingDownNat

/-- A differential simplicial module on an augmented sheaf algebra. Its terms are
actual relative differential tensors, and every operator is normalized on `c ⊗ dx`.
Source: Stacks 08SE, 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
structure QuotientDifferentials {T : TopCat.{u}} (B E : T.Sheaf CommRingCat.{u})
    (L : SimplicialObject (T.Sheaf CommRingCat.{u}))
    (b : (SimplicialObject.const _).obj B ⟶ L)
    (e : L ⟶ (SimplicialObject.const _).obj E) where
  module : SimplicialObject (ringedSiteModules.{u} (CategoryTheory.SheafDifferentials.ring E))
  termIso : ∀ n : ℕ, module.obj (op ⦋n⦌) ≅
    differentialSheaf (b.app (op ⦋n⦌)) (e.app (op ⦋n⦌))
  operator : ∀ (m n : ℕ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (V : (Opens T)ᵒᵖ)
    (c : E.obj.obj V) (x : (L.obj (op ⦋n⦌)).obj.obj V),
    ((module.map θ.op) ≫ (termIso m).hom).val.app V
      ((termIso n).inv.val.app V
        (differentialSection (b.app (op ⦋n⦌)) (e.app (op ⦋n⦌)) V c x)) =
      differentialSection (b.app (op ⦋m⦌)) (e.app (op ⦋m⦌)) V c
        ((L.map θ.op).hom.app V x)

/-- The quotient differential complex in nonpositive cohomological degrees.
Source: Stacks 08SE, 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def quotientDifferentialComplex {T : TopCat.{u}} {B E : T.Sheaf CommRingCat.{u}}
    {L : SimplicialObject (T.Sheaf CommRingCat.{u})}
    {b : (SimplicialObject.const _).obj B ⟶ L}
    {e : L ⟶ (SimplicialObject.const _).obj E} (M : QuotientDifferentials B E L b e) :=
  (negativeComplex _).obj M.module

/-- The local generator of a quotient differential complex. Source: Stacks 08SE
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def quotientDifferentialGenerator {T : TopCat.{u}} {B E : T.Sheaf CommRingCat.{u}}
    {L : SimplicialObject (T.Sheaf CommRingCat.{u})}
    {b : (SimplicialObject.const _).obj B ⟶ L}
    {e : L ⟶ (SimplicialObject.const _).obj E} (M : QuotientDifferentials B E L b e)
    (n : ℕ) (V : (Opens T)ᵒᵖ) (c : E.obj.obj V) (x : (L.obj (op ⦋n⦌)).obj.obj V) :
    ((quotientDifferentialComplex M).X (-(n : ℤ))).val.obj V :=
  ((((AlgebraicTopology.alternatingFaceMapComplex _).obj M.module).extendXIso
    ComplexShape.embeddingDownNat (i := n) rfl).inv.val.app V)
      ((M.termIso n).inv.val.app V
        (differentialSection (b.app (op ⦋n⦌)) (e.app (op ⦋n⦌)) V c x))

/-- A standard complex generator allowing any local polynomial section.
Source: Stacks 08SS (blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def standardSheafGenerator (C : Coherence.{u}) (S : Comparison C)
    {T : TopCat.{u}} (f : Arrow (T.Sheaf CommRingCat.{u})) (n : ℕ)
    (V : (Opens T)ᵒᵖ) (c : f.right.obj.obj V)
    (x : ((S.sheaves T f).standard.algebra.obj (op ⦋n⦌)).obj.obj V) :
    ((standardSheafComplex C S f).X (-(n : ℤ))).val.obj V :=
  (((S.sheaves T f).standard.complexIso.hom.f (-(n : ℤ))).val.app V)
    (((((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (S.sheaves T f).standard.differentials).extendXIso
        ComplexShape.embeddingDownNat (i := n) rfl).inv.val.app V)
      (((S.sheaves T f).standard.differentialIso n).inv.val.app V
        (differentialSection ((S.sheaves T f).standard.base.app (op ⦋n⦌))
          ((S.sheaves T f).standard.augmentation.app (op ⦋n⦌)) V c x)))

/-- The normalized short exact sequence and roof, for a fixed injective ring-sheaf
map. Quotient and differential presentations are specified on generators, so
existence of this structure asserts the canonical construction, not existence
of arbitrary complexes or arbitrary arrows. Source: Stacks 08SD, 08SE, 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
structure InjectiveCotangentRoof (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1} j) where
  quotientQ : InjectiveQuotientModel C S F f j
  quotientR : InjectiveQuotientModel C S F (𝟙 B) j
  augmentationQ_quasiIso : QuasiIso (injectiveQuotientAugmentation quotientQ)
  augmentationR_quasiIso : QuasiIso (injectiveQuotientAugmentation quotientR)
  differentialQ : QuotientDifferentials B E (injectiveQuotient C S F f j)
    (injectiveQuotientRight C S F f j) quotientQ.augmentation
  differentialR : QuotientDifferentials B E (injectiveQuotient C S F (𝟙 B) j)
    (injectiveQuotientRight C S F (𝟙 B) j) quotientR.augmentation
  quotientMap : injectiveQuotient C S F f j ⟶ injectiveQuotient C S F (𝟙 B) j
  quotientMap_left : injectiveQuotientLeft C S F f j ≫ quotientMap =
    (F.functoriality.polynomial (v := 𝟙 T)
      (f := Arrow.mk (f ≫ j)) (g := Arrow.mk j) (injectiveBaseSquare f j)).map ≫
        injectiveQuotientLeft C S F (𝟙 B) j
  quotientMap_right : injectiveQuotientRight C S F f j ≫ quotientMap =
    injectiveQuotientRight C S F (𝟙 B) j
  quotientMap_augmentation : quotientMap ≫ quotientR.augmentation = quotientQ.augmentation
  first : StandardLinearization C S (injectiveTargetSquare f j) D
  quotientArrow : standardSheafComplex C S (Arrow.mk (f ≫ j)) ⟶
    quotientDifferentialComplex differentialQ
  quotientArrow_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ) (c : E.obj.obj V)
    (x : ((S.sheaves T (Arrow.mk (f ≫ j))).standard.algebra.obj (op ⦋n⦌)).obj.obj V),
    (quotientArrow.f (-(n : ℤ))).val.app V
      (standardSheafGenerator C S (Arrow.mk (f ≫ j)) n V c x) =
      quotientDifferentialGenerator differentialQ n V c
        (((injectiveQuotientLeft C S F f j).app (op ⦋n⦌)).hom.app V x)
  alpha : standardSheafComplex C S (Arrow.mk j) ⟶
    quotientDifferentialComplex differentialR
  alpha_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ) (c : E.obj.obj V)
    (x : ((S.sheaves T (Arrow.mk j)).standard.algebra.obj (op ⦋n⦌)).obj.obj V),
    (alpha.f (-(n : ℤ))).val.app V (standardSheafGenerator C S (Arrow.mk j) n V c x) =
      quotientDifferentialGenerator differentialR n V c
        (((injectiveQuotientLeft C S F (𝟙 B) j).app (op ⦋n⦌)).hom.app V x)
  beta : quotientDifferentialComplex differentialQ ⟶ quotientDifferentialComplex differentialR
  beta_formula : ∀ (n : ℕ) (V : (Opens T)ᵒᵖ) (c : E.obj.obj V)
    (x : ((injectiveQuotient C S F f j).obj (op ⦋n⦌)).obj.obj V),
    (beta.f (-(n : ℤ))).val.app V (quotientDifferentialGenerator differentialQ n V c x) =
      quotientDifferentialGenerator differentialR n V c ((quotientMap.app (op ⦋n⦌)).hom.app V x)
  alpha_quasiIso : QuasiIso alpha
  beta_quasiIso : QuasiIso beta
  zero : first.map ≫ quotientArrow = 0
  shortExact : ∀ i : ℤ,
    (ShortComplex.mk (first.map.f i) (quotientArrow.f i)
      (congrArg (fun h ↦ h.f i) zero)).ShortExact
  baseArrow : standardSheafComplex C S (Arrow.mk (f ≫ j)) ⟶
    standardSheafComplex C S (Arrow.mk j)
  baseArrow_formula : ∀ (V : (Opens T)ᵒᵖ) (i : ℤ)
    (x : ((standardSheafComplex C S (Arrow.mk (f ≫ j))).X i).val.obj V),
    (baseArrow.f i).val.app V x =
      (((S.maps (v := 𝟙 T) (f := Arrow.mk (f ≫ j)) (g := Arrow.mk j)
        (injectiveBaseSquare f j)).map.f i).hom.app V x)
  arrow_square : quotientArrow ≫ beta = baseArrow ≫ alpha
  derivedIso : (DerivedCategory.Q.{u + 1} (C := ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring E))).obj (quotientDifferentialComplex differentialQ) ≅
    (DerivedCategory.Q.{u + 1} (C := ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring E))).obj (standardSheafComplex C S (Arrow.mk j))
  derivedIso_roof :
    derivedIso.hom ≫
      (DerivedCategory.Q.{u + 1} (C := ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring E))).map alpha =
      (DerivedCategory.Q.{u + 1} (C := ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring E))).map beta
  derivedIso_arrow : (DerivedCategory.Q.{u + 1} (C := ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring E))).map quotientArrow ≫ derivedIso.hom =
    (DerivedCategory.Q.{u + 1} (C := ringedSiteModules.{u}
      (CategoryTheory.SheafDifferentials.ring E))).map baseArrow

/-- Forget scalars on complexes without changing any underlying sections.
Source: Stacks 08SZ (blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def roofForget {T : TopCat.{u}} (E : T.Sheaf CommRingCat.{u}) :=
  (SheafOfModules.toSheaf (CategoryTheory.SheafDifferentials.ring E)).mapHomologicalComplex
    (.up ℤ)

/-- Restriction to an open subspace on ring sheaves, with literal section coordinates.
Source: Stacks 08SZ (blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def roofOpenRings {T : TopCat.{u}} (U : Opens T) :=
  U.isOpenEmbedding.sheafPullback CommRingCat.{u}

/-- Restriction to an open subspace on additive complexes. Source: Stacks 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def roofOpenComplex {T : TopCat.{u}} (U : Opens T) :=
  letI : (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).Additive :=
    { map_add := rfl }
  (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)

/-- A quotient tensor section in the sheafification's fixed coordinates.
Source: Stacks 08SD, 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def quotientTensorSection {C : Coherence.{u}} {S : Comparison C}
    {F : FlatFunctorialModel C S} {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    {f : A ⟶ B} {j : B ⟶ E} (M : InjectiveQuotientModel C S F f j)
    (n : ℕ) (V : (Opens T)ᵒᵖ)
    (p : standardTerm (sectionArrow (Arrow.mk (f ≫ j)) V) n) (b : B.obj.obj V) :
    ((injectiveQuotient C S F f j).obj (op ⦋n⦌)).obj.obj V :=
  (M.sheafification n).hom.hom.app V
    ((toSheafify (Opens.grothendieckTopology T) (M.presheaf n)).app V
      ((M.coordinate n V).inv (injectiveQuotientTensor C f j V n p b)))

/-- A sectionwise differential generator followed by sheafification.
Source: Stacks 08SS, 08SX
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def roofLocalGenerator (C : Coherence.{u}) (S : Comparison C) {T : TopCat.{u}}
    (f : Arrow (T.Sheaf CommRingCat.{u})) (n : ℕ) (V : (Opens T)ᵒᵖ)
    (b : f.right.obj.obj V) (p : standardTerm (sectionArrow f V) n) :
    ((standardSheafComplex C S f).X (-(n : ℤ))).val.obj V :=
  sectionElement (S.sheaves T f).sections V (-(n : ℤ))
    (complexGenerator (C.differentials (C.standard (sectionArrow f V))) n b
      (eqToHom ((C.standard_spec (sectionArrow f V)).1 n).symm p))

/-- A local tensor generator in the actual ordinary scalar extension.
Source: Stacks 08SZ, 06YY
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
def roofFirstGenerator (C : Coherence.{u}) (S : Comparison C) {T : TopCat.{u}}
    {A B E : T.Sheaf CommRingCat.{u}} (f : A ⟶ B) (j : B ⟶ E)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1} j)
    (n : ℕ) (V : (Opens T)ᵒᵖ) (c : E.obj.obj V) (b : B.obj.obj V)
    (p : standardTerm (sectionArrow (Arrow.mk f) V) n) :
    (((D.E.mapHomologicalComplex (.up ℤ)).obj
      (standardSheafComplex C S (Arrow.mk f))).X (-(n : ℤ))).val.obj V :=
  (eqToHom (D.obj_eq ((standardSheafComplex C S (Arrow.mk f)).X (-(n : ℤ)))).symm).val.app V
    (scalarExtensionSection j ((standardSheafComplex C S (Arrow.mk f)).X (-(n : ℤ))) V c
      (roofLocalGenerator C S (Arrow.mk f) n V b p))

/-- The restriction comparisons for the whole sequence and roof. Ring comparisons
are fixed on pure quotient tensors, and differential comparisons on their local
universal differentials. The commuting squares include the standard base arrow;
consequently the chain square and its localized inverse-roof equality restrict too.
Source: Stacks 08SE, 08SZ and 08SX
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof). -/
structure InjectiveRoofOpenRestriction (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    {f : A ⟶ B} {j : B ⟶ E}
    {D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1} j}
    (M : InjectiveCotangentRoof C S F f j D) (U : Opens T)
    {D' : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
      ((roofOpenRings U).map j)}
    (N : InjectiveCotangentRoof C S F ((roofOpenRings U).map f)
      ((roofOpenRings U).map j) D') where
  algebraQ : injectiveQuotient C S F f j ⋙ roofOpenRings U ≅
    injectiveQuotient C S F ((roofOpenRings U).map f) ((roofOpenRings U).map j)
  algebraR : injectiveQuotient C S F (𝟙 B) j ⋙ roofOpenRings U ≅
    injectiveQuotient C S F (𝟙 ((roofOpenRings U).obj B)) ((roofOpenRings U).map j)
  algebraQ_tensor : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (p : standardTerm
      (sectionArrow (Arrow.mk (f ≫ j)) (U.isOpenEmbedding.functor.op.obj W)) n)
    (b : B.obj.obj (U.isOpenEmbedding.functor.op.obj W)),
    (algebraQ.hom.app (op ⦋n⦌)).hom.app W
      (quotientTensorSection M.quotientQ n (U.isOpenEmbedding.functor.op.obj W) p b) =
        quotientTensorSection N.quotientQ n W p b
  algebraR_tensor : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (p : standardTerm
      (sectionArrow (Arrow.mk ((𝟙 B) ≫ j)) (U.isOpenEmbedding.functor.op.obj W)) n)
    (b : B.obj.obj (U.isOpenEmbedding.functor.op.obj W)),
    (algebraR.hom.app (op ⦋n⦌)).hom.app W
      (quotientTensorSection M.quotientR n (U.isOpenEmbedding.functor.op.obj W) p b) =
        quotientTensorSection N.quotientR n W p b
  first : (roofOpenComplex U).obj ((roofForget E).obj
      ((D.E.mapHomologicalComplex (.up ℤ)).obj (standardSheafComplex C S (Arrow.mk f)))) ≅
    (roofForget ((roofOpenRings U).obj E)).obj
      ((D'.E.mapHomologicalComplex (.up ℤ)).obj
        (standardSheafComplex C S (Arrow.mk ((roofOpenRings U).map f))))
  middle : (roofOpenComplex U).obj
      ((roofForget E).obj (standardSheafComplex C S (Arrow.mk (f ≫ j)))) ≅
    (roofForget ((roofOpenRings U).obj E)).obj
      (standardSheafComplex C S (Arrow.mk ((roofOpenRings U).map f ≫ (roofOpenRings U).map j)))
  last : (roofOpenComplex U).obj
      ((roofForget E).obj (standardSheafComplex C S (Arrow.mk j))) ≅
    (roofForget ((roofOpenRings U).obj E)).obj
      (standardSheafComplex C S (Arrow.mk ((roofOpenRings U).map j)))
  quotientQ : (roofOpenComplex U).obj
      ((roofForget E).obj (quotientDifferentialComplex M.differentialQ)) ≅
    (roofForget ((roofOpenRings U).obj E)).obj (quotientDifferentialComplex N.differentialQ)
  quotientR : (roofOpenComplex U).obj
      ((roofForget E).obj (quotientDifferentialComplex M.differentialR)) ≅
    (roofForget ((roofOpenRings U).obj E)).obj (quotientDifferentialComplex N.differentialR)
  quotientQ_generator : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (c : E.obj.obj (U.isOpenEmbedding.functor.op.obj W))
    (x : ((injectiveQuotient C S F f j).obj (op ⦋n⦌)).obj.obj
      (U.isOpenEmbedding.functor.op.obj W)),
    (quotientQ.hom.f (-(n : ℤ))).hom.app W
      (quotientDifferentialGenerator M.differentialQ n
        (U.isOpenEmbedding.functor.op.obj W) c x) =
      quotientDifferentialGenerator N.differentialQ n W c
        ((algebraQ.hom.app (op ⦋n⦌)).hom.app W x)
  quotientR_generator : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (c : E.obj.obj (U.isOpenEmbedding.functor.op.obj W))
    (x : ((injectiveQuotient C S F (𝟙 B) j).obj (op ⦋n⦌)).obj.obj
      (U.isOpenEmbedding.functor.op.obj W)),
    (quotientR.hom.f (-(n : ℤ))).hom.app W
      (quotientDifferentialGenerator M.differentialR n
        (U.isOpenEmbedding.functor.op.obj W) c x) =
      quotientDifferentialGenerator N.differentialR n W c
        ((algebraR.hom.app (op ⦋n⦌)).hom.app W x)
  first_generator : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (c : E.obj.obj (U.isOpenEmbedding.functor.op.obj W))
    (b : B.obj.obj (U.isOpenEmbedding.functor.op.obj W))
    (p : standardTerm (sectionArrow (Arrow.mk f) (U.isOpenEmbedding.functor.op.obj W)) n),
    (first.hom.f (-(n : ℤ))).hom.app W
      (roofFirstGenerator C S f j D n (U.isOpenEmbedding.functor.op.obj W) c b p) =
      roofFirstGenerator C S ((roofOpenRings U).map f) ((roofOpenRings U).map j)
        D' n W c b p
  middle_generator : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (c : E.obj.obj (U.isOpenEmbedding.functor.op.obj W))
    (p : standardTerm
      (sectionArrow (Arrow.mk (f ≫ j)) (U.isOpenEmbedding.functor.op.obj W)) n),
    (middle.hom.f (-(n : ℤ))).hom.app W
      (roofLocalGenerator C S (Arrow.mk (f ≫ j)) n
        (U.isOpenEmbedding.functor.op.obj W) c p) =
      roofLocalGenerator C S
        (Arrow.mk ((roofOpenRings U).map f ≫ (roofOpenRings U).map j)) n W c p
  last_generator : ∀ (n : ℕ) (W : (Opens U)ᵒᵖ)
    (c : E.obj.obj (U.isOpenEmbedding.functor.op.obj W))
    (p : standardTerm (sectionArrow (Arrow.mk j) (U.isOpenEmbedding.functor.op.obj W)) n),
    (last.hom.f (-(n : ℤ))).hom.app W
      (roofLocalGenerator C S (Arrow.mk j) n (U.isOpenEmbedding.functor.op.obj W) c p) =
      roofLocalGenerator C S (Arrow.mk ((roofOpenRings U).map j)) n W c p
  algebraQ_augmentation : algebraQ.hom ≫ N.quotientQ.augmentation =
    Functor.whiskerRight M.quotientQ.augmentation (roofOpenRings U)
  algebraR_augmentation : algebraR.hom ≫ N.quotientR.augmentation =
    Functor.whiskerRight M.quotientR.augmentation (roofOpenRings U)
  algebra_map : Functor.whiskerRight M.quotientMap (roofOpenRings U) ≫ algebraR.hom =
    algebraQ.hom ≫ N.quotientMap
  first_square : (roofOpenComplex U).map ((roofForget E).map M.first.map) ≫ middle.hom =
    first.hom ≫ (roofForget ((roofOpenRings U).obj E)).map N.first.map
  quotient_square : (roofOpenComplex U).map ((roofForget E).map M.quotientArrow) ≫
    quotientQ.hom = middle.hom ≫ (roofForget ((roofOpenRings U).obj E)).map N.quotientArrow
  alpha_square : (roofOpenComplex U).map ((roofForget E).map M.alpha) ≫ quotientR.hom =
    last.hom ≫ (roofForget ((roofOpenRings U).obj E)).map N.alpha
  beta_square : (roofOpenComplex U).map ((roofForget E).map M.beta) ≫ quotientR.hom =
    quotientQ.hom ≫ (roofForget ((roofOpenRings U).obj E)).map N.beta
  base_square : (roofOpenComplex U).map ((roofForget E).map M.baseArrow) ≫ last.hom =
    middle.hom ≫ (roofForget ((roofOpenRings U).obj E)).map N.baseArrow

/-- The injective ring-sheaf differential sequence and its canonical
quotient-resolution roof exist, and their normalized comparisons commute
with restriction to every open subspace. No flatness of `E` over `B` is assumed.
`C`, `S`, `F` and `D` present the already recorded standard and tensor constructions.
Source: Stacks Project, cotangent.tex, Tags 08SD, 08SE and 08SZ
(blueprint: lem-sfb-injective-sheaf-cotangent-sequence-roof).

Proof:
1. On each open write A, B, C for the section rings. Injectivity of B → C
   recursively includes the variables of P in those of Q. Polynomial coefficient
   lists show injectivity at the next stage. Complementary variables exhibit Q_n
   as P_n[Y_n], and similarly R_n as S_n[Z_n]. Complements define no maps.
2. Apply lem-sfb-injective-standard-resolution-quotients to A → B → C and
   B → B → C. Both tensor quotients are polynomial resolutions in the exact
   sense of lem-trf-cotangent-resolution-coherence, without assuming flatness
   of B → C.
3. By lem-weil-pbc-polynomial-ring-kahler-basis-any-variables, after tensoring
   to C the differential modules are free on old variables, all variables, and
   complementary variables. The canonical arrows include old coordinates and
   project onto new coordinates. Coordinate kernels, injections and lifts give
   degreewise split exactness, also for infinite variable sets. Their universal
   differential formulas commute with simplicial operators and alternating faces.
4. Strict standard functoriality supplies the square P → Q, S → R. The tensor
   universal property gives Qbar → Rbar, q tensor b mapped to f(q) tensor b.
   Augmentations and simplicial operators commute on pure tensors. Universal
   differentials give alpha and beta with the displayed formulas.
5. Compare R, Qbar and Rbar with the standard polynomial resolution by
   lem-trf-cotangent-resolution-coherence. Naturality makes alpha and beta
   isomorphisms in D(C), hence quasi-isomorphisms. Restriction of scalars
   computes kernels and cohomology on the same elements; the inverse of a
   bijective C-linear map is C-linear.
6. Sheafify these canonical constructions on all opens. The iterated standard
   sheaf resolution is the sheafified sectionwise resolution: induct using
   lem-pc-sites-sheafification-underlying-sets and the free-algebra universal
   property of def-weil-pbc-sheafification, as in
   lem-trf-affine-cotangent-comparison. Faces and augmentations have the same formulas.
7. Apply lem-pc-sites-module-sheafification-tensor and
   lem-trf-sheafified-module-differentials-cokernel. Tensor associativity
   identifies the first term with K[B/A] tensor_B C. Exact module sheafification
   preserves the sequence and cohomology, including both quotient augmentations.
8. On every differential generator beta q and alpha v both send dq tensor c
   to d(f(q) tensor 1) tensor c. Thus the chain square commutes. Invert alpha
   in the localization def-weil-abstract-derived-category; the roof is an
   isomorphism and carries q to the canonical base-ring arrow v. The first
   arrow is the normalized standard linearization from
   lem-sfb-standard-sheaf-cotangent-flat-functorial-model.
9. Restriction sends z tensor b to z|_V tensor b|_V and dz tensor c to
   d(z|_V) tensor c|_V. Strict standard composition and the preceding generator
   formulas make every square commute. For an open subspace the sectionwise
   data are literally the restricted data. Apply
   lem-sp-module-slice-sheafification-independent-ring to commute sheafification
   with open restriction. This gives the normalized restriction isomorphisms
   of the whole sequence and roof. Localizing their commuting squares and
   inverting alpha also restricts the derived identification and arrow equality. -/
theorem exists_injectiveCotangentRoof (C : Coherence.{u}) (S : Comparison C)
    (F : FlatFunctorialModel C S) {T : TopCat.{u}} {A B E : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (j : B ⟶ E) (hj : ∀ V : (Opens T)ᵒᵖ, Function.Injective (j.hom.app V))
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1} j) :
    ∃ M : InjectiveCotangentRoof C S F f j D,
      ∀ (U : Opens T)
        (D' : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, u, u, u + 1, u + 1}
          ((roofOpenRings U).map j)),
      ∃ N : InjectiveCotangentRoof C S F ((roofOpenRings U).map f)
        ((roofOpenRings U).map j) D', Nonempty (InjectiveRoofOpenRestriction C S F M U N) := by
  sorry

end TopCat.SheafCotangent
