/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
public import Sheaf.CategoryTheory.Sites.TorsorWithSection
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Sheaf.CategoryTheory.SignedFibreTriangulated
import Sheaf.CategoryTheory.BoundedInjectiveFibreDescent
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Sheaf.AlgebraicGeometry.RelativeEtaleCohomology
import WeilConjectures.CategoryTheory.Sites.Torsor

/-!
# Relative torsor representatives and boundary signs

Source: Stacks Project, Tag 03AJ, and the relative refinement in blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, clause (a)
(blueprint: lem-pur-divisor-torsor-boundary-signs).

-- Q32 revalidation delivery of the reviewed statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

/-- The constant section one of the extension presentation.
Source: Stacks Tag 03AJ (blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorExtensionOne (T : Scheme.{u}) (U : T.Etale) :
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).obj.obj (op U) :=
  (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op U) ⟨1⟩

/-- First signed coordinate of the actual shifted cone, transported out of extension by zero.
Source: Stacks Tag 03AJ, signed relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorSignedA (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    (relativeSectionComplex T U I).X ((q : ℤ) + 1) ⟶
      (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((CochainComplex.mappingCone (relativeSectionRestriction T U I)).shiftFunctorObjXIso
    (-1) ((q : ℤ) + 1) q (add_neg_cancel_right (q : ℤ) 1).symm).hom ≫
  homotopyCofiber.fstX (relativeSectionRestriction T U I) q ((q : ℤ) + 1) rfl ≫
  ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat (Nat.cast_add q 1)).hom

/-- Second signed coordinate is minus the ordinary cone's second coordinate.
Thus the differential reads `(da,res a-db)`.
Source: Stacks Tag 03AJ, signed relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorSignedB (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    (relativeSectionComplex T U I).X ((q : ℤ) + 1) ⟶ (I.X q).obj.obj (op U) :=
  -(((CochainComplex.mappingCone (relativeSectionRestriction T U I)).shiftFunctorObjXIso
    (-1) ((q : ℤ) + 1) q (add_neg_cancel_right (q : ℤ) 1).symm).hom ≫
    homotopyCofiber.sndX (relativeSectionRestriction T U I) q ≫
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
        ComplexShape.embeddingUpNat rfl).hom)

/-- A signed pair represents a class precisely when it is the coordinates of a cycle
mapping to that class under Mathlib's homology quotient.
Source: Stacks Tag 03AJ, relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def TorsorSignedRepresents (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op U))
    (x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)) : Prop :=
  ∃ z : (relativeSectionComplex T U I).cycles ((q : ℤ) + 1),
    torsorSignedA T U I q ((relativeSectionComplex T U I).iCycles _ z) = a ∧
    torsorSignedB T U I q ((relativeSectionComplex T U I).iCycles _ z) = b ∧
    (relativeSectionComplex T U I).homologyπ _ z = x

/-- Localization boundary induced by the actual shifted cone inclusion. In signed
coordinates it sends `b` to `(0,-b)`.
Source: Stacks Tag 0G71; Tag 03AJ, relative refinement
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorLocalizationBoundary (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℤ) :
    (relativeSections U I).homology q ⟶ (relativeSectionComplex T U I).homology (q + 1) :=
  (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1} (-1) (q + 1) q
    ((congrArg (fun n : ℤ ↦ -1 + n) (add_comm q 1)).trans
      (neg_add_cancel_left 1 q))).inv.app (relativeSections U I) ≫
  homologyMap ((shiftFunctor _ (-1 : ℤ)).map
    (CochainComplex.mappingCone.inr (relativeSectionRestriction T U I))) (q + 1)

/-- The class of an ordinary section cocycle, using the extension-by-zero transport.
Source: Stacks Tags 011J and 03AJ
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def TorsorSectionRepresents {T : Scheme.{u}} (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op U)) (x : (relativeSections U I).homology (q : ℤ)) : Prop :=
  ∃ z : (relativeSections U I).cycles (q : ℤ),
    ((((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
      ComplexShape.embeddingUpNat rfl).hom ((relativeSections U I).iCycles q z) = b ∧
    (relativeSections U I).homologyπ q z = x

/-- The evaluated split resolution sequence over the specified open.
Source: Stacks Tags 011J and 013T
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
def torsorOpenShortComplex (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)) :=
  S.map (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})

/-- The representative and sign assertions for a simultaneous relative classification.
The extension presentation and resolution maps are arbitrary models, not chosen maps.
Source: Stacks Tag 03AJ and blueprint lem-pur-divisor-class.proof.md, clause (a)
(blueprint: lem-pur-divisor-torsor-boundary-signs). -/
structure DivisorTorsorBoundarySigns
    (e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1) : Prop where
  representative : ∀ (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (h : E.middle ⟶ I.cocomplex.X 0) (_hh : E.inclusion ≫ h = I.ι.f 0),
    ∃ a : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cocomplex.X 1,
      E.projection ≫ a = h ≫ I.cocomplex.d 0 1 ∧
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 0
        (a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))))
        (h.hom.app (op (Scheme.Etale.mk W.ι))
          (E.generator (op (Scheme.Etale.mk W.ι)) P.2))
        (e T W G I (Quotient.mk _ P))
  resolutions : ∀ (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I J : InjectiveResolution G) (a : I.Hom J (𝟙 G))
    (P : Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι)),
    homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1 (e T W G I P) =
      e T W G J P
  localization : ∀ (T : Scheme.{u}) (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) (q : ℕ)
    (b : (I.X q).obj.obj (op (Scheme.Etale.mk W.ι)))
    (x : (relativeSections (Scheme.Etale.mk W.ι) I).homology q),
    TorsorSectionRepresents (Scheme.Etale.mk W.ι) I q b x →
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I q 0 (-b)
        (torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I q x)
  trivial : ∀ (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (g : G.obj.obj (op (Scheme.Etale.mk W.ι))),
    ∃ x : (relativeSections (Scheme.Etale.mk W.ι) I.cocomplex).homology 0,
      TorsorSectionRepresents (Scheme.Etale.mk W.ι) I.cocomplex 0
        ((I.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) x ∧
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 0 0
        ((I.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g)
        (e T W G I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩)) ∧
      e T W G I (Quotient.mk _ ⟨Sheaf.Torsor.trivial G, g⟩) =
        -(torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 0 x)
  coefficients : ∀ (T : Scheme.{u}) (W : T.Opens)
    (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (_hS : S.ShortExact) (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (K : InjectiveResolution S.X₃) (a : I.cocomplex ⟶ J.cocomplex)
    (b : J.cocomplex ⟶ K.cocomplex) (hab : a ≫ b = 0)
    (_ha : I.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (_hb : J.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ K.ι)
    (hs : ∀ n : ℕ, Nonempty (((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)),
    ∃ hOpen : (torsorOpenShortComplex T (Scheme.Etale.mk W.ι)
        (ShortComplex.mk a b hab)).ShortExact,
      ∀ (g : S.X₃.obj.obj (op (Scheme.Etale.mk W.ι))),
      ∃ x : (relativeSections (Scheme.Etale.mk W.ι) K.cocomplex).homology 0,
        TorsorSectionRepresents (Scheme.Etale.mk W.ι) K.cocomplex 0
          ((K.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g) x ∧
        relativeConnecting T (Scheme.Etale.mk W.ι) (ShortComplex.mk a b hab) hs 1
            (e T W S.X₃ K (Quotient.mk _ ⟨Sheaf.Torsor.trivial S.X₃, g⟩)) =
          torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 1
            (hOpen.δ 0 1 rfl x) ∧
        ∀ (r : (J.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk W.ι)))
          (_hr : (b.f 0).hom.app (op (Scheme.Etale.mk W.ι)) r =
            (K.ι.f 0).hom.app (op (Scheme.Etale.mk W.ι)) g),
          ∃ c : (I.cocomplex.X 1).obj.obj (op (Scheme.Etale.mk W.ι)),
            (a.f 1).hom.app (op (Scheme.Etale.mk W.ι)) c =
              (J.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk W.ι)) r ∧
            TorsorSectionRepresents (Scheme.Etale.mk W.ι) I.cocomplex 1 c
              (hOpen.δ 0 1 rfl x) ∧
            TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 1 0 (-c)
              (relativeConnecting T (Scheme.Etale.mk W.ι) (ShortComplex.mk a b hab) hs 1
                (e T W S.X₃ K (Quotient.mk _ ⟨Sheaf.Torsor.trivial S.X₃, g⟩))) ∧
            TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I.cocomplex 1 0 (-c)
              (torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I.cocomplex 1
                (hOpen.δ 0 1 rfl x))
  extensions : ∀ (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
    (E : Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1)
    (h h' : E.middle ⟶ I.cocomplex.X 0)
    (_hh : E.inclusion ≫ h = I.ι.f 0) (_hh' : E.inclusion ≫ h' = I.ι.f 0)
    (a a' : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ I.cocomplex.X 1)
    (_ha : E.projection ≫ a = h ≫ I.cocomplex.d 0 1)
    (_ha' : E.projection ≫ a' = h' ≫ I.cocomplex.d 0 1),
    ∃ x : (I.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk (𝟙 T))),
      a'.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) -
        a.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T))) =
        (I.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) x ∧
      h'.hom.app (op (Scheme.Etale.mk W.ι))
          (E.generator (op (Scheme.Etale.mk W.ι)) P.2) -
        h.hom.app (op (Scheme.Etale.mk W.ι))
          (E.generator (op (Scheme.Etale.mk W.ι)) P.2) =
        (I.cocomplex.X 0).obj.map
          ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op x
  coefficient_representatives : ∀ (T : Scheme.{u}) (W : T.Opens)
    (I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ J) (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op (Scheme.Etale.mk W.ι)))
    (x : (relativeSectionComplex T (Scheme.Etale.mk W.ι) I).homology ((q : ℤ) + 1)),
    TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I q a b x →
      TorsorSignedRepresents T (Scheme.Etale.mk W.ι) J q
        ((f.f (q + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) a)
        ((f.f q).hom.app (op (Scheme.Etale.mk W.ι)) b)
        (homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f) ((q : ℤ) + 1) x)
  restriction_representatives : ∀ (T T' : Scheme.{u}) (h : T' ⟶ T) [Etale h]
    (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J)
    (q : ℕ) (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (b : (I.X q).obj.obj (op (Scheme.Etale.mk W.ι)))
    (x : (relativeSectionComplex T (Scheme.Etale.mk W.ι) I).homology ((q : ℤ) + 1)),
    TorsorSignedRepresents T (Scheme.Etale.mk W.ι) I q a b x →
      TorsorSignedRepresents T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J q
        ((globalResolutionSectionTransfer h I J f).f (q + 1) a)
        ((openResolutionSectionTransfer h I J f W).f q b)
        (homologyMap (relativeTransfer h W I J f) ((q : ℤ) + 1) x)
  localization_coefficients : ∀ (T : Scheme.{u}) (W : T.Opens)
    (I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ J) (q : ℤ),
    torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I q ≫
        homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f) (q + 1) =
      homologyMap (extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat) q ≫
        torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) J q
  localization_restriction : ∀ (T T' : Scheme.{u}) (h : T' ⟶ T) [Etale h]
    (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (f : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J)
    (q : ℤ),
    torsorLocalizationBoundary T (Scheme.Etale.mk W.ι) I q ≫
        homologyMap (relativeTransfer h W I J f) (q + 1) =
      homologyMap (extendMap (openResolutionSectionTransfer h I J f W)
        ComplexShape.embeddingUpNat) q ≫
        torsorLocalizationBoundary T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J q
  connecting_coefficients : ∀ (T : Scheme.{u}) (W : T.Opens)
    (S S' : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (hs' : ∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (f : S ⟶ S') (q : ℤ),
    relativeConnecting T (Scheme.Etale.mk W.ι) S hs q ≫
        homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f.τ₁) (q + 1) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk W.ι) f.τ₃) q ≫
        relativeConnecting T (Scheme.Etale.mk W.ι) S' hs' q
  connecting_restriction : ∀ (T T' : Scheme.{u}) (h : T' ⟶ T) [Etale h]
    (W : T.Opens)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (S' : ShortComplex
      (CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (hs' : ∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (f : S ⟶ S'.map ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)))
    (q : ℤ),
    relativeConnecting T (Scheme.Etale.mk W.ι) S hs q ≫
        homologyMap (relativeTransfer h W S.X₁ S'.X₁ f.τ₁) (q + 1) =
      homologyMap (relativeTransfer h W S.X₃ S'.X₃ f.τ₃) q ≫
        relativeConnecting T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' hs' q

/-- The canonical relative torsor classification admits the specified extension
representatives and the two boundary signs, simultaneously in all resolution models.
The first four compatibility clauses are exactly the interface of
`relative_torsor_cohomology`; the final conjunct specifies the representatives.
Source: Stacks Tag 03AJ; blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-divisor-class.proof.md, clause (a)
(blueprint: lem-pur-divisor-torsor-boundary-signs).

Proof:
1. Write A=I(T), B=I(W), and r for restriction. Changing the second coordinate of
Cone(r)[-1] by a minus sign gives D(a,b)=(da,ra-db). The isomorphism C[1] to Cone(r)
is (a,b) ↦ (-b,a), so the localization inclusion is b ↦ (0,-b).
Use def-amb-relative-etale-cohomology and lem-amb-signed-fibre-triangulated.
2. For the canonical torsor extension of lem-sc-torsor-h1 and
 def-sc-torsor-extension-presentation, extend the resolution augmentation to h.
Since dh kills G, it factors uniquely as a-bar times the projection. The projection
is epi, so da-bar=0. Evaluating at one gives a; evaluating h at the specified section
gives b, with db=res(a).
3. The map t ↦ h(generator(t)) identifies the torsor with the sheaf of solutions
dt=a, and carries its section to b. Locally every solution differs from a chosen one
by a unique section of G, since ker(d)=G. These local inverses glue by uniqueness.
Thus the relative classification of lem-amb-relative-torsor-cohomology sends the pair
to [(a,b)], including its prescribed nullhomotopy, not merely its absolute class.
4. The difference h'-h factors through the integer sheaf. Evaluating the factor at
one gives x, and the representative difference is (dx,res x)=D(x).
5. A resolution comparison u carries the pair to (u a,u b). Its augmentation equation
is strict because the source is concentrated in degree zero and the target is
nonnegative. The signed homotopy is (Ha,-Hb), so comparisons induce canonical maps
independent of choices, by lem-amb-bounded-injective-fibre-descent.
6. On the trivial torsor the universal property extends t ↦ augmentation(t) to h.
It gives dh=0, hence the representative is (0,g). By step 1 its class is minus the
localization boundary. If g extends over T this is the boundary D(g).
7. Use the split horseshoe of lem-weil-pbc-injective-resolution-ses. Sections and the
finite cone sums preserve its split rows. A lift r of g has differential in the image
of I1; let c be its unique preimage. It is closed. The absolute boundary is [c], by
lem-weil-pbc-complex-ses-connecting-formula. The differential of the relative lift
(0,r) is (0,-dr), so its boundary is [(0,-c)], also the localization boundary of [c].
Changing r by inclusion(t) changes this pair by (0,-dt)=D(0,t).
8. Etale restriction computes pullback on section resolutions by
lem-weil-pbc-cohomology-pullback-functorial, clause 5. All coordinates restrict
componentwise, including the minus sign. The relative classification is natural;
localization inclusions commute with cone maps; and
lem-weil-pbc-complex-ses-long-exact-naturality gives the connecting squares for any
coefficient-sequence morphism, without requiring preservation of a chosen splitting.
Together with steps 4-5 this proves naturality for arbitrary resolution choices. -/
theorem divisor_torsor_boundary_signs :
    ∃ e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1,
    ((∀ T W G I,
      e T W G I (Quotient.mk _
        ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op (Scheme.Etale.mk W.ι))) 0⟩) = 0) ∧
    (∀ T W G I (c : ResolutionSectionCanonicalComparison G I)
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)),
      relativeForgetH1 T W G I c (e T W G I (Quotient.mk _ P)) =
        Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
          (Quotient.mk _ P.1)) ∧
    (∀ (T : Scheme.{u}) (W : T.Opens)
      (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : G ⟶ G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.Hom J f) (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
      (Q : Sheaf.Torsor G') (q : Sheaf.Torsor.ContractedProductPresentation.{u, u} T f P.1 Q),
      HomologicalComplex.homologyMap
          (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1
          (e T W G I (Quotient.mk _ P)) =
        e T W G' J (Quotient.mk _ ⟨Q, q.quotient (op (Scheme.Etale.mk W.ι)) P.2 0⟩)) ∧
    (∀ (T T' : Scheme.{u}) (h : T' ⟶ T) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.cocomplex ⟶
        ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
      (_ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)) (Q : Sheaf.Torsor G')
      (b : P.1.sheaf.obj ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
      (_hb : ∀ (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.1.sheaf.obj.obj A),
        b.app A (P.1.vadd A g t) =
          Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj A.unop))
            (f.hom.app A g) (b.app A t)),
      HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) 1
          (e T W G I (Quotient.mk _ P)) =
        e T' (h ⁻¹ᵁ W) G' J (Quotient.mk _
          ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
            (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩))) ∧
    DivisorTorsorBoundarySigns e := by
  sorry

end AlgebraicGeometry.Etale
