/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CurvePerverseHeartStatement.CurvePerverseHeartStatement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Condensed curve perverse intermediate extension

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`,
ordinary direct-image paragraph.
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

open WeilConjectures
open WeilConjectures.NativeL2
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
  (c : Scheme.MiddleExtensionCurve D)

/-- The condensed coefficient ring of $\overline{\mathbf Q}_\ell$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev coeff (ell : ℕ) [Fact ell.Prime] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.padicAlgClRingObj ell
/-- The geometric open $U=U_0\otimes_{k_0}k$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev geomU (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  (D.geometricFiber c.U).left
/-- The geometric curve $C=C_0\otimes_{k_0}k$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev geomC (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  (D.geometricFiber c.C).left
/-- The geometric open immersion $j:U\to C$, base change of $j_0$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev geomJ (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  NativeL2.geometricMap D c.j
/-- The geometric Frobenius automorphism $g_U$ of $U$ defining Weil structures.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev frobU (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  StrictWeilCondensed.modelFrobenius D c.U
/-- The geometric Frobenius automorphism $g_C$ of $C$ defining Weil structures.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev frobC (D : FiniteFieldDatum.{u}) (c : Scheme.MiddleExtensionCurve D) :=
  StrictWeilCondensed.modelFrobenius D c.C
/-- Module sheaves over the condensed coefficient ring on the pro-étale site
(the ambient category of thm-a1-curve-perverse-heart).
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev Modules (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X : Scheme.{u}) :=
  CurvePerverseHeartStatement.Modules ell X
/-- The perverse heart ${}^pD^{\le0}(C)\cap{}^pD^{\ge0}(C)$ of thm-a1-curve-perverse-heart
inside the bounded constructible derived category of the geometric curve.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev perverseHeart (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) (hEll : ell ≠ D.p) :
    ObjectProperty (DerivedCategory (Modules D ell (geomC D c))) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
  letI : Invertible (ell : D.k) := invertibleOfNonzero
    (by
      intro h
      have hd : D.p ∣ ell := by
        exact (CharP.cast_eq_zero_iff D.k D.p ell).mp h
      exact hEll ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : ell.Prime)).mp hd).symm)
  letI : LocallyOfFiniteType (D.geometricFiber c.C).hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : QuasiCompact (D.geometricFiber c.C).hom := inferInstanceAs
    (QuasiCompact (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : IsSeparated (D.geometricFiber c.C).hom := inferInstanceAs
    (IsSeparated (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  fun K => CurvePerverseHeartStatement.InHeart
    (AlgebraicGeometry.ProEtale.boundedConstructible
      (condensedRingObj (coeff ell) (geomC D c)))
    (fun K : (AlgebraicGeometry.ProEtale.boundedConstructible
        (condensedRingObj (coeff ell) (geomC D c))).FullSubcategory ↦
      CondensedRing.CondensedPerverseLEZero ell (D.geometricFiber c.C)
        ⟨K.obj, K.property⟩)
    (fun K : (AlgebraicGeometry.ProEtale.boundedConstructible
        (condensedRingObj (coeff ell) (geomC D c))).FullSubcategory ↦
      CondensedRing.CondensedPerverseGEZero ell (D.geometricFiber c.C)
        ⟨K.obj, K.property⟩)
    K
/-- The ordinary module direct image $A=j_*F$ (def-wf-middle-extension).
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev image (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) : Modules D ell (geomC D c) :=
  (NativeL2.middleImage D ell c.j).obj F.carrier
/-- The shifted ordinary direct image $(j_*F)[1]$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev shiftedImage (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    DerivedCategory (Modules D ell (geomC D c)) :=
  (NativeL2.shiftedMiddleImage D ell c.j).obj F.carrier
/-- The derived restriction $j^*$ to the geometric open.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev restriction (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) :
    DerivedCategory (Modules D ell (geomC D c)) ⥤
      DerivedCategory (Modules D ell (geomU D c)) :=
  (CondensedRing.upperStar (coeff ell) (geomJ D c)).mapDerivedCategory
/-- A sheaf on $U$ placed in degree zero and shifted by one: $F\mapsto F[1]$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
abbrev shiftedSheaf (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) :
    Modules D ell (geomU D c) ⥤ DerivedCategory (Modules D ell (geomU D c)) :=
  DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)

/-- The canonical identification $j^*((j_*F)[1])\to F[1]$: shift and single-complex
commutation of $j^*$ followed by the shifted counit $j^*j_*F\to F$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def openIdentificationMap (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    (restriction D ell c).obj (shiftedImage D ell c F) ⟶
      (shiftedSheaf D ell c).obj F.carrier :=
  ((restriction D ell c).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (image D ell c F)) ≫
    (shiftFunctor _ (1 : ℤ)).map
      (((CondensedRing.upperStar (coeff ell) (geomJ D c)).mapDerivedCategorySingleFunctor 0).hom.app
        (image D ell c F)) ≫
    (shiftedSheaf D ell c).map
      ((CondensedRing.upperStarLowerStarAdjunction (coeff ell) (geomJ D c)).counit.app F.carrier)

/-- Both boundary Hom vanishings: $\operatorname{Hom}(Q,P)=0=\operatorname{Hom}(P,Q)$ for every
heart object $Q$ with $j^*Q=0$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def BoundaryMinimal (_F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) (P :
    DerivedCategory (Modules D ell (geomC D c))) (hEll : ell ≠ D.p) : Prop :=
  ∀ Q : DerivedCategory (Modules D ell (geomC D c)),
    perverseHeart D ell c hEll Q →
    IsZero ((restriction D ell c).obj Q) →
      (∀ f : Q ⟶ P, f = 0) ∧ (∀ f : P ⟶ Q, f = 0)

/-- The pullback composition comparison $\rho:g_U^*j^*\simeq j^*g_C^*$, from the
canonical square $j g_U=g_C j$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def restrictionFrobeniusComparison :
    restriction D ell c ⋙ StrictWeilCondensed.action (coeff ell) (frobU D c) ≅
      StrictWeilCondensed.action (coeff ell) (frobC D c) ⋙ restriction D ell c :=
  (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar (coeff ell) (geomJ D c))
      (CondensedRing.upperStar (coeff ell) (frobU D c).hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarSquareComparison (coeff ell)
        (CommSq.mk (NativeL2.frobeniusSquare D c.j).w)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar (coeff ell) (frobC D c).hom)
      (CondensedRing.upperStar (coeff ell) (geomJ D c))

/-- The Weil structure of $F[1]$ induced by that of $F$.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def shiftedWeilMap (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) :
    (StrictWeilCondensed.action (coeff ell) (frobU D c)).obj
        ((shiftedSheaf D ell c).obj F.carrier) ⟶
      (shiftedSheaf D ell c).obj F.carrier :=
  ((StrictWeilCondensed.action (coeff ell) (frobU D c)).commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj F.carrier) ≫
    (shiftFunctor _ (1 : ℤ)).map
      (((CondensedRing.upperStar (coeff ell) (frobU D c).hom).mapDerivedCategorySingleFunctor
        0).hom.app F.carrier) ≫
    (shiftedSheaf D ell c).map F.str.hom

/-- All clauses of the node: heart membership, the canonical open identification,
the boundary-Hom characterization with unique normalized comparison, and Weil compatibility.
Source: `rem-dl-a1-conventions.md`, ordinary direct-image paragraph
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension). -/
def IntermediateExtensionAssertion
    (hEll : ell ≠ D.p)
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c)) : Prop :=
  perverseHeart D ell c hEll (shiftedImage D ell c F) ∧
    ∃ β : (restriction D ell c).obj (shiftedImage D ell c F) ≅
        (shiftedSheaf D ell c).obj F.carrier,
      β.hom = openIdentificationMap D ell c F ∧
      BoundaryMinimal D ell c F (shiftedImage D ell c F) hEll ∧
      (∀ P : DerivedCategory (Modules D ell (geomC D c)),
        perverseHeart D ell c hEll P →
        ∀ α : (restriction D ell c).obj P ≅
          (shiftedSheaf D ell c).obj F.carrier,
          BoundaryMinimal D ell c F P hEll ↔
            ∃! e : P ≅ shiftedImage D ell c F,
              (restriction D ell c).map e.hom ≫ β.hom = α.hom) ∧
      ∃ θA : (StrictWeilCondensed.action (coeff ell) (frobC D c)).obj
          (shiftedImage D ell c F) ≅ shiftedImage D ell c F,
        (restrictionFrobeniusComparison D ell c).hom.app _ ≫
            (restriction D ell c).map θA.hom ≫ β.hom =
          (StrictWeilCondensed.action (coeff ell) (frobU D c)).map β.hom ≫
            shiftedWeilMap D ell c F ∧
        ∀ P : DerivedCategory (Modules D ell (geomC D c)),
          perverseHeart D ell c hEll P →
          BoundaryMinimal D ell c F P hEll →
          ∀ (α : (restriction D ell c).obj P ≅
            (shiftedSheaf D ell c).obj F.carrier)
            (θP : (StrictWeilCondensed.action (coeff ell) (frobC D c)).obj P ≅ P)
            (e : P ≅ shiftedImage D ell c F),
            (restriction D ell c).map e.hom ≫ β.hom = α.hom →
            (restrictionFrobeniusComparison D ell c).hom.app P ≫
                (restriction D ell c).map θP.hom ≫ α.hom =
              (StrictWeilCondensed.action (coeff ell) (frobU D c)).map α.hom ≫
                shiftedWeilMap D ell c F →
            θP.hom ≫ e.hom = (StrictWeilCondensed.action (coeff ell) (frobC D c)).map e.hom ≫ θA.hom

/-- The ordinary direct image shifted by one is the perverse intermediate extension.
Proof (deferred at stage 2), following the nine DAG steps.  (1) Base change preserves
separatedness, finite type, smoothness, geometric connectedness and dimension one; the
open remains dense and has finite closed complement.  (2) Apply the current definition
of the ordinary degree-zero direct image and the curve-heart basic-object clause; the
open counit is the canonical identification.  (3) A heart object restricting to zero
has only degree-zero punctual cohomology by the curve-heart description.  (4) The
Ext-one classification and ordinary adjunction retract the first map of an extension,
forcing the boundary-to-image Hom to vanish; standard t-structure orthogonality gives
the reverse vanishing.  (5) The truncation exact sequence and minimality kill degree
zero, so every minimal extension is a shifted sheaf.  (6) The adjoint to the ordinary
direct image has punctual kernel and cokernel; the kernel-free and boundary-minimal
arguments make it an isomorphism.  (7) Full faithfulness of shifted single complexes
and ordinary adjunction give the unique comparison with the prescribed open map.
(8) The canonical Frobenius square and degree-zero comparison give the induced Weil
isomorphism, normalized on the open.  (9) Uniqueness of the normalized comparison
proves Weil equivariance.  The assertion is stated in the geometric derived category,
with the Weil convention supplied by the current curve-heart interface.
Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/rem-dl-a1-conventions.md`;
(blueprint: lem-dl-a1-condensed-curve-intermediate-extension).
-/
theorem condensed_curve_intermediate_extension
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D)
    (_hEll : ell ≠ D.p) [GeometricallyConnected c.C.hom]
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    (_hCons : IsConstantModelConstructible (coeff ell) (geomU D c) F.carrier)
    (_hLisse : IsLisseCoefficientModule (coeff ell) F.carrier) :
    IntermediateExtensionAssertion D ell c _hEll F := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
