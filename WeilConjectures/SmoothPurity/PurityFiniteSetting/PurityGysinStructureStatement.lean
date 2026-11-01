/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHomSpecified
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurGysinLocalizationPushforward
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinCohomologyExtraction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinExtractionHypotheses
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinOpenCoefficientIso
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinSupportHom
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummer

/-! # Structure of the zero-section exceptional object

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction,
lem-pur-gysin-structure.md and lem-pur-gysin-structure.proof.md, steps 1--4
(blueprint: lem-pur-gysin-structure).

Clause two uses only the specified supported-Hom map, the closed exceptional
adjunction, and evaluation on H^0. It asserts no comparison of whole localization
triangles and does not use RetractedSupport.Comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate open is the canonical complement, over the affine line.
Source: def-pur-affine-line-datum (blueprint: lem-pur-gysin-structure). -/
def gysinCoordinateComplement (Y : Scheme.{u}) :
    Scheme.ProEt.mk (openImmersion Y) ≅
      Scheme.ProEt.mk (zeroSection Y).openComplement.ι := by
  let h : Set.range (openImmersion Y).base =
      Set.range (zeroSection Y).openComplement.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact AffineSpace.range_basicOpen_ι_coord Y
  exact MorphismProperty.Over.isoMk
    (IsOpenImmersion.isoOfRangeEq (openImmersion Y) (zeroSection Y).openComplement.ι h)
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ h)

/-- Apply the specified supported-Hom map and then the actual closed adjunction.
The source is s_*A in degree zero; exactness identifies it with Rs_! A. The final
maps are the shift and bounded-below site-comparison isomorphisms. Source:
lem-pur-gysin-support-hom, its displayed composite
(blueprint: lem-pur-gysin-structure). -/
def gysinSupportToHom (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (x : P.gysinSupport h Y) :
    P.derivedSheaf h Y false ⟶ P.gysinValue h Y := by
  let s := zeroSection Y
  letI := (Compactification.ofIsProper s).hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace a
  letI : QuasiCompact (lineProjection Y) := by
    change QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
    infer_instance
  letI : CompactSpace (Line Y) :=
    QuasiCompact.compactSpace_of_compactSpace (lineProjection Y)
  let U := P.derivedSheaf h Y false
  let R := sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper s)
  let hU : ProEtale.DerivedCategory.plusEtaleOrigin (Modules P) Y U :=
    (ProEtale.DerivedCategory.plusEtaleOrigin (Modules P) Y).prop_of_iso
      ((comparisonUpperStar (Modules P) Y).mapDerivedCategorySingleFunctor 0 |>.app
        (P.constantEtale Y))
      (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
        (show _root_.DerivedCategory.TStructure.t.plus
          ((_root_.DerivedCategory.singleFunctor (EtSheaves P Y) 0).obj
            (P.constantEtale Y)) from ⟨0, inferInstance⟩))
  let hL : _root_.DerivedCategory.TStructure.t.plus ((P.gysinInput h Y).obj⟦(2 : ℤ)⟧) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((_root_.DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app (P.gysinInput h Y))
      ((P.gysinInput h Y)⟦(2 : ℤ)⟧).property
  let hc : IsCompl (Set.range s.base) (Set.range (openImmersion Y).base) := by
    rw [show Set.range (openImmersion Y).base = (Set.range s.base)ᶜ from
      AffineSpace.range_basicOpen_ι_coord Y]
    exact isCompl_compl
  letI : QuasiCompact (openImmersion Y) := by
    dsimp [openImmersion, Punctured]
    infer_instance
  letI : PreservesFiniteColimits (lowerStar (Modules P) s) :=
    preservesFiniteColimits_lowerStar_of_isCompl (R := P.Coefficient) s (openImmersion Y) hc
  let f := (supportedCohomologyHom P s 2).hom.app (P.gysinInput h Y) x
  let v :=
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (Modules P) s).hom.app U ≫
    (lowerStar (Modules P) s).rightDerivedFunctorIsoMapDerivedCategory.hom.app U ≫
    ((lowerStar (Modules P) s).mapDerivedCategorySingleFunctor 0).hom.app (P.constant Y) ≫ f
  exact rightDerivedUpperShriekHomEquiv s hU hL v ≫
    (comparisonUpperStar (Modules P) Y).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriek P.Coefficient s).map
        (((comparisonLowerStar (Modules P) (Line Y)).rightDerivedFunctor.commShiftIso
          (2 : ℤ)).hom.app (P.gysinInput h Y).obj) ≫
        ((Etale.rightDerivedUpperShriek P.Coefficient s).commShiftIso (2 : ℤ)).hom.app
          ((comparisonLowerStar (Modules P) (Line Y)).rightDerivedFunctor.obj
            (P.gysinInput h Y).obj)) ≫
    ((comparisonUpperStar (Modules P) Y).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      ((Etale.rightDerivedUpperShriek P.Coefficient s).obj
        ((comparisonLowerStar (Modules P) (Line Y)).rightDerivedFunctor.obj
          (P.gysinInput h Y).obj)) ≫
    (R.map (((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategoryPlusCompatibility.app
      (P.gysinEtaleInput h Y)).hom))⟦(2 : ℤ)⟧'

/-- The canonical map from supported classes to sections of H^0: supported-Hom,
closed adjunction, then H^0 and evaluation on 1. Source: proof step 4
(blueprint: lem-pur-gysin-structure). -/
def gysinSupportToSections (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (x : P.gysinSupport h Y) : (localClasses P Y 0).obj (P.gysinValue h Y) :=
  P.gysinHomToSections h Y (P.gysinSupportToHom h Y a x)

/-- The coordinate Kummer class in the actual open term of the support sequence.
The restriction coefficient isomorphism is constrained in the statement to have
the canonical root-pullback map as its forward map. Source: proof step 4
(blueprint: lem-pur-gysin-structure). -/
def gysinCoordinateSupportSection (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
      (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true) :
    (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y)) (Modules P)
      (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1).obj (P.gysinInput h Y) :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  let E := globalSectionsFunctor (Modules P) (Punctured Y)
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let e := Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory.symm
      E.rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' V E (openSectionsIso P j)
  let x := (_root_.DerivedCategory.homologyFunctor (Modules P) 1).map
    (E.rightDerivedFunctor.map b.inv ≫ e.hom.app (P.gysinInput h Y).obj)
      (P.gysinGlobalClass (Punctured Y) 1 (P.coordinateKummer h Y a).hom)
  let y := ((sectionPlusIso P (Line Y) (Scheme.ProEt.mk j) 1).hom.app
    (P.gysinInput h Y)) x
  ((complementSectionsIso P (zeroSection Y) j (gysinCoordinateComplement Y) 1).hom.app
    (P.gysinInput h Y)) y

/-- Structure of the exceptional inverse image of the zero section, with the
specified supported-Hom identification and coordinate boundary.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction,
lem-pur-gysin-structure.md and its proof, steps 1--4
(blueprint: lem-pur-gysin-structure).

Proof:
1. Apply lem-pur-gysin-localization-pushforward to the affine-line datum
   def-pur-affine-line-datum: pushing localization along p gives the triangle
   Rs! A(1) -> Rp_* A(1) -> Rpi_* A(1) -> Rs! A(1)[1]. Its middle arrow is
   the open-adjunction unit followed by the direct-image compositor.
2. prop-pur-gm-relative-kummer computes the middle and open terms. The unit
   composition identity fix-prop-adjunctions makes H^0 of the middle arrow
   invertible: its composite with the p-unit is the pi-unit.
3. lem-pur-gysin-cohomology-extraction gives H^r(Rs! A(1))=0 for r != 2
   and identifies H^2 with the constant rank-one module on the Kummer
   boundary. After shifting, this proves the first three conjuncts, including
   constructibility and Tor amplitude [0,0].
4. lem-pur-gysin-support-hom identifies support cohomology with Hom using
   lem-pur-supported-hom followed by s_* adjoint to Rs!. Its second clause
   identifies Hom with global H^0 sections. These are exactly the specified
   maps below. thm-pur-with-support-exactness supplies the support boundary;
   applying the first identification to the coordinate class gives m, whose
   H^0 section is its image under the composite identification. The open
   coefficient comparison is canonical pullback of the finite root line.
-/
theorem gysin_structure_statement (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.gysinValue h Y)) ∧
    (∀ q : ℤ, q ≠ 0 →
      IsZero ((_root_.DerivedCategory.homologyFunctor (ProSheaves P Y) q).obj
        (P.gysinValue h Y))) ∧
    (∃ H : EtSheaves P Y,
      Nonempty ((comparisonUpperStar (Modules P) Y).obj H ≅
        (_root_.DerivedCategory.homologyFunctor (ProSheaves P Y) 0).obj (P.gysinValue h Y)) ∧
      ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
        ∀ i : V.I₀, Nonempty
          ((Etale.upperStar (Modules P) (V.f i)).obj H ≅ P.constantEtale (V.X i))) ∧
    Function.Bijective (P.gysinHomToSections h Y) ∧
    Function.Bijective (P.gysinSupportToHom h Y a) ∧
    Function.Bijective (P.gysinSupportToSections h Y a) ∧
    ∃ b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
        (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true,
      b.hom = P.gysinOpenCoefficient h Y ∧
      ∀ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤,
        Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤ δ →
        ∃ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          P.gysinSupportToHom h Y a
              ((δ 1).app ⟨P.gysinInput h Y, trivial⟩
                (P.gysinCoordinateSupportSection h Y a b)) = m ∧
          P.gysinHomToSections h Y m = P.gysinSupportToSections h Y a
            ((δ 1).app ⟨P.gysinInput h Y, trivial⟩
              (P.gysinCoordinateSupportSection h Y a b)) := by
  letI : Y.Over (Spec (CommRingCat.of P.field.k)) := ⟨a⟩
  letI : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k)) := by
    change LocallyOfFiniteType a
    infer_instance
  letI : QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k)) := by
    change QuasiCompact a
    infer_instance
  letI : IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k)) := by
    change IsSeparated a
    infer_instance
  obtain ⟨first, δ, δet, _, hT, he⟩ :=
    gysin_localization_pushforward P h Y a
  let T := gysinTriangle P h Y first δ
  obtain ⟨hK, _, _⟩ := relative_kummer P h Y
  obtain ⟨⟨L, M, hB, eB, hC, eC₀, eC₁, hMor₂⟩⟩ :=
    gysin_triangle_extraction_hypotheses P h Y a first δ δet hT he hK
  letI : IsIso ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      T.mor₂) := hMor₂
  obtain ⟨hA, hMor₃, hShift, eShift⟩ := gysin_cohomology_extraction P Y a T L M hT
    hB eB hC eC₀ eC₁
  let d : GysinExtractionResult P Y T :=
    { M := M, hA := hA, hMor₃ := hMor₃, hShift := hShift, eShift := eShift }
  have hfinite := gysin_clause1_finiteTor P h Y a first δ hT d
  have hzero : ∀ q : ℤ, q ≠ 0 → IsZero
      ((_root_.DerivedCategory.homologyFunctor (ProSheaves P Y) q).obj
        (P.gysinValue h Y)) := by
    simpa [T, gysinTriangle, gysinValue] using d.hShift
  have hlocal := gysin_clause1_local_model P h Y a first δ hT d
  obtain ⟨hsup, hconcentrated⟩ := gysin_support_hom P h Y a
  have hhom : Function.Bijective (P.gysinHomToSections h Y) :=
    hconcentrated.2 hzero
  have hsections : Function.Bijective (P.gysinSupportToSections h Y a) := by
    change Function.Bijective (fun x ↦
      P.gysinHomToSections h Y (P.gysinSupportToHom h Y a x))
    exact hhom.comp hsup
  letI : IsIso (P.gysinOpenCoefficient h Y) :=
    gysin_open_coefficient_isIso P h Y a
  let b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
      (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true :=
    asIso (P.gysinOpenCoefficient h Y)
  refine ⟨hfinite, hzero, hlocal, hhom, hsup, hsections, b, rfl, ?_⟩
  · intro δ hδ
    let z := (δ 1).app ⟨P.gysinInput h Y, trivial⟩
        (P.gysinCoordinateSupportSection h Y a b)
    refine ⟨P.gysinSupportToHom h Y a z, rfl, ?_⟩
    rfl

end WeilConjectures.PurityFiniteSetting
