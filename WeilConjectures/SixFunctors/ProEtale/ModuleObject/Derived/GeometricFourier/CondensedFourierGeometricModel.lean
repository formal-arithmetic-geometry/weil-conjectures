/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.DualBundlePairing
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierPullback
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-! # Base linearity of the condensed Fourier--Deligne transform

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/prop-base-linear.md
and the adjacent prop-base-linear.proof.md (blueprint: prop-base-linear).

The natural isomorphism is in both variables on the actual bounded constructible
categories. The final equation uses the specified descent Frobenius on the transform
and the root-normalized signed Tate structures, including negative twists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier

open PurityTransport

variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- The base-change square, its composition law, and its Frobenius square.
Source: def-fd-transform.md, base change of the defining square
(blueprint: prop-base-linear).
Proof: the pullback projections define map. Pasting their defining Cartesian squares
cancels the common field-extension square. Functoriality gives composition. Naturality
of id times geometric Frobenius gives the last equality, checked on both projections. -/
theorem map_properties {X Y Z : Over (Spec (.of D.k₀))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (projection D X) (map D f) f.left (projection D Y) ∧
    map D (f ≫ g) = map D f ≫ map D g ∧
    (StrictWeilCondensed.modelFrobenius D X).hom ≫ map D f =
      map D f ≫ (StrictWeilCondensed.modelFrobenius D Y).hom := by
  let _ := Fintype.ofFinite D.k₀
  let B := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hpb : IsPullback (projection D X) (map D f) f.left (projection D Y) := by
    let e := pullback.congrHom f.w.symm rfl ≪≫
      (pullbackRightPullbackFstIso Y.hom B f.left).symm
    apply IsPullback.of_iso_pullback ⟨by simp [map, B]⟩ e
    · simp [e, B, -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase]
    · apply pullback.hom_ext <;> simp [e, map, B, -pullback.fst_comp_eq_toBase,
        -pullback.snd_comp_eq_toBase]
  refine ⟨hpb, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp [map]
  · exact WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian D X Y f |>.2.2.2.2.1

/-- The defining properties needed by the concrete base-changed compactification.
Source: def-fd-transform.md, compactification and geometric application
(blueprint: prop-base-linear).
Proof: the first clause is the image of c.comm under base change. The base-change
squares in map_properties transport properness and the open immersion from c.
The last clause is naturality of Frobenius for the open immersion; both horizontal
maps are isomorphisms, so its commuting square is Cartesian. -/
theorem compactification_properties {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    map D f = map D (openMap D c) ≫ map D (properMap D c) ∧
    IsProper (map D (properMap D c)) ∧ IsOpenImmersion (map D (openMap D c)) ∧
    IsPullback (StrictWeilCondensed.modelFrobenius D X).hom (map D (openMap D c))
      (map D (openMap D c)) (StrictWeilCondensed.modelFrobenius D (middle D c)).hom := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : f = openMap D c ≫ properMap D c :=
      Over.OverMorphism.ext c.comm
    exact (congrArg (map D) hc).trans
      (map_properties D (openMap D c) (properMap D c)).2.1
  · exact MorphismProperty.of_isPullback (P := @IsProper)
      (map_properties D (properMap D c) (𝟙 _)).1 c.isProper
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (map_properties D (openMap D c) (𝟙 _)).1 c.isOpenImmersion
  · exact IsPullback.of_horiz_isIso
      ⟨(map_properties D (openMap D c) (𝟙 _)).2.2⟩

/-- The actual Frobenius diagram on this compactification. No lift is supplied as a hypothesis.
Source: def-fd-transform.md and prop-base-linear.md, Weil clause
(blueprint: prop-base-linear). -/
def frobeniusSquare {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) :
    CompactificationReindexing.Square (compactification D c) (compactification D c)
      (StrictWeilCondensed.modelFrobenius D X).hom
      (StrictWeilCondensed.modelFrobenius D Y).hom where
  middle := (StrictWeilCondensed.modelFrobenius D (middle D c)).hom
  openSquare := (compactification_properties D c).2.2.2
  properSquare := ⟨(map_properties D (properMap D c) (𝟙 Y)).2.2⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Descent of an arithmetic module to the fibre under a map fixing its projection.
This generic construction keeps the module pullback comparison independent of the
size of the geometric Fourier square.
Source: def-fd-transform.md, arithmetic descent (blueprint: prop-base-linear). -/
def modelDescent {X Y : Scheme.{u}} (π : X ⟶ Y) (g : X ≅ X)
    (h : g.hom ≫ π = π)
    (A : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (StrictWeilCondensed.action Λ g).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ π).obj A)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ π).obj A) :=
  ((upperStar Λ g.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (((upperStarComp Λ g.hom π).app A).symm ≪≫
        eqToIso (congrArg (fun t ↦ (upperStar Λ t).obj A) h))

/-- The normalized descent datum on the geometric kernel, obtained by composition of
ordinary module pullbacks and the identity Frobenius followed by the model projection.
Source: def-fd-transform.md and prop-base-linear.md, Weil clause
(blueprint: prop-base-linear). -/
def kernelDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤)) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D (square D p p'))).obj
      (kernel D Λ p p' ψ b) ≅ kernel D Λ p p' ψ b := by
  letI := Fintype.ofFinite D.k₀
  exact modelDescent Λ (projection D (square D p p'))
    (StrictWeilCondensed.modelFrobenius D (square D p p'))
    (D.galoisMap_projections (square D p p').hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1
    (arithmeticKernel D Λ p p' ψ b)

/-- Pullback of a specified Weil structure, with the actual derived square comparison.
Source: prop-base-linear.proof.md, first and last paragraphs
(blueprint: prop-base-linear). -/
def pullDatum {X Y : Over (Spec (.of D.k₀))} (f : X ⟶ Y)
    (K : category D Λ Y)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj
      ((upperStar Λ (map D f)).leftDerivedFunctor.obj K) ≅
      (upperStar Λ (map D f)).leftDerivedFunctor.obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeilCondensed.modelFrobenius D X).hom).symm.app _ ≪≫
    (pullbackSquareComparison Λ
      (⟨(map_properties D f (𝟙 Y)).2.2⟩ :
        CommSq (StrictWeilCondensed.modelFrobenius D X).hom (map D f) (map D f)
          (StrictWeilCondensed.modelFrobenius D Y).hom)).symm.app K ≪≫
    (upperStar Λ (map D f)).leftDerivedFunctor.mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ
        (StrictWeilCondensed.modelFrobenius D Y).hom).app K ≪≫ φ)

/-- The compact-support Frobenius structure is the proper/open exchange on the actual
base-changed arithmetic compactification, followed by the direct image of the input datum.
Source: prop-base-linear.proof.md, final paragraph (blueprint: prop-base-linear). -/
def pushDatum {X Y : Over (Spec (.of D.k₀))} {f : X ⟶ Y}
    (c : Compactification f.left) (K : category D Λ X)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D X)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D Y)).obj
      ((rightDerivedLowerShriekOfCompactification Λ (compactification D c)).obj K) ≅
      (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).obj K := by
  let s := frobeniusSquare D c
  letI : IsIso s.middle := inferInstanceAs
    (IsIso (StrictWeilCondensed.modelFrobenius D (middle D c)).hom)
  let sq : CommSq (StrictWeilCondensed.modelFrobenius D X).hom (map D f) (map D f)
      (StrictWeilCondensed.modelFrobenius D Y).hom := ⟨(map_properties D f (𝟙 Y)).2.2⟩
  letI := (CompactificationReindexing.square_isIso Λ s sq).2
  exact (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (StrictWeilCondensed.modelFrobenius D Y).hom).symm.app _ ≪≫
    (asIso (CompactificationReindexing.squareExchange Λ s)).app K ≪≫
    (rightDerivedLowerShriekOfCompactification Λ (compactification D c)).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ
        (StrictWeilCondensed.modelFrobenius D X).hom).app K ≪≫ φ)

/-- Frobenius on the Fourier transform: monoidal pullback, arithmetic-kernel descent,
proper/open compact exchange and the exact shift comparison, in that order.
Source: prop-base-linear.md, Weil clause and its final proof paragraph
(blueprint: prop-base-linear).
Blueprint: (blueprint: def-fd-geometric-fourier-model).-/
def transformDatum {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ Λ))
    (b : Γ(pullback p.left p'.left, ⊤))
    (c : Compactification (pullback.snd p.left p'.left)) (r : ℤ)
    (K : category D Λ V)
    (φ : (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V)).obj K ≅ K) :
    (StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V')).obj
      ((transform D Λ p p' ψ b c r).obj K) ≅ (transform D Λ p p' ψ b c r).obj K :=
  ((StrictWeilCondensed.action Λ (StrictWeilCondensed.modelFrobenius D V')).commShiftIso r).app _ ≪≫
    (shiftFunctor _ r).mapIso
      (pushDatum D Λ (f := snd D p p') c _
        (StrictWeilCondensed.tensorDatum Λ (StrictWeilCondensed.modelFrobenius D (square D p p'))
          (pullDatum D Λ (fst D p p') K φ) (kernelDatum D Λ p p' ψ b)))

/-- The existing signed Tate-twist functor with actual condensed E coefficients.
Source: prop-base-linear.md, clause (2); sk-def-sp-tate-twist
(blueprint: prop-base-linear). -/
def twist (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (X : Over (Spec (.of D.k₀))) (m : ℤ) :
    category D (Coefficient.rational E |>.obj ell) X ⥤
      category D (Coefficient.rational E |>.obj ell) X :=
  tensorRight (StrictWeilCondensed.derivedTateLine ell (.rational E) (fiber D X) m)

/-- Pullback followed by tensoring with a locally free module preserves ordinary
bounded constructibility on a constant-model bounded constructible input.
Work with a generic coefficient ring so that the predicate and tensor conversions
are checked independently of the concrete condensed E model.
Proof: use the adic predicate comparison on the input, then preservation under pullback,
and apply tensor stability to the constructible single complex of the locally free module.
Source: adicConstructibilityPredicateComparison, the scheme pullback preservation lemma,
and BoundedConstructibleTensorObj.boundedConstructible_tensorObj (blueprint: prop-base-linear). -/
private theorem pullback_tensorRight_single_mem
    (ell : ℕ) [Fact ell.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X Y : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (hadic : IsEllAdicCoefficient ell R inferInstance) (hR : LisseTensorHypotheses R)
    (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (hM : IsLocallyFree (condensedRingObj R X) M)
    (K : ConstantModelBoundedConstructible R Y) :
    boundedConstructible (condensedRingObj R X)
      (((upperStar R f).leftDerivedFunctor ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj M)).obj K.obj) := by
  have hK : boundedConstructible (condensedRingObj R Y) K.obj := by
    rw [(adicConstructibilityPredicateComparison ell Y R hadic).2]
    exact K.property
  exact boundedConstructible_tensorObj hR
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme R f K.obj hK)
    (boundedConstructible_singleFunctor_zero_obj R M hM.isConstructibleModuleObject)

/-- Specialize pullback–tensor stability to the named arithmetic Fourier kernel.
Keeping this specialization generic avoids unfolding the concrete E-valued kernel.
Proof: apply pullback–tensor stability to the geometric pullback of the arithmetic kernel.
Source: the preceding stability lemma and the definition of kernel
(blueprint: prop-base-linear). -/
private theorem kernel_tensor_mem
    (ell : ℕ) [Fact ell.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {S V V' : Over (Spec (.of D.k₀))}
    (p : V ⟶ S) (p' : V' ⟶ S) (ψ : AddChar D.k₀ (MonObj.Γ R))
    (b : Γ(pullback p.left p'.left, ⊤))
    [TopologicalSpace.NoetherianSpace (fiber D (square D p p'))]
    [IsLocallyNoetherian (fiber D V)] [CompactSpace (fiber D V)]
    (hadic : IsEllAdicCoefficient ell R inferInstance) (hR : LisseTensorHypotheses R)
    (hM : IsLocallyFree (condensedRingObj R (fiber D (square D p p')))
      ((upperStar R (projection D (square D p p'))).obj (arithmeticKernel D R p p' ψ b)))
    (K : ConstantModelBoundedConstructible R (fiber D V)) :
    boundedConstructible (condensedRingObj R (fiber D (square D p p')))
      ((((upperStar R (map D (fst D p p'))).leftDerivedFunctor) ⋙
        tensorRight (kernel D R p p' ψ b)).obj K.obj) :=
  pullback_tensorRight_single_mem ell R (fiber D (square D p p')) (fiber D V)
    hadic hR (map D (fst D p p')) _ hM K

/-- Kernel tensor stability for the exact rational coefficient presentation used here.
Proof: apply the generic kernel stability lemma, using the continuous-field adic
predicate comparison and continuous-field tensor hypotheses.
Source: kernel_tensor_mem and tensorHypotheses_continuousMapRingObj
(blueprint: prop-base-linear). -/
private theorem rational_kernel_tensor_mem
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    {S V V' : Over (Spec (.of D.k₀))} (p : V ⟶ S) (p' : V' ⟶ S)
    (ψ : AddChar D.k₀ (MonObj.Γ ((Coefficient.rational E).obj ell)))
    (b : Γ(pullback p.left p'.left, ⊤))
    [TopologicalSpace.NoetherianSpace (fiber D (square D p p'))]
    [IsLocallyNoetherian (fiber D V)] [CompactSpace (fiber D V)]
    (hM : IsLocallyFree
      (condensedRingObj ((Coefficient.rational E).obj ell) (fiber D (square D p p')))
      ((upperStar ((Coefficient.rational E).obj ell) (projection D (square D p p'))).obj
        (arithmeticKernel D ((Coefficient.rational E).obj ell) p p' ψ b)))
    (K : ConstantModelBoundedConstructible ((Coefficient.rational E).obj ell) (fiber D V)) :
    boundedConstructible
      (condensedRingObj ((Coefficient.rational E).obj ell) (fiber D (square D p p')))
      ((((upperStar ((Coefficient.rational E).obj ell)
          (map D (fst D p p'))).leftDerivedFunctor) ⋙
        tensorRight (kernel D ((Coefficient.rational E).obj ell) p p' ψ b)).obj K.obj) := by
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  exact kernel_tensor_mem D ell ((Coefficient.rational E).obj ell) p p' ψ b
    (.continuous E) (tensorHypotheses_continuousMapRingObj ell E).lisseTensorHypotheses hM K

/-- The exact-to-derived pullback comparison on a module in degree zero.
This is the existing map-derived/single comparison, with the coefficient ring generic.
Source: leftDerivedUpperStarIsoMapDerivedCategory and mapDerivedCategorySingleFunctor. -/
private def upperStar_single_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :
    (upperStar R f).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((upperStar R f).obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory R f).app _ ≪≫
    ((upperStar R f).mapDerivedCategorySingleFunctor 0).app M

/-- Evaluate the existing monoidal pullback comparison at its right tensor factor.
The generic coefficient parameter keeps this elementary functor conversion small.
Source: leftDerivedUpperStarTensorIso. -/
private def upperStar_tensorRight_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y))) :
    tensorRight M ⋙ (upperStar R f).leftDerivedFunctor ≅
      (upperStar R f).leftDerivedFunctor ⋙
        tensorRight ((upperStar R f).leftDerivedFunctor.obj M) :=
  Functor.isoWhiskerRight (leftDerivedUpperStarTensorIso R f) ((evaluation _ _).obj M)

set_option Elab.async false in
set_option maxHeartbeats 400000 in -- Kernel checking the natural functor comparisons.
end AlgebraicGeometry.ProEtale.CondensedRing.GeometricFourier
