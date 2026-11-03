/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RealSheaves.CohomologyEuler.RealSheavesCohomologyEulerSeries
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.AlgebraicGeometry.GroupScheme.RealSheaves.CohomologyEuler.CurveSheafEulerIdentity
import WeilConjectures.AlgebraicGeometry.GroupScheme.MiddleImageCompactZero

/-!
# Euler product for a condensed middle extension

Source: latest blueprint, in directory
`part-weights-riemann-hypothesis/sec-purity-real-sheaves/`, files
`sec-weights-at-the-boundary-points/sk-p-real-semi/lem-wf-euler-product-middle-extension.md`
and its `.proof.md`, order 4117
(blueprint: lem-wf-euler-product-middle-extension).
The helpers specialize the recorded condensed definitions; no coefficient model changes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hEll : l ≠ D.p)
  {U₀ X₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [SmoothOfRelativeDimension 1 X₀.hom]
  (j : U₀ ⟶ X₀) [IsOpenImmersion j.left] [IsDominant j.left]
  (F : NativeL2.WeilModule D l U₀)
  (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)

/-- The actual ordinary condensed middle image placed in degree zero, with the induced
strict Weil structure. Constructibility is the recorded middle-image theorem; a constant
finite local presentation is in particular a locally finite presentation on each stratum.
Source: latest blueprint, def-wf-middle-extension, degree-zero identification, and
lem-wf-euler-product-middle-extension.proof.md, first paragraph
(blueprint: lem-wf-euler-product-middle-extension). -/
def nativeMiddleComplex : RealSheaves.CohomologyEuler.Complex D l X₀ := by
  classical
  have : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : CompactSpace (D.geometricFiber X₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  have : QuasiSeparatedSpace (D.geometricFiber X₀).left :=
    quasiSeparatedSpace_of_quasiSeparated (D.geometricFiber X₀).hom
  let M := NativeL2.middleWeilImage D l j F
  have hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left)
      M.carrier := by
    have h := NativeL2.middleImage_constructible D l j hEll F.carrier hF
    change IsConstructibleModuleObject _
      (NativeL2.middleWeilImage D l j F).carrier
    unfold NativeL2.middleWeilImage
    change IsConstructibleModuleObject _ ((NativeL2.middleImage D l j).obj F.carrier)
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at h
    obtain ⟨S, hS⟩ := h
    refine ⟨S, fun a ↦ ?_⟩
    exact (CondensedRing.isLocallyFinitelyPresented_mapMod_iff
      (Profinite.padicAlgClRingObj l) (S.immersion a) _).mpr
      (HasFiniteConstantLocalModel.isLocallyFinitelyPresented
        (Profinite.padicAlgClRingObj l) _ (hS a))
  exact ⟨IsoAlgebra.mk ((DerivedCategory.singleFunctor _ 0).obj M.carrier)
    (((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).mapDerivedCategorySingleFunctor 0).app M.carrier ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso M.str),
    (condensedWeilSingle l (D.geometricFrobenius X₀).hom ⟨M, hM⟩).property⟩

/-- The recorded coefficientwise Euler series of the middle image. The closed points are
those of the finite-field model. The compatible embeddings merely choose geometric lifts;
localSeries_independent makes their choices immaterial.
Source: latest blueprint, d-real-cohom, Euler-series display, specialized in the first
paragraph of lem-wf-euler-product-middle-extension.proof.md
(blueprint: lem-wf-euler-product-middle-extension). -/
def nativeMiddleEulerSeries (ι : PadicAlgCl l →+* ℂ)
    (i : ∀ x : closedPoints X₀.left, X₀.left.residueField x.val →+* D.k)
    (hi : ∀ x, (i x).comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    PowerSeries ℂ :=
  RealSheaves.CohomologyEuler.eulerSeries D l X₀
    (nativeMiddleComplex D l hEll j F hF) ι i hi

/-- The reverse characteristic polynomial of the canonical compact-support Frobenius,
coefficientwise transported through iota. The compactification presents the existing
compact-support functor; any compactification of the geometric structure map is allowed.
Source: latest blueprint, d-real-cohom, cohomology and Frobenius paragraph, and the two
right-hand factors of lem-wf-euler-product-middle-extension.md
(blueprint: lem-wf-euler-product-middle-extension). -/
def nativeMiddleCompactFactor (c : Compactification (D.geometricFiber X₀).hom)
    (ι : PadicAlgCl l →+* ℂ) (r : ℤ) : PowerSeries ℂ :=
  let K := nativeMiddleComplex D l hEll j F hF
  letI := (RealSheaves.CohomologyEuler.cohomology_finite D l X₀ hEll c K).1 true r
  let A := RealSheaves.CohomologyEuler.frobeniusOnCohomology D l X₀ hEll c K true r
  (((LinearMap.charpolyRev A.hom).map
    (ι.comp (ULift.ringEquiv : ULift.{u + 1} (PadicAlgCl l) ≃+* PadicAlgCl l).toRingHom) :
      Polynomial ℂ) : PowerSeries ℂ)

private theorem nativeMiddleComplex_concentrated (r : ℤ) (hr : r ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      (nativeMiddleComplex D l hEll j F hF).obj.carrier) := by
  change IsZero ((DerivedCategory.homologyFunctor _ r).obj
    ((DerivedCategory.singleFunctor _ 0).obj (NativeL2.middleWeilImage D l j F).carrier))
  rcases lt_or_gt_of_ne hr with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 r h
  · exact DerivedCategory.isZero_of_isLE _ 0 r h

private theorem nativeMiddleCompactFactor_eq_one_of_isZero
    (c : Compactification (D.geometricFiber X₀).hom)
    (ι : PadicAlgCl l →+* ℂ) (r : ℤ)
    (h : IsZero (RealSheaves.CohomologyEuler.cohomology D l X₀ c true
      (nativeMiddleComplex D l hEll j F hF) r)) :
    nativeMiddleCompactFactor D l hEll j F hF c ι r = 1 := by
  classical
  let := ModuleCat.isZero_iff_subsingleton.mp h
  dsimp [nativeMiddleCompactFactor]
  rw [LinearMap.charpolyRev_of_subsingleton, Polynomial.map_one, Polynomial.coe_one]

/-- The Euler series of the lisse condensed Weil module's ordinary middle extension,
multiplied by its degree-two compact-support factor, is its degree-one factor.

Proof, following the two paragraphs of the blueprint proof:
1. Apply the uniform Euler-product trace formula to j_*F placed in degree zero in Dbc.
   Its local factors are the middle-image stalk determinants. Compact support on the
   curve has only degrees zero, one and two, giving L P0 P2 = P1.
2. Choose a smooth proper compactification k : X -> Xbar. The canonical map
   k_!j_*F -> (kj)_*F is injective: its stalks are identities on X and have zero source
   on the boundary. Its kernel is constructible by coefficientHeartGeneralStatement;
   exact geometric-point evaluation and the lisse filtration show that this kernel is
   zero. A compactly supported section thus gives a generic invariant vector. Its germ
   at a boundary point is that same vector in the inertia invariants. Affineness makes
   the boundary nonempty, so the zero boundary germ kills the vector. Hence Hc0 = 0,
   its determinant is one, and the claimed identity follows.

Source place: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-purity-real-sheaves/sec-weights-at-the-boundary-points/sk-p-real-semi/
  lem-wf-euler-product-middle-extension.proof.md, both paragraphs
(blueprint: lem-wf-euler-product-middle-extension). -/
theorem lSeries_middleExtension_eq_ratio
    [GeometricallyConnected X₀.hom] [IsAffine X₀.left]
    (c : Compactification (D.geometricFiber X₀).hom)
    (ι : PadicAlgCl l →+* ℂ)
    (i : ∀ x : closedPoints X₀.left, X₀.left.residueField x.val →+* D.k)
    (hi : ∀ x, (i x).comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    nativeMiddleEulerSeries D l hEll j F hF ι i hi *
        nativeMiddleCompactFactor D l hEll j F hF c ι 2 =
      nativeMiddleCompactFactor D l hEll j F hF c ι 1 := by
  have hEuler := RealSheaves.CohomologyEuler.curve_sheaf_euler_identity
    D l X₀ hEll c (nativeMiddleComplex D l hEll j F hF)
    (nativeMiddleComplex_concentrated D l hEll j F hF) ι i hi
  change nativeMiddleEulerSeries D l hEll j F hF ι i hi *
      nativeMiddleCompactFactor D l hEll j F hF c ι 0 *
      nativeMiddleCompactFactor D l hEll j F hF c ι 2 =
    nativeMiddleCompactFactor D l hEll j F hF c ι 1 at hEuler
  have hzero : IsZero (RealSheaves.CohomologyEuler.cohomology D l X₀ c true
      (nativeMiddleComplex D l hEll j F hF) 0) := by
    have hz := isZero_middleImage_compact_zero D l hEll j F.carrier hF c
    apply RealSheaves.CohomologyEuler.cohomology_isZero
    change IsZero ((CondensedRing.condensedRingCompactCohomology
      (Profinite.padicAlgClRingObj l) c 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (NativeL2.middleWeilImage D l j F).carrier))
    unfold NativeL2.middleWeilImage
    exact hz
  rw [nativeMiddleCompactFactor_eq_one_of_isZero D l hEll j F hF c ι 0 hzero,
    mul_one] at hEuler
  exact hEuler

end WeilConjectures
