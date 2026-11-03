/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierPerverse.CondensedFourierPerverse
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedRealified.CondensedRealifiedKernel
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedOpenClosedLocalizationMapsCore
public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.ConstituentNonexceptional
public import WeilConjectures.AlgebraicGeometry.CondensedFourierPerverse.ZeroExtensionComparisonBounds
public import WeilConjectures.AlgebraicGeometry.CondensedFourierPerverse.ZeroExtensionComparisonStructural

/-!
# Zero-extension comparison for the condensed Fourier--Deligne transform

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/`
`sk-p-dl-a1-correction/prop-fd-zero-extension-comparison.md`, statement and Steps 1--5
of the `.proof.md` (blueprint: prop-fd-zero-extension-comparison).

The statement uses the condensed coefficient model.  The correction structure records the
short exact sequence on Weil modules and the three Fourier comparison isomorphisms;
its first term is the lisse, punctual-weight correction on the full dual affine line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedFourierPerverse

open CondensedCurvePerverse
open AffineLineConventions
open CondensedGenericWeil
open WeilConjectures
open WeilConjectures.NativeL2
open WeilConjectures.CondensedRealified
open WeilConjectures.CondensedWeil

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime]

/-- A degree-one shift of a condensed module on the geometric affine line.
Source: the `[1]` in the zero-extension comparison
(blueprint: `prop-fd-zero-extension-comparison`). -/
abbrev shiftedSingle (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime]
    (N : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj l) (line D)) :=
  (shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj N)

/-- The pointwise closed-operator eigenvalue bound at most weight `w`.
Source: the weight clause of `prop-fd-zero-extension-comparison`. -/
def HasClosedOperatorWeightsAtMost
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {X₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D l X₀) (ι : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l)),
    Module.End.HasEigenvalue (NativeL2.closedOperator D l X₀ M x i hi).hom α →
      ‖ι α.down‖ ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)

/-- Derived condensed Weil objects on the geometric affine line, with their invertible
Frobenius structure map: the Weil category in which the three Fourier comparisons of the
statement are formed.
Source: `prop-fd-zero-extension-comparison.md`, the displayed isomorphisms and Step 5
("the transform and the triangles are formed in the Weil category")
(blueprint: prop-fd-zero-extension-comparison). -/
abbrev condensedWeilDerived
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] :=
  Endofunctor.IsoAlgebra (action D l)

/-- The canonical degree-zero Weil single of a condensed Weil module, used for the
unshifted boundary sheaf `B` in `FT_ψ(B) ≅ B'[1]`.
Source: `prop-fd-zero-extension-comparison.md`, second displayed isomorphism
(blueprint: prop-fd-zero-extension-comparison). -/
def weilSingle
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (N : NativeL2.WeilModule D l (lineModel D)) : condensedWeilDerived D l :=
  Endofunctor.IsoAlgebra.mk (DerivedCategory.singleFunctor _ 0 |>.obj N.carrier)
    (CondensedFourierPerverse.singleDescent
      (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (lineModel D))
      N.carrier N.str)

/-- The canonical degree-one shifted single of a condensed Weil module, used for
`j_!M[1]`, `G[1]`, `B'[1]` and `(j'_*M')[1]`.
Source: `prop-fd-zero-extension-comparison.md`, the `[1]` shifts of the displayed
isomorphisms (blueprint: prop-fd-zero-extension-comparison). -/
def shiftedWeilSingle
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (N : NativeL2.WeilModule D l (lineModel D)) : condensedWeilDerived D l :=
  Endofunctor.IsoAlgebra.mk (shiftedSingle D l N.carrier)
    (((action D l).commShiftIso (1 : ℤ)).app _ ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso
        (CondensedFourierPerverse.singleDescent
          (Profinite.padicAlgClRingObj l) (D.geometricFrobenius (lineModel D))
          N.carrier N.str))

/-- The condensed correction package for the zero-extension comparison.  Its open extension
and boundary are actual Weil-module constructions, so all subsequent cokernels and comparison
isomorphisms retain the canonical Frobenius data.
Source: `prop-fd-zero-extension-comparison.md`, the definition `B := j_*M/j_!M` and the three
displayed relations (Step 1 and Step 5 of the proof)
(blueprint: prop-fd-zero-extension-comparison). -/
structure CondensedFourierCorrection
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {U₀ U₁ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType U₁.hom] [QuasiCompact U₁.hom]
    (j₀ : U₀ ⟶ lineModel D) (j₁ : U₁ ⟶ lineModel D)
    (M : Lisse l (D.geometricFrobenius U₀))
    (M' : Lisse l (D.geometricFrobenius U₁))
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l)))
    (c : Compactification (secondModel D).left)
    [IsOpenImmersion j₀.left] [IsOpenImmersion j₁.left]
    [IsDominant j₀.left] [IsDominant j₁.left] where
  /-- Frobenius base-change comparison for the open extension by zero. -/
  openComparison :
    (CondensedWeil.openModuleExtension D l j₀) ⋙
          CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (D.geometricFrobenius (lineModel D)).hom ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (D.geometricFrobenius U₀).hom ⋙
        CondensedWeil.openModuleExtension D l j₀
  /-- The comparison is the mate of the inverse Frobenius square comparison. -/
  openComparison_canonical :
    openComparison.inv = ((mateEquiv
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj l) (NativeL2.geometricMap D j₀))
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj l) (NativeL2.geometricMap D j₀))).symm
      (.mk _ _ _ _ (CondensedRing.upperStarSquareComparison
        (Profinite.padicAlgClRingObj l) (NativeL2.frobeniusSquare D j₀)).inv)).natTrans
  /-- The canonical Weil-module map from the open extension to the middle image. -/
  boundaryMap :
    (CondensedWeil.openWeilExtension D l j₀ openComparison).obj M.obj ⟶
      NativeL2.middleWeilImage D l j₀ M.obj
  /-- Its underlying abelian-sheaf map is exactly the canonical open-immersion map. -/
  boundaryMap_canonical :
    HEq
      (boundaryMap.hom.f.hom)
      ((ProEtale.openImmersionLowerShriekToLowerStar Ab.{u + 1}
        (NativeL2.geometricMap D j₀)).app
        ((Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l)
          (D.geometricFiber U₀).left)).obj M.obj.carrier))
  /-- The Weil-equivariant short exact sequence `0 → B' → G → j'_* M' → 0`. -/
  seq : ShortComplex (NativeL2.WeilModule D l (lineModel D))
  shortExact : seq.ShortExact
  /-- The transform of `j_! M [1]` is the middle term, shifted by one, in the Weil category. -/
  isoExtension :
    Endofunctor.IsoAlgebra.mk
        ((transform D l ψ c).obj
          (shiftedSingle D l
            ((CondensedWeil.openWeilExtension D l j₀ openComparison).obj M.obj).carrier))
        (frobeniusComponent D l ψ c _ ≪≫
          (transform D l ψ c).mapIso
            (shiftedWeilSingle D l
              ((CondensedWeil.openWeilExtension D l j₀ openComparison).obj M.obj)).str) ≅
      shiftedWeilSingle D l seq.X₂
  /-- The transform of the degree-zero boundary is the correction shifted by one,
  in the Weil category. -/
  isoBoundary :
    Endofunctor.IsoAlgebra.mk
        ((transform D l ψ c).obj
          ((DerivedCategory.singleFunctor _ 0).obj (cokernel boundaryMap).carrier))
        (frobeniusComponent D l ψ c _ ≪≫
          (transform D l ψ c).mapIso
            (weilSingle D l (cokernel boundaryMap)).str) ≅
      shiftedWeilSingle D l seq.X₁
  /-- The third term is the middle extension `j'_* M'`, as a Weil-module isomorphism. -/
  isoMiddle : seq.X₃ ≅
    (NativeL2.middleWeilImage D l j₁ M'.obj)

/-- The zero-extension comparison on the condensed affine-line model.

The hypotheses are a nontrivial additive character; dense open immersions `j` and `j'`;
a nonzero simple lisse condensed Weil module `M`; condensed constituent-nonexceptionality;
punctual `ι`-purity of weight `w`; and the Fourier-partner comparison for the middle images.
The conclusion supplies the short exact sequence, the degree-zero boundary transform and shifted
extension isomorphisms, the middle-extension identification, lissity on the full dual line, and the
pointwise weight bound.  No geometric irreducibility or unramifiedness-at-infinity hypothesis
is added.  The proof follows the five source steps: (1) the open--closed sequence, (2) the
finite-etale Fourier boundary calculation, (3) lissity, (4) the closed-operator weight bound,
and (5) the heart short-exact sequence and truncation.  The functor `transform` is the
condensed realization of the defining Fourier--Deligne transform: it is the prescribed
pullback--kernel tensor--compactified lower-shriek composite, followed by the degree-one shift,
and its Weil structure is `frobeniusComponent`; this is the condensed counterpart of the
`def-fd-transform` record.  Source: `literature/blueprint/latest/blueprint/`
`part-weights-riemann-hypothesis/sec-deligne-laumon-a1/`
`sec-purity-of-the-lisse-part-of-the-fourier-transform/sk-p-dl-a1-correction/`
`prop-fd-zero-extension-comparison.md` and `.proof.md`, Steps 1--5.
(blueprint: prop-fd-zero-extension-comparison)
-/
theorem zeroExtensionComparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hℓ : l ≠ D.p)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) (hψ : ψ ≠ 1)
    {U₀ U₁ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType U₁.hom] [QuasiCompact U₁.hom]
    (j₀ : U₀ ⟶ lineModel D) (j₁ : U₁ ⟶ lineModel D)
    [IsOpenImmersion j₀.left] [IsOpenImmersion j₁.left]
    [IsOpenImmersion (NativeL2.geometricMap D j₀)]
    [IsDominant j₀.left] [IsDominant j₁.left]
    (M : Lisse l (D.geometricFrobenius U₀))
    (hM0 : ¬ IsZero M.obj.carrier)
    (hMsimple : Simple M)
    (hne : IsConstituentNonexceptional D U₀ l j₀ M ψ)
    (M' : Lisse l (D.geometricFrobenius U₁))
    (c : Compactification (secondModel D).left)
    (hFT : Nonempty (Endofunctor.IsoAlgebra.mk
          ((transform D l ψ c).obj
            (shiftedSingle D l
              (NativeL2.middleWeilImage D l j₀ M.obj).carrier))
          (frobeniusComponent D l ψ c _ ≪≫
            (transform D l ψ c).mapIso
              (shiftedWeilSingle D l (NativeL2.middleWeilImage D l j₀ M.obj)).str) ≅
        shiftedWeilSingle D l (NativeL2.middleWeilImage D l j₁ M'.obj)))
    (ι : PadicAlgCl l →+* ℂ) {w : ℝ}
    (hw : NativeL2.Pure D l U₀ M.obj ι w) :
    ∃ C : CondensedFourierCorrection D l j₀ j₁ M M' ψ c,
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) C.seq.X₁.carrier ∧
      HasClosedOperatorWeightsAtMost D l C.seq.X₁ ι w := by
  obtain ⟨C, hC⟩ := zeroExtensionComparison_structural D l hℓ ψ hψ j₀ j₁ M hM0
    hMsimple hne M' c hFT ι hw
  obtain ⟨hl, hwC⟩ := zeroExtensionComparison_bounds D l hℓ ψ hψ j₀ j₁ M hM0
    hMsimple hne M' c hFT ι hw C hC
  exact ⟨C, hl, hwC⟩

end AlgebraicGeometry.ProEtale.CondensedFourierPerverse
