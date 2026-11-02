/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.ConstituentNonexceptional
public import WeilConjectures.AlgebraicGeometry.CondensedFourierPerverse.CondensedFourierPerverse
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurveSimpleObjects
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform

/-!
# Fourier transform of a middle extension

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-middle/_section.md
and part-weights-riemann-hypothesis/sec-fourier-transform/
sec-fourier-transforms-of-middle-extensions/sk-p-dl-a1-middle/
(blueprint: sk-p-dl-a1-middle).

All sheaves below use actual condensed modules over the pulled-back
`Profinite.padicAlgClRingObj`; no legacy adic `WeilSheaf` interface is used.  The
ordinary direct image is `NativeL2.middleImage`, its degree-one placement is the
usual single complex and shift, and the Fourier operation is the geometric
`CondensedFourierPerverse.transform`, built from `ProEtale.condensedFourierTransform`.
The proof is postponed at this stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedAffineLine

variable (D : WeilConjectures.FiniteFieldDatum.{u})
variable (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)

/-- The condensed coefficient ring `Q̄_ℓ` of the conventions.
Source: `sk-p-dl-a1-middle/_section.md`, statement (coefficients of `rem-dl-a1-conventions`)
(blueprint: sk-p-dl-a1-middle). -/
abbrev Λ := Profinite.padicAlgClRingObj ell

/-- The affine line `A¹_{k₀}` over the finite field (also used as the dual line).
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
abbrev A₀ := CondensedFourierPerverse.lineModel D

/-- The geometric affine line `A = A₀ ⊗ k`.
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
abbrev A := CondensedFourierPerverse.line D

/-- An open of `P¹_{k₀}` as a `k₀`-model, the canonical `openModel` of the conventions.
Source: `sk-p-dl-a1-middle/_section.md`, statement; `rem-dl-a1-conventions`, standard chart
(blueprint: sk-p-dl-a1-middle). -/
abbrev UModel (U₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens) :=
  CondensedLisseExtensionInertia.openModel D U₀

/-- A dense open `j : U₀ ↪ A¹_{k₀} ⊂ P¹_{k₀}` together with a lisse Weil sheaf on it.
The open is given inside `P¹_{k₀}`, contained in the standard affine chart; `chart` says that
`j₀` is the restriction of the standard chart `A¹ ↪ P¹`, so that the point at infinity of the
unramifiedness predicate is the infinity of the same affine coordinate.
Source: `sk-p-dl-a1-middle/_section.md`, statement (`j`, `M`); `rem-dl-a1-conventions`
(blueprint: sk-p-dl-a1-middle). -/
structure Datum where
  U₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens
  [finiteU : LocallyOfFiniteType (UModel D U₀).hom]
  [quasiCompactU : QuasiCompact (UModel D U₀).hom]
  hU : U₀ ≤ (ProjectiveLine.affineChart (Spec (.of D.k₀))).opensRange
  hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀))))
  j₀ : UModel D U₀ ⟶ A₀ D
  chart : j₀.left ≫ ProjectiveLine.affineChart (Spec (.of D.k₀)) = U₀.ι
  [openImmersion : IsOpenImmersion j₀.left]
  [dominant : IsDominant j₀.left]
  dense : DenseRange j₀.left
  F : AffineLineConventions.WeilSheaf D ell (UModel D U₀)
  hF : AffineLineConventions.IsLisse F

attribute [instance] Datum.finiteU Datum.quasiCompactU Datum.openImmersion Datum.dominant

/-- The category of lisse Weil sheaves on `U₀`; simplicity here is irreducibility in the
sense of `rem-dl-a1-conventions`.
Source: `sk-p-dl-a1-middle/_section.md`, statement; `rem-dl-a1-conventions`, irreducible lisse
(blueprint: sk-p-dl-a1-middle). -/
abbrev LisseCategory (X : Datum D ell) :=
  ObjectProperty.FullSubcategory
    (fun N : WeilConjectures.NativeL2.WeilModule D ell (UModel D X.U₀) ↦
    IsLisseCoefficientModule (Λ ell) N.carrier)

/-- The sheaf of a datum as an object of the lisse Weil category.
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
def lisseObject (X : Datum D ell) : LisseCategory D ell X :=
  ⟨X.F.obj, X.hF⟩

/-- The geometric open immersion `U ↪ A` obtained from `j₀` by base change to `k`.
Source: `sk-p-dl-a1-middle/_section.md`, statement (restriction to `U'₀`)
(blueprint: sk-p-dl-a1-middle). -/
abbrev geomMap (X : Datum D ell) :
    (D.geometricFiber (UModel D X.U₀)).left ⟶ A D :=
  ((CondensedFourierPerverse.geometric D).map X.j₀).left

/-- The ordinary condensed middle extension `(j_*M)[1]` with its Weil structure, using the
recorded lower-star operation (`def-wf-middle-extension`).
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
noncomputable def middleExtension (X : Datum D ell) :
    Endofunctor.IsoAlgebra (CondensedFourierPerverse.action D ell) := by
  let carrier := (WeilConjectures.NativeL2.shiftedMiddleImage D ell X.j₀).obj X.F.obj.carrier
  let W := (CondensedCurvePerverse.weilPlaced (Profinite.padicAlgClRingObj ell)
    (D.geometricFrobenius (A₀ D)) (1 : ℤ)).obj
      (WeilConjectures.NativeL2.middleWeilImage D ell X.j₀ X.F.obj)
  have _ : carrier = W.carrier := by
    dsimp [carrier, W, CondensedCurvePerverse.weilPlaced]
    unfold WeilConjectures.NativeL2.middleWeilImage
    rfl
  exact W

/-- Geometric constancy, the recorded predicate of `rem-dl-a1-conventions`.
Source: `sk-p-dl-a1-middle/_section.md`, final assertion (blueprint: sk-p-dl-a1-middle). -/
abbrev IsGeometricallyConstant (X : Datum D ell) : Prop :=
  AffineLineConventions.IsGeometricallyConstant X.F

/-- Weil objects of the derived category of the geometric affine line.
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
abbrev WeilDerived := Endofunctor.IsoAlgebra (CondensedFourierPerverse.action D ell)

/-- The Fourier image equipped with the canonical Frobenius comparison from the perverse
transform module.  The structure map is the prescribed comparison followed by the original
Weil structure.
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
noncomputable def fourierWeilObject (ψ : AddChar D.k₀ (MonObj.Γ (Λ ell)))
    (c : Compactification (CondensedFourierPerverse.secondModel D).left)
    (K : WeilDerived D ell) : WeilDerived D ell :=
  Endofunctor.IsoAlgebra.mk
    ((CondensedFourierPerverse.transform D ell ψ c).obj K.carrier)
    ((CondensedFourierPerverse.frobeniusComponent D ell ψ c K.carrier) ≪≫
      (CondensedFourierPerverse.transform D ell ψ c).mapIso K.str)

/-- The Fourier partner relation, including the `H⁻¹` restriction identification.
Source: `sk-p-dl-a1-middle/_section.md`, statement (blueprint: sk-p-dl-a1-middle). -/
def IsFourierPartner (ψ : AddChar D.k₀ (MonObj.Γ (Λ ell)))
    (X Y : Datum D ell) : Prop :=
  ∃ c : Compactification (CondensedFourierPerverse.secondModel D).left,
    Nonempty (fourierWeilObject D ell ψ c (middleExtension D ell X) ≅
      middleExtension D ell Y) ∧
    ∃ K : Endofunctor.IsoAlgebra
        ((CondensedRing.upperStar (Λ ell)
          (D.geometricFrobenius (UModel D Y.U₀)).hom).mapDerivedCategory),
      Nonempty (K ≅
        (CondensedCurvePerverse.weilPlaced (Profinite.padicAlgClRingObj ell)
          (D.geometricFrobenius (UModel D Y.U₀)) 0).obj Y.F.obj) ∧
      Nonempty (K.carrier ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.upperStar (Λ ell) (geomMap D ell Y)).obj
            ((DerivedCategory.homologyFunctor _ (-1 : ℤ)).obj
              (fourierWeilObject D ell ψ c (middleExtension D ell X)).carrier)))

end AlgebraicGeometry.ProEtale.CondensedAffineLine
