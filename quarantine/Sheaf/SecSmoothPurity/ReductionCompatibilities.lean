/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.Paper.FiniteRingCompactSupportProjection

/-! # Units, composition and purity under finite coefficient change

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-compatibilities.md and its proof
(blueprint: det-sp-reduction-compatibilities).

The first two identities use the intrinsic constant-ring Dctf adjunctions. The third
uses the equivalent fixed-coefficient presentation of the general-ring purity node,
including its actual diagonal/Rees/integration normalization. No flatness is assumed.

## Main statements

* `reductionCompatibilities_unit`: coefficient change preserves the adjunction unit.
* `reductionCompatibilities_composition`: the exceptional comparisons satisfy the cocycle.
* `reductionCompatibilities_purity`: coefficient change preserves normalized smooth purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Coefficient change preserves the unit of the constructible compact-support adjunction.
The equation `hc` specifies exactly the counit-characterized comparison of the dependency;
it is written without an inverse by multiplying by the canonical support comparison.
Source: sk-lem-sp-reduction-compatibilities, clause (1)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Steps 1--2): Scalar extension preserves Dctf and its canonical tensor and
pullback identifications. Transpose the displayed composite under the B-adjunction.
Naturality of the B-counit and hc identify its transpose with b_M, then the extended
A-counit, inverse b at G_A F_A M, and F_B of the extended A-unit. Naturality of b at
the A-unit and the A triangle identity reduce this to the identity. This is also the
transpose of the B-unit. Injectivity of the adjunction Hom bijection gives equality. -/
theorem reductionCompatibilities_unit
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (cpt : Compactification f)
    [cpt.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of D.k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of D.k))]
    [IsSeparated (cpt.Z ↘ Spec (.of D.k))]
    [cpt.i.IsOver (Spec (.of D.k))] [cpt.g.IsOver (Spec (.of D.k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A cpt.i cpt.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B cpt.i cpt.g).obj M.obj))
    (hSX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶
      reductionCtfScalar φ Y hSY ⋙ GB)
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj ≫
          (reductionCompactSupport B cpt.i cpt.g).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    (M : spFiniteConstructibleTorCategory X A) :
    (scalarExtensionFunctor φ X).map (adjA.unit.app M).hom ≫
        (c.app ((reductionCtfCompactSupport A cpt.i cpt.g hFA).obj M)).hom ≫
        (GB.map (ObjectProperty.homMk
          ((reductionDirectImageComparison φ cpt.i cpt.g).app M.obj))).hom =
      (adjB.unit.app ((reductionCtfScalar φ X hSX).obj M)).hom := by
  sorry

/-- Successive exceptional coefficient comparisons compose with the recorded scalar
associators on both schemes. The three comparisons are fixed by their counit equations.
Source: sk-lem-sp-reduction-compatibilities, clause (2)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Step 3): Transpose the successive comparison under the C-adjunction.
The BC counit equation removes cBC. Naturality of bBC at cAB then moves the latter
through bBC inverse. The AB counit equation leaves scalar extension of the A-counit
followed by the two inverse support comparisons. The coefficient cocycle of
reductionDirectImage_cocycle, with naturality of the scalar associator, identifies
this with the transpose defining cAC. Injectivity of transposition proves equality.
All scalar associators are those normalized by K-flat balanced tensor in Step 1. -/
theorem reductionCompatibilities_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (cpt : Compactification f)
    [cpt.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of D.k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of D.k))]
    [IsSeparated (cpt.Z ↘ Spec (.of D.k))]
    [cpt.i.IsOver (Spec (.of D.k))] [cpt.g.IsOver (Spec (.of D.k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    {C : Type u} [CommRing C] [Finite C]
    (_hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (ψ : B →+* C)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A cpt.i cpt.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B cpt.i cpt.g).obj M.obj))
    (hFC : ∀ M : spFiniteConstructibleTorCategory X C,
      spFiniteConstructibleTor Y C ((reductionCompactSupport C cpt.i cpt.g).obj M.obj))
    (hABX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hABY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hBCX : ∀ K : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor X C ((scalarExtensionFunctor ψ X).obj K.obj))
    (hBCY : ∀ K : spFiniteConstructibleTorCategory Y B,
      spFiniteConstructibleTor Y C ((scalarExtensionFunctor ψ Y).obj K.obj))
    (hACX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X C ((scalarExtensionFunctor (ψ.comp φ) X).obj K.obj))
    (hACY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y C ((scalarExtensionFunctor (ψ.comp φ) Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB)
    (GC : spFiniteConstructibleTorCategory Y C ⥤ spFiniteConstructibleTorCategory X C)
    (adjC : reductionCtfCompactSupport C cpt.i cpt.g hFC ⊣ GC)
    (cAB : GA ⋙ reductionCtfScalar φ X hABX ⟶
      reductionCtfScalar φ Y hABY ⋙ GB)
    (hcAB : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj ≫
          (reductionCompactSupport B cpt.i cpt.g).map (cAB.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hABY).obj K)).hom =
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    (cBC : GB ⋙ reductionCtfScalar ψ X hBCX ⟶
      reductionCtfScalar ψ Y hBCY ⋙ GC)
    (hcBC : ∀ K : spFiniteConstructibleTorCategory Y B,
      (reductionDirectImageComparison ψ cpt.i cpt.g).app (GB.obj K).obj ≫
          (reductionCompactSupport C cpt.i cpt.g).map (cBC.app K).hom ≫
          (adjC.counit.app ((reductionCtfScalar ψ Y hBCY).obj K)).hom =
        (scalarExtensionFunctor ψ Y).map (adjB.counit.app K).hom)
    (cAC : GA ⋙ reductionCtfScalar (ψ.comp φ) X hACX ⟶
      reductionCtfScalar (ψ.comp φ) Y hACY ⋙ GC)
    (hcAC : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison (ψ.comp φ) cpt.i cpt.g).app (GA.obj K).obj ≫
          (reductionCompactSupport C cpt.i cpt.g).map (cAC.app K).hom ≫
          (adjC.counit.app ((reductionCtfScalar (ψ.comp φ) Y hACY).obj K)).hom =
        (scalarExtensionFunctor (ψ.comp φ) Y).map (adjA.counit.app K).hom)
    (K : spFiniteConstructibleTorCategory Y A) :
    (scalarExtensionFunctor ψ X).map (cAB.app K).hom ≫
        (cBC.app ((reductionCtfScalar φ Y hABY).obj K)).hom ≫
        (GC.map (ObjectProperty.homMk
          ((scalarExtensionFunctor_composition φ ψ Y).hom.app K.obj))).hom =
      (scalarExtensionFunctor_composition φ ψ X).hom.app (GA.obj K).obj ≫
        (cAC.app K).hom := by
  sorry

/-- Scalar extension carries the diagonal/DNC-normalized smooth purity map to the
same map over the new finite ring, under canonical pullback/twist balancing.
`alphaA` and `alphaB` are precisely the orientations of finiteGeneralRingSmoothPurity:
OrientationNormalized retains the actual diagonal mate, the t=1-normalized Rees
comparison and the inverse integration-transposed bundle arrow. `e` retains the
scalar/root-generator normalization; it is not an arbitrary Tate-line isomorphism.
Source: sk-lem-sp-reduction-compatibilities, clause (3)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Steps 1 and 4--8): The scalar monoidal and pullback identifications are
balanced tensor maps on flat K-flat representatives, respecting symmetry and shifts.
For the fixed compactification apply ringedExchangeTensorCoherence to its proper part
and the extension-by-zero tensor comparison to its open part. On the open part both
orders extend sections by zero and multiply the same B-scalars. Pasting gives the
projection/scalar square. FiniteRingCompactSupportProjection makes its projection
maps invertible on the bounded intrinsically constructible inputs omega_A and K.
Transpose the tensor map h using inverse projection followed by the counit at A_Y.
The projection square, naturality and the counit equation defining c identify the
two tensor-map transposes, hence c (h_A)_B = h_B rho. Choose one positive ell-power
annihilating both A and B. finiteGeneralRingSmoothPurity identifies each orientation
with extension of the same prime-power diagonal orientation. Clause (2), already
stated above, gives delta (o_A)_B = o_B; exponent independence permits this common
choice. Finally gamma_R = h_R (1 tensor o_R). Substitute the two equalities to obtain
c (gamma_A)_B = gamma_B lambda. Intrinsic finite-ring comparison identifies the fixed
module presentation used here with the ordinary uncompleted constant-ring category. -/
theorem reductionCompatibilities_purity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasCompactification f]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hn : 1 ≤ n)
    (hA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0)
    (hB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaA : Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) (ℓ ^ n) hA X d)
    (alphaB : Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} B) (ℓ ^ n) hB X d)
    (_ha : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hA X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaA)
    (_hb : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} B) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hB X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaB)
    (e : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) (ℓ ^ n) hA hB X)
    (K : Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) Y)
    (_hK : Etale.FiniteSmoothPurity.IsCtf (ULift.{u + 1, u} A) Y K) :
    (Etale.FiniteSmoothPurity.proScalar (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).map
        (Etale.FiniteSmoothPurity.proGamma (ULift.{u + 1, u} A) f _ alphaA K) ≫
        Etale.FiniteSmoothPurity.proCoefficientMap
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) f K =
      Etale.FiniteSmoothPurity.proLambda f d e K ≫
        Etale.FiniteSmoothPurity.proGamma (ULift.{u + 1, u} B) f _ alphaB
          ((Etale.FiniteSmoothPurity.proScalar
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
