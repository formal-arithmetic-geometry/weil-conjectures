/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange

public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Sheaf.SixFunctors.CtfStabilityDirectImages
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.SecSmoothPurity.ScalarExtensionFunctor

/-!
# Mixed finite-coefficient base change

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
`sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-mixed.md`, node
(blueprint: det-sp-mixed-base-change).

The statement records the two coefficient/base-change squares for the canonical
compact-support and exceptional comparisons.  The maps are written in the ordinary
constant-ring pro-etale categories; the inputs are the existing bounded intrinsically
constructible finite-Tor categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Change derived realization coordinates for an exact fixed-scalar functor.
Source: blueprint mixed-base-change proof, Step 1 (blueprint: det-sp-mixed-base-change). -/
def mixedDerivedTransport (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ((sfIntrinsicModuleEquivalence X A).inverse ⋙ F ⋙
        (sfIntrinsicModuleEquivalence Y A).functor).mapDerivedCategory ≅
      (sfIntrinsicDerivedEquivalence X A).inverse ⋙ F.mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)

/-- Transport the actual ordinary open base-change isomorphism to intrinsic coefficients.
The realization units cancel at the middle schemes; the outside comparisons are fixed
by their sectionwise units. No inverse is chosen from bare existence.
Source: blueprint mixed-base-change proof, Steps 1 and 3
(blueprint: det-sp-mixed-base-change). -/
def mixedOpenBaseChangeIso (A : Type u) [CommRing A] [Finite A]
    {U' U Z' Z : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ Z')
    (j : U ⟶ Z) (g : Z' ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙
        proEtaleConstantRingDerivedPullback A g ≅
      proEtaleConstantRingDerivedPullback A h ⋙
        (sfIntrinsicExtensionByZero j' A).mapDerivedCategory := by
  let Λ := ULift.{u + 1, u} A
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
  let J' := (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategory
  let V := (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory
  let H := (upperStar (ModuleCat.{u + 1} Λ) h).mapDerivedCategory
  let EU := sfIntrinsicDerivedEquivalence U A
  let EZ := sfIntrinsicDerivedEquivalence Z A
  let EU' := sfIntrinsicDerivedEquivalence U' A
  let EZ' := sfIntrinsicDerivedEquivalence Z' A
  exact Functor.isoWhiskerLeft _ (openSquareDerivedPullbackModel A g) ≪≫
    Functor.isoWhiskerRight (mixedDerivedTransport A _) _ ≪≫
    Functor.isoWhiskerLeft _ (mixedDerivedTransport A _) ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ J) (EZ.funInvIdAssoc (V ⋙ EZ'.functor)) ≪≫
    Functor.isoWhiskerLeft EU.inverse
      (Functor.isoWhiskerRight (ordinaryOpenExtensionBaseChangeIso Λ h j' j g sq)
        EZ'.functor) ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ H) (EU'.funInvIdAssoc (J' ⋙ EZ'.functor)).symm ≪≫
    Functor.isoWhiskerLeft (EU.inverse ⋙ H ⋙ EU'.functor)
      (mixedDerivedTransport A
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j')).symm ≪≫
    Functor.isoWhiskerRight
      (mixedDerivedTransport A (upperStar (ModuleCat.{u + 1} Λ) h)).symm _ ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel A h).symm _

/-- The coefficient-independent pullback compactification.
Source: blueprint mixed-base-change Step 1 (blueprint: det-sp-mixed-base-change). -/
abbrev mixedPullbackCompactification
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f) : Compactification f' :=
  c.ofIsPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

/-- The canonical compact-support exchange, in the same intrinsic constant-ring
coordinates as b. Its proper factor is the normalized counit mate, and its open
factor is the existing ordinary base-change isomorphism transported above.
Source: blueprint mixed-base-change proof Step 4
(blueprint: det-sp-mixed-base-change). -/
def mixedCompactSupportExchange (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g)
    (c : Compactification f) :
    reductionCompactSupport A c.i c.g ⋙ proEtaleConstantRingDerivedPullback A g ⟶
      proEtaleConstantRingDerivedPullback A h ⋙
        reductionCompactSupport A (mixedPullbackCompactification sq c).i
          (mixedPullbackCompactification sq c).g := by
  let hp := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let cp := mixedPullbackCompactification sq c
  let psq : ChosenCartesianSquare (pullback.fst c.g g) (pullback.snd c.g g) c.g g :=
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  exact Functor.whiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
      (directImageConstantExchange A psq) ≫
    Functor.whiskerRight
      (mixedOpenBaseChangeIso A h cp.i c.i (pullback.fst c.g g)
        (c.isPullback_i_ofIsPullback hp)).hom (directImageConstantPush A cp.g)

/-- Pullback on the full intrinsic Dctf categories; the certificate affects only membership.
Source: blueprint mixed-base-change proof Steps 4 and 6
(blueprint: det-sp-mixed-base-change). -/
def mixedCtfPullback (A : Type u) [CommRing A] [Finite A]
    {U V : Scheme.{u}} (g : U ⟶ V)
    (hg : ∀ K : spFiniteConstructibleTorCategory V A,
      spFiniteConstructibleTor U A ((proEtaleConstantRingDerivedPullback A g).obj K.obj)) :=
  (spFiniteConstructibleTor U A).lift
    ((spFiniteConstructibleTor V A).ι ⋙ proEtaleConstantRingDerivedPullback A g) hg

set_option maxHeartbeats 600000 in
-- Elaborating the four full-subcategory adjunctions and their counit equations
-- exceeds the default heartbeat budget; the ordinary 60-second file limit is retained.
/-- The compact-support and exceptional mixed coefficient/base-change identities.
All comparison maps are specified: beta is the proper/open composite above, c and c'
obey their actual coefficient-counit equations, and eA and eB obey the base-change
counit equations. The latter equations are written after precomposition by beta,
which is invertible on Dctf. They therefore specify exactly the transposes in the node.
The right adjoints are right adjoints on Dctf, with no assertion about ambient adjoints.

Source: main-20261015, sk-prop-sp-purity-bc-mixed.md
(blueprint: det-sp-mixed-base-change).

Proof, following the six steps of the DAG:
1. Pull back the chosen compactification. Smooth relative dimension is unchanged.
   Compute the scalar/pullback comparisons on flat K-flat resolutions: both routes
   send a local pure tensor to the same tensor with the composite inverse image.
   These identifications respect the square comparison and its coefficient action.
2. For the proper factor, transpose the two mixed composites under the primed
   B-adjunction. Both transposes are scalar extension of the pullback of the
   A-counit followed by the pullback-square comparison. Use the defining counit
   equation of the coefficient mate and naturality of the square comparison.
   The adjunction bijection equates the two proper mixed composites.
3. For the open factor, extension by zero of a flat-term K-flat resolution is again
   flat-term K-flat: tensoring it with Q is j_!(P tensor j^*Q); both open functors
   are exact, and j_! preserves the sums in total tensor products. Both mixed maps
   restrict to the identity on the open. The open adjunction detects maps from j'_!,
   proving the open mixed square without detecting derived maps by geometric stalks.
4. The actual formulas are b = Rp_*(open scalar map) followed after the proper mate,
   and beta = Rp'_*(open base change) after proper exchange. Finite-ring constructible
   derived origin supplies bounded etale antecedents. Proper exchange agrees with
   transported exchange by its counit-mate normalization; the open factors agree by
   restriction and the open adjunction. Thus beta is the specified exchange, invertible
   on Dctf. Pullback and scalar extension preserve Dctf, so all inputs are legitimate.
5. Substitute these formulas, move the open scalar map through proper exchange by
   naturality, use the proper and open mixed squares, and then move open base change
   through the proper coefficient mate by naturality. The result is the first identity.
6. Transpose both exceptional composites under the primed B-adjunction. The left
   transpose is scalar extension of the pulled-back A-counit after the inverses of
   scalar-extended beta_A and b'. The right transpose is the same pulled-back counit
   after the inverses of pullback(b) and beta_B. The first identity at M = GA(K),
   inverted, equates those factors. The adjunction bijection gives the second identity.
-/
theorem mixedBaseChange
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y X' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))]
    [QuasiCompact (X' ↘ Spec (.of k))] [IsSeparated (X' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (cpt : Compactification f) [cpt.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of k))] [IsSeparated (cpt.Z ↘ Spec (.of k))]
    [cpt.i.IsOver (Spec (.of k))] [cpt.g.IsOver (Spec (.of k))]
    {Y' : Scheme.{u}} [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare g' f' f g)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A
        ((reductionCompactSupport A cpt.i
          cpt.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B
        ((reductionCompactSupport B cpt.i
          cpt.g).obj M.obj))
    (hFAp : ∀ M : spFiniteConstructibleTorCategory X' A,
      spFiniteConstructibleTor Y' A
        ((reductionCompactSupport A (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).obj M.obj))
    (hFBp : ∀ M : spFiniteConstructibleTorCategory X' B,
      spFiniteConstructibleTor Y' B
        ((reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).obj M.obj))
    (hSX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hSXp : ∀ K : spFiniteConstructibleTorCategory X' A,
      spFiniteConstructibleTor X' B ((scalarExtensionFunctor φ X').obj K.obj))
    (hSYp : ∀ K : spFiniteConstructibleTorCategory Y' A,
      spFiniteConstructibleTor Y' B ((scalarExtensionFunctor φ Y').obj K.obj))
    (hVA : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y' A ((proEtaleConstantRingDerivedPullback A g).obj K.obj))
    (hVB : ∀ K : spFiniteConstructibleTorCategory Y B,
      spFiniteConstructibleTor Y' B ((proEtaleConstantRingDerivedPullback B g).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (GAp : spFiniteConstructibleTorCategory Y' A ⥤ spFiniteConstructibleTorCategory X' A)
    (GBp : spFiniteConstructibleTorCategory Y' B ⥤ spFiniteConstructibleTorCategory X' B)
    (adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB)
    (adjAp : reductionCtfCompactSupport A (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g hFAp ⊣ GAp)
    (adjBp : reductionCtfCompactSupport B (mixedPullbackCompactification sq cpt).i
      (mixedPullbackCompactification sq cpt).g hFBp ⊣ GBp)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (cp : GAp ⋙ reductionCtfScalar φ X' hSXp ⟶ reductionCtfScalar φ Y' hSYp ⋙ GBp)
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj ≫
        (reductionCompactSupport B cpt.i cpt.g).map (c.app K).hom ≫
        (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
      (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    (hcp : ∀ K : spFiniteConstructibleTorCategory Y' A,
      (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).app (GAp.obj K).obj ≫
        (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map (cp.app K).hom ≫
        (adjBp.counit.app ((reductionCtfScalar φ Y' hSYp).obj K)).hom =
      (scalarExtensionFunctor φ Y').map (adjAp.counit.app K).hom)
    (eA : ∀ K : spFiniteConstructibleTorCategory Y A,
      (proEtaleConstantRingDerivedPullback A g').obj (GA.obj K).obj ⟶
        (GAp.obj ((mixedCtfPullback A g hVA).obj K)).obj)
    (eB : ∀ K : spFiniteConstructibleTorCategory Y B,
      (proEtaleConstantRingDerivedPullback B g').obj (GB.obj K).obj ⟶
        (GBp.obj ((mixedCtfPullback B g hVB).obj K)).obj)
    (heA : ∀ K : spFiniteConstructibleTorCategory Y A,
      (mixedCompactSupportExchange A sq cpt).app (GA.obj K).obj ≫
        (reductionCompactSupport A (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map (eA K) ≫
        (adjAp.counit.app ((mixedCtfPullback A g hVA).obj K)).hom =
      (proEtaleConstantRingDerivedPullback A g).map (adjA.counit.app K).hom)
    (heB : ∀ K : spFiniteConstructibleTorCategory Y B,
      (mixedCompactSupportExchange B sq cpt).app (GB.obj K).obj ≫
        (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map (eB K) ≫
        (adjBp.counit.app ((mixedCtfPullback B g hVB).obj K)).hom =
      (proEtaleConstantRingDerivedPullback B g).map (adjB.counit.app K).hom) :
    (∀ M : spFiniteConstructibleTorCategory X A,
      (directImageScalarPullbackIso φ g).inv.app
          ((reductionCompactSupport A cpt.i cpt.g).obj M.obj) ≫
        (proEtaleConstantRingDerivedPullback B g).map
          ((reductionDirectImageComparison φ cpt.i cpt.g).app M.obj) ≫
        (mixedCompactSupportExchange B sq cpt).app
          ((scalarExtensionFunctor φ X).obj M.obj) =
      (scalarExtensionFunctor φ Y').map ((mixedCompactSupportExchange A sq cpt).app M.obj) ≫
        (reductionDirectImageComparison φ (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).app
            ((proEtaleConstantRingDerivedPullback A g').obj M.obj) ≫
        (reductionCompactSupport B (mixedPullbackCompactification sq cpt).i
          (mixedPullbackCompactification sq cpt).g).map
            ((directImageScalarPullbackIso φ g').inv.app M.obj)) ∧
    (∀ K : spFiniteConstructibleTorCategory Y A,
      (scalarExtensionFunctor φ X').map (eA K) ≫
          (cp.app ((mixedCtfPullback A g hVA).obj K)).hom =
        (directImageScalarPullbackIso φ g').inv.app (GA.obj K).obj ≫
          (proEtaleConstantRingDerivedPullback B g').map (c.app K).hom ≫
          eB ((reductionCtfScalar φ Y hSY).obj K) ≫
          (GBp.map (ObjectProperty.homMk
            ((directImageScalarPullbackIso φ g).hom.app K.obj))).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
