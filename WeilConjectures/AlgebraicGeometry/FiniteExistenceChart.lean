/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSheafProjectionData
public import WeilConjectures.AlgebraicGeometry.SmoothRepresentingPair
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace

/-! # The finite Brown adjoint on a coordinate chart

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-finite-existence,
`det-sp-finite-existence-chart.md`, clauses 1--3
(blueprint: det-sp-finite-existence-chart).

The affine space is the library's ordered coordinate tower, with its canonical
`affineTraceAffineSpaceIso` to `AffineSpace (ULift (Fin d)) Y`. Counits use the
specified sum adjunction and the specified ordered affine-line adjunction.
The statement uses the ordinary etale presentation of Dctf; finite site comparison
identifies this with the pro-etale assertion, including its counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The canonical compact-support composition comparison for a coordinate chart.
Both factors are the graph-normalized etale sum/compact-support comparisons.
Source: chart proof, step 6 (blueprint: det-sp-finite-existence-chart). -/
def finiteChartLeftComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (d : ℕ)
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : j ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y d) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf :=
  letI := affineTraceNoetherian Y d
  let cp := HasCompactification.compactification (affineTraceProjection Y d)
  let cg := HasCompactification.compactification (e ≫ affineTraceProjection Y d)
  let norm := canonicalEtaleCompactSupportNormalization A
  etaleAmbientLeftComparison A norm e (affineTraceProjection Y d) cp cg ≪≫
    (etaleAmbientLeftComparison A norm j f cf (cg.copy he)).symm

/-- The actual Brown counit restricted to the chart, expressed on its canonical
compact-support composite. No right-adjoint comparison is chosen here.
Source: chart proof, step 7 (blueprint: det-sp-finite-existence-chart). -/
def finiteChartBrownCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
    (f : X ⟶ Y) (j : U ⟶ X) [IsOpenImmersion j] (d : ℕ)
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    (he : j ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f)
    (H : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y)
    (counit : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) cf).obj H ⟶ K) :
    ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).obj
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj H) ⟶ K :=
  (finiteChartLeftComparison A f j d e he cf).hom.app
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj H) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
      ((etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j inferInstance).mapDerivedCategoryAdjunction.counit.app
          H) ≫ counit

/-- The finite chart adjunctions, with fibre-sum, tensor-trace, and Brown-counit
normalizations. The base field has characteristic p > 0 different from ell and
finite ell-cohomological dimension. Noetherian instances and exponent
invertibility are derived from this standing finite-type setting.
The Brown adjoint is supplied by its existing representing-pair interface on Dctf,
with no adjunction on the whole unbounded category assumed.

Source: latest blueprint `det-sp-finite-existence-chart`, clauses 1--3
(blueprint: det-sp-finite-existence-chart).

Proof:
1. Finite-type schemes over k are Noetherian and ell^n is invertible on them.
The graph-normalized compact-support comparison identifies Re! with exact sum
extension. Its termwise sum/evaluation adjunction restricts to Dctf. On stalks,
the germ-normalized direct-sum comparison sends each lift summand to that lift;
the inverse-image stalk comparison makes its evaluation the identity. Thus the
counit is the fibre sum, including an empty fibre.
2. Compose the normalized projective-line/open-chart adjunctions in coordinate
order, starting from the identity for d=0. The canonical reassociation identifies
the right functor with p* tensor the finite Tate object shifted by 2d. The actual
counit tensor normalization identifies its value at K with inverse projection,
then 1 tensor the unit trace, then the right unitor. Pullback, Tate tensor and
shift preserve Dctf, and compact support preserves it as well.
3. Compose the sum and affine Hom bijections. Use the canonical compact-support
composition comparison and the open sum adjunction to transport the Brown
counit; this is exactly finiteChartBrownCounit. Transpose it under the composite
adjunction. Transpose the composite counit in the opposite direction. The Hom
bijections show that the two maps are inverse and that the counit equation
uniquely determines the comparison. Finite site comparison transports these
Hom bijections and their actual counits to the pro-etale Dctf categories.
-/
theorem finite_existence_chart
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {X Y U : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [U.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    (d : ℕ)
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [SmoothOfRelativeDimension d f]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (he : j ≫ f = e ≫ affineTraceProjection Y d) (cf : Compactification f) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth d f
    letI : HasCompactification f := cf.hasCompactification
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    letI : IsNoetherian X := ⟨⟩
    letI : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    letI : IsNoetherian Y := ⟨⟩
    letI : IsLocallyNoetherian U :=
      LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
    letI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
    letI : IsNoetherian U := ⟨⟩
    let hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
      have h : (ell : k) ≠ 0 :=
        CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime)
          (Fact.out : ringChar k ≠ ell)
      simpa only [map_natCast, map_pow, Nat.cast_pow] using
        (((Ne.isUnit h).pow n).map (Scheme.ΓSpecIso (.of k)).inv.hom).map
          (Y ↘ Spec (.of k)).appTop.hom
    let A := ULift.{u + 1} (ZMod (ell ^ n))
    let N := ell ^ n
    let hA : (N : A) = 0 := CharP.cast_eq_zero A N
    let hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
    letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
    let P := AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleProperty A
    let T := affineTraceTower Y d
    let p := affineTraceProjection Y d
    let L := rightDerivedLowerShriek (ModuleCat.{u + 1} A) p
    let E := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    let R := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    let s := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction
    let W := SectionLocalDualizingComparisons.tateObject A N hA T d
    let Q := fun K : DerivedCategoryModule A Y ↦
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj
        ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K)).obj W
    ∃ (t : OrdinaryFiniteTwistTransport A N hA)
      (D : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
        OrdinaryFiniteP1Datum A N hA t S hS),
      (PreservesFiniteLimits (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) ∧
       PreservesFiniteColimits (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance)) ∧
      (∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
        letI : DecidableEq (Over.mk x ⟶ Over.mk e) := Classical.decEq _
        ∀ (z : Over.mk x ⟶ Over.mk e)
        (a : ((Scheme.pointSmallEtale z.left).sheafFiber
          (A := ModuleCat.{u + 1} A)).obj ((upperStar (ModuleCat.{u + 1} A) e).obj F)),
        ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).map
          ((etaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app F)
          ((etaleProjectionSumStalkIso A e x
            ((upperStar (ModuleCat.{u + 1} A) e).obj F)).inv
              (DirectSum.lof A _ _ z a)) = (etaleProjectionLiftStalkIso A e x z F).hom a) ∧
      (∀ M, P U M → P T (E.obj M)) ∧
      (∀ B, P T B → P U (R.obj B)) ∧
      (∀ (B : DerivedCategoryModule A T), P T B →
        ∀ (M : DerivedCategoryModule A U), P U M →
          Function.Bijective (fun b : M ⟶ R.obj B ↦ E.map b ≫ s.counit.app B)) ∧
      (∀ M, P T M → P Y (L.obj M)) ∧
      (∀ (K : DerivedCategoryModule A Y), P Y K →
        P T (Q K) ∧
        (∀ (M : DerivedCategoryModule A T), P T M →
          Function.Bijective (fun b : M ⟶ Q K ↦ L.map b ≫
            OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K)) ∧
        (∃ proj : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
            (L.obj W) ≅ L.obj (Q K),
          proj.hom = compactSupportProjectionMap A p W K ∧
          OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K =
            proj.inv ≫ ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
              (OrdinaryAffineCounitTensorNormalization.trace A N hN hA t D Y hY d) ≫
                (derivedTensorSingleUnitIso K).hom) ∧
        (∀ B : RepresentingPair ell n f K, P X B.object →
          ∃! α :
            (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj B.object ≅
              R.obj (Q K),
          (E ⋙ L).map α.hom ≫
            L.map (s.counit.app (Q K)) ≫
              OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D Y hY d K =
            finiteChartBrownCounit A f j d e he
              (HasCompactification.compactification f) B.object K B.counit)) := by
  sorry

end AlgebraicGeometry.Etale
