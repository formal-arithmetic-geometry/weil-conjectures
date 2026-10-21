/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
public import Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
import Sheaf.Paper.EtaleSumTensorTotalization
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate

/-! # The tensor normalization of the etale sum right adjoint

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1; Stacks Project Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

The comparison is the existing derived graph comparison. The tensor arrow uses the
inverse of the specified compactification projection, transported to exact pullback.
All adjunctions are quantified, and all inputs belong to the ordinary unbounded categories.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange exactEtaleSumExchange

/-- The conjugate of the inverse canonical graph comparison for a fixed compactification.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorRho
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (canonicalEtaleCompactSupportComparison A e c).symm

attribute [local irreducible] etaleTensorRho

/-- The coefficient normalization eta is rho at the unit followed by coefficient pullback.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorEta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G.obj (constantComplex A X) ≅ constantComplex A U :=
  (etaleTensorRho A e c G adj).app (constantComplex A X) ≪≫ etaleSumPullbackUnitIso A e

attribute [local irreducible] etaleTensorEta

/-- The specified compactification projection, with exact rather than left-derived pullback.
Source: Stacks Tag 0GKF, support-map compatibility (2)
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorProjection
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (e : U ⟶ X)
    (c : Compactification e) (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K))

attribute [local irreducible] etaleTensorProjection

/-- The specified projection is invertible, including compactifications with nonfinite proper part.
Source: Stacks Tag 0GKF; blueprint Step 1
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

Proof: Support-map compatibility (2) conjugates this arrow by the canonical graph comparison
to the derived sum projection. The latter is an isomorphism: on sheaves its generator rule
is distribution over lift-indexed sums, and flat K-flat resolutions and sum totalization
descend that rule to arbitrary unbounded inputs. Cancel the graph comparison isomorphisms. -/
theorem isIso_etaleTensorProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (M : DerivedCategoryModule A U) (K : DerivedCategoryModule A X) :
    IsIso (etaleTensorProjection A e c M K) := by
  sorry

/-- The displayed inverse transpose defining tau, as an actual compact-support morphism.
Source: blueprint Step 1, displayed inverse-transpose formula; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorInverseTranspose
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (((derivedTensor (ModuleCat.{u + 1} A) U).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).obj
          (G.obj (constantComplex A X))) ⟶ K :=
  haveI := isIso_etaleTensorProjection A e c (G.obj (constantComplex A X)) K
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) U).hom.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).app
          (G.obj (constantComplex A X))) ≫
    inv (etaleTensorProjection A e c (G.obj (constantComplex A X)) K) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
      (adj.counit.app (constantComplex A X))).app K ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X K).hom

attribute [local irreducible] etaleTensorInverseTranspose

/-- The tensor transpose tau under the chosen compact-support adjunction.
Source: blueprint Step 1, displayed inverse-transpose formula; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorTau
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) U).obj
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).obj
        (G.obj (constantComplex A X)) ⟶ G.obj K :=
  adj.homEquiv _ _ (etaleTensorInverseTranspose A e c G adj K)

attribute [local irreducible] etaleTensorTau

/-- Counit characterization and the tensor equality, as maps natural in every unbounded K.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

Proof:
1. Conjugate the inverse graph comparison. The defining mate equation, composed with d,
   gives ev S(rho) d = epsilon. Conversely the sum-adjunction Hom bijection makes rho
   the unique natural transformation satisfying this equation. For a : F N -> K, naturality
   gives J_S(a d_N^{-1}) = J_F(a) rho_K.
2. At the sheaf level the sum projection sends (s,b) tensor h to (s,b tensor s^*h).
   Evaluation followed by coefficient multiplication sends both sides of the unit-counit
   identity to b h. Linearity, tensor universality and sheafification give equality of maps;
   inverse image is restriction on etale test objects and respects the constant-ring action.
3. Choose flat-term K-flat representatives. Pullback and sum extension preserve these;
   sum totalization identifies the projection with the same generator map in every degree.
   The termwise sum/restriction adjunction descends its evaluation counit. The coefficient
   unit has degree zero, so the differentials agree. Tensor descent and localization give
   the unit-counit identity naturally on all unbounded K.
4. Apply support-map compatibility (2) to replace the inverse specified projection in the
   inverse transpose q_F of tau. Naturality of d gives q_F d^{-1} as the sum inverse
   projection followed by (epsilon at the unit) tensor 1 and the left unitor.
5. Substitute epsilon d^{-1} = ev S(rho) at the unit. Naturality of sum projection moves
   rho through it. The identity of step 3 reduces the result to ev S of
   lambda ((eta tensor 1) sym). Signed symmetry and its unit constraint identify this arrow
   with the right unitor after 1 tensor eta; no Koszul sign is omitted.
6. Transpose under the sum adjunction, using step 1. This gives tau rho = (1 tensor eta)
   unitor. Every construction is natural in K, giving the final naturality clause.
-/
theorem etaleSumRightAdjointTensor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    (∀ r : G ⟶ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory,
      (∀ K : DerivedCategoryModule A X,
        (canonicalEtaleCompactSupportComparison A e c).hom.app (G.obj K) ≫
          (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
            (r.app K) ≫
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K = adj.counit.app K) ↔
        r = (etaleTensorRho A e c G adj).hom) ∧
    (∀ K : DerivedCategoryModule A X,
      etaleTensorTau A e c G adj K ≫ (etaleTensorRho A e c G adj).hom.app K =
        ((derivedTensor (ModuleCat.{u + 1} A) U).obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).map
            (etaleTensorEta A e c G adj).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) U
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom) ∧
    (∀ (K L : DerivedCategoryModule A X) (f : K ⟶ L),
      ((derivedTensor (ModuleCat.{u + 1} A) U).map
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map f)).app
          (G.obj (constantComplex A X)) ≫ etaleTensorTau A e c G adj L =
        etaleTensorTau A e c G adj K ≫ G.map f) := by
  sorry

/-- Refinement preserves rho, eta and the actual tensor transpose.
Source: blueprint Step 1; Stacks Tag 0GKF
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

Proof (step 7): For the canonical left comparison t, proper-support compatibility gives
 d' t = d, and support-map compatibility intertwines the specified projections. Conjugate
 t^{-1} to obtain r. The counit characterization gives r rho' = rho; at the coefficient
 unit this gives r eta' = eta. Substitute into the inverse-transpose formula and use
 projection compatibility to obtain tau r = (1 tensor r_unit) tau'. Common-refinement
 coherence follows from composition of left comparisons and contravariant conjugacy. -/
theorem etaleSumRightAdjointTensor_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e)
    (G H : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    (conjugateIsoEquiv adj adj'
        (rightDerivedLowerShriekOfCompactificationIso A c d).symm ≪≫
      etaleTensorRho A e d H adj' = etaleTensorRho A e c G adj) ∧
    ((conjugateIsoEquiv adj adj'
        (rightDerivedLowerShriekOfCompactificationIso A c d).symm).app (constantComplex A X) ≪≫
      etaleTensorEta A e d H adj' = etaleTensorEta A e c G adj) ∧
    (∀ K : DerivedCategoryModule A X,
      etaleTensorTau A e c G adj K ≫
        (conjugateIsoEquiv adj adj'
          (rightDerivedLowerShriekOfCompactificationIso A c d).symm).hom.app K =
      ((derivedTensor (ModuleCat.{u + 1} A) U).obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).map
          ((conjugateIsoEquiv adj adj'
            (rightDerivedLowerShriekOfCompactificationIso A c d).symm).hom.app
              (constantComplex A X)) ≫ etaleTensorTau A e d H adj' K) := by
  sorry

/-- The pullback-composition comparison for a Cartesian square, from its commutative boundary.
Source: blueprint Step 1, step 8; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorPullbackSquare
    (A : Type (u + 1)) [CommRing A] {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    (sq : IsPullback h e' e g) :
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory :=
  (unboundedEtaleUpperStarCompIso A h e).symm ≪≫
    eqToIso (congrArg (fun f : U' ⟶ X =>
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory)
      sq.w) ≪≫ unboundedEtaleUpperStarCompIso A e' g

attribute [local irreducible] etaleTensorPullbackSquare

/-- The normalized right restriction comparison chi, with the precise formula of step 8.
Source: blueprint Step 1, step 8; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-tensor). -/
noncomputable def etaleTensorRestrictionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}} {e : U ⟶ X} {e' : U' ⟶ X'}
    {g : X' ⟶ X} {h : U' ⟶ U} (sq : IsPullback h e' e g)
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e'] [QuasiCompact e] [QuasiCompact e']
    (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙ H :=
  Functor.isoWhiskerRight (etaleTensorRho A e c G adj) _ ≪≫
    etaleTensorPullbackSquare A sq ≪≫
      Functor.isoWhiskerLeft _ (etaleTensorRho A e' d H adj').symm

attribute [local irreducible] etaleTensorRestrictionIso

/-- Open restriction preserves the coefficient normalization and tensor transpose, with chi
as the specified right-adjoint comparison, including the coefficient-unit transports.
Source: blueprint Step 1; Stacks Tags 0GKF and 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-tensor).

Proof (steps 8--9): On a test object over X', lifts to the fiber product are exactly lifts
 to U. Thus restriction preserves both evaluation and the sum tensor generator rule.
 Support-map compatibility (1) identifies the restriction of d with d'. The left-composite
 compact-support comparison becomes the nested-summand comparison for sum extension;
 conjugating and mate-pasting identifies its right comparison with the displayed chi.
 The constant pullback-unit comparisons then give the eta equation. Pull back the tensor
 equality, use the canonical tensor-pullback comparison and the eta equation, and use the
 tensor equality for e'. Cancel the invertible rho' to obtain the tau equation below.
 The specified projection normalizations agree by the same test-object generator rule.
 No equality of derived morphisms is inferred merely from stalk cohomology. -/
theorem etaleSumRightAdjointTensor_openRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {g : X' ⟶ X} {h : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e'] [QuasiCompact e] [QuasiCompact e']
    [IsOpenImmersion g] [IsOpenImmersion h] (sq : IsPullback h e' e g)
    (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (H : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
        (etaleTensorEta A e c G adj).hom ≫ (etaleSumPullbackUnitIso A h).hom =
      (etaleTensorRestrictionIso A sq c d G H adj adj').hom.app (constantComplex A X) ≫
        H.map (etaleSumPullbackUnitIso A g).hom ≫ (etaleTensorEta A e' d H adj').hom) ∧
    (∀ K : DerivedCategoryModule A X,
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
          (etaleTensorTau A e c G adj K) ≫
        (etaleTensorRestrictionIso A sq c d G H adj adj').hom.app K =
      (((etaleSupportExactUpperTensorIso A h).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).app
            (G.obj (constantComplex A X))) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) U').map
          ((etaleTensorPullbackSquare A sq).hom.app K)).app
            ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj
              (G.obj (constantComplex A X))) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) U').obj
          ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))).map
          ((etaleTensorRestrictionIso A sq c d G H adj adj').hom.app (constantComplex A X) ≫
            H.map (etaleSumPullbackUnitIso A g).hom) ≫
        etaleTensorTau A e' d H adj'
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) := by
  sorry

end AlgebraicGeometry.Etale
