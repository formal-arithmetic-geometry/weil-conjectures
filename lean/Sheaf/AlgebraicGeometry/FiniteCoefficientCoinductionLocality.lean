/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Locality of derived finite-coefficient coinduction

Source: Travaux de Gabber, Expose XVII, Proposition 6.2.1.1, printed p. 294;
Stacks Project, Tags 08JI and 09XQ
(blueprint: lem-per-finite-coefficient-coinduction-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The kernel of the open adjunction unit, with constant module coefficients.
This is the same supported-kernel construction as for abelian sheaves.
Source: Stacks Project, Tag 09XQ
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def supportedKernelCoefficients (R : Type (u + 1)) [CommRing R]
    {O X : Scheme.{u}} (j : O ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  kernel (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) j).unit

/-- The supported-kernel functor is additive, since its maps are uniquely determined by
composition with its monic kernel inclusion.
Source: Stacks Project, Tag 09XQ
(blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: compose the additivity equation with the kernel inclusion, use its naturality
and additivity of the identity functor, and cancel the monomorphism. -/
theorem supportedKernelCoefficients_additive (R : Type (u + 1)) [CommRing R]
    {O X : Scheme.{u}} (j : O ⟶ X) :
    (supportedKernelCoefficients R j).Additive := by
  sorry

attribute [instance] supportedKernelCoefficients_additive

/-- The supported kernel viewed on the closed subscheme: `i⁻¹ ker(1 → j_*j⁻¹)`.
Source: Stacks Project, Tag 09XQ
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def supportedClosedInverseImageCoefficients (R : Type (u + 1)) [CommRing R]
    {Z O X : Scheme.{u}} (i : Z ⟶ X) (j : O ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  supportedKernelCoefficients R j ⋙ upperStar (ModuleCat.{u + 1} R) i

/-- Additivity of supported inverse image follows from additivity of its two factors.
Source: Stacks 09XQ
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
instance supportedClosedInverseImageCoefficients_additive (R : Type (u + 1)) [CommRing R]
    {Z O X : Scheme.{u}} (i : Z ⟶ X) (j : O ⟶ X) :
    (supportedClosedInverseImageCoefficients R i j).Additive :=
  inferInstanceAs (supportedKernelCoefficients R j ⋙
    upperStar (ModuleCat.{u + 1} R) i).Additive

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Restriction of scalars commutes with inverse image. The isomorphism is the conjugate
of the sectionwise identity commuting direct image and coextension of scalars.
Source: Gabber XVII 6.2.1.1, locality expansion
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def coinductionScalarPullbackIso {Y X : Scheme.{u}} (g : Y ⟶ X) :
    upperStar (ModuleCat.{u + 1} B) g ⋙ Sheaf.restrictScalars Y.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ upperStar (ModuleCat.{u + 1} A) g :=
  (conjugateIsoEquiv
    ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g).comp
      (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ))).symm
    (lowerStarCompCoextendScalarsIso φ g)

/-- The same scalar-pullback isomorphism on bounded-below derived categories, obtained
by localization of exact functors.
Source: Gabber XVII 6.2.1.1, locality expansion
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def coinductionScalarPullbackIsoPlus {Y X : Scheme.{u}} (g : Y ⟶ X) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategoryPlus ⋙
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus ≅
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (coinductionScalarPullbackIso φ g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical B-linear coinduction pullback comparison: the mate of the scalar-pullback
isomorphism under restriction/coinduction. Its adjunct is the pulled-back evaluation counit.
Source: Gabber XVII 6.2.1.1, locality expansion
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def finiteCoinductionPullbackMap {Y X : Scheme.{u}} (g : Y ⟶ X) :
    (coextendScalars φ X).rightDerivedFunctorPlus ⋙
        (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙
        (coextendScalars φ Y).rightDerivedFunctorPlus :=
  (mateEquiv (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).derivedPlus
    (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).derivedPlus
    (TwoSquare.mk _ _ _ _ (coinductionScalarPullbackIsoPlus φ g).hom)).natTrans

/-- Restriction of scalars commutes with direct image, by the identity on every section.
This is its localization on bounded-below derived categories for a closed immersion.
Source: Gabber XVII 6.2.1.1, locality expansion
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def coinductionScalarClosedImageIsoPlus {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} B) i).mapDerivedCategoryPlus ⋙
        (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ≅
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (Iso.refl _ : lowerStar (ModuleCat.{u + 1} B) i ⋙
          Sheaf.restrictScalars X.smallEtaleTopology φ ≅
        Sheaf.restrictScalars Z.smallEtaleTopology φ ⋙
          lowerStar (ModuleCat.{u + 1} A) i) ≪≫
    Functor.mapDerivedCategoryPlusCompIso
      (Sheaf.restrictScalars Z.smallEtaleTopology φ)
      (lowerStar (ModuleCat.{u + 1} A) i)

/-- The normalized closed comparison, obtained by conjugating the scalar/direct-image
identity under the two pasted adjunctions. Thus it preserves their counits.
Source: Gabber XVII 6.2.1.1, locality expansion; Stacks 09XQ
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def finiteCoinductionClosedIso {Z O X : Scheme.{u}}
    (i : Z ⟶ X) (j : O ⟶ X) [IsClosedImmersion i]
    (aA : lowerStar (ModuleCat.{u + 1} A) i ⊣ supportedClosedInverseImageCoefficients A i j)
    (aB : lowerStar (ModuleCat.{u + 1} B) i ⊣ supportedClosedInverseImageCoefficients B i j) :
    (coextendScalars φ X).rightDerivedFunctorPlus ⋙
        (supportedClosedInverseImageCoefficients B i j).rightDerivedFunctorPlus ≅
      (supportedClosedInverseImageCoefficients A i j).rightDerivedFunctorPlus ⋙
        (coextendScalars φ Z).rightDerivedFunctorPlus :=
  conjugateIsoEquiv
    (aB.derivedPlus.comp
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).derivedPlus)
    ((Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ).derivedPlus.comp aA.derivedPlus)
    (coinductionScalarClosedImageIsoPlus φ i).symm

/-- Derived coinduction is right t-exact in the convention of a lower cohomology bound.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: restriction of scalars is exact and left adjoint to coextension. Choose an injective
representative vanishing below a; termwise coextension preserves that vanishing and computes
its right derived functor. This is proof Steps 1 and 2 of the node. -/
theorem coinduction_preserves_lower_bound (X : Scheme.{u})
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a : ℤ) (hK : K.IsGE a) :
    ((coextendScalars φ X).rightDerivedFunctorPlus.obj K).IsGE a := by
  sorry

/-- Coinduction on a bounded-below injective representative is termwise Hom with B, with
its usual B-action. The derived-functor unit is the canonical comparison, not a chosen iso.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: exact restriction is left adjoint to coextension, so coextension preserves injectives.
The bounded-below injective representative is K-injective and the localization unit is
invertible on it. Independence of representatives follows from homotopy equivalence of
injective representatives. These are proof Steps 1 and 2 of the node. -/
theorem coinduction_injective_representative (X : Scheme.{u})
    (I : CochainComplex.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.1.X n)] :
    IsIso ((coextendScalars φ X).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient _).obj I)) := by
  sorry

/-- Finite-coefficient coinduction commutes with arbitrary exact etale inverse image.
The augmentation is a quasi-isomorphism to B in degree zero; each resolution term is
finite free, with no lower bound on the resolution. The comparison is the B-linear mate
of the pulled-back evaluation counit, as defined above.
Source: Gabber XVII 6.2.1.1 and Stacks 08JI
(blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof:
1. Exact restriction and sectionwise Hom give the restriction/coinduction adjunction;
   coextension preserves injectives (lem-sp-right-adjoint-preserves-injectives).
2. Bounded-below injective representatives compute the right derived adjoint and preserve
   the lower bound (lem-weil-pbc-dplus-injective-representative and the homotopy adjunction).
3. Apply the exact constant-sheaf functor to the augmented finite-free resolution. The
   bounded-free RHom model computes the underlying A-object by Hom(P,N). For N zero below
   a, degree n has only the finitely many terms a-n ≤ p ≤ 0. Its differential is
   d_N f - (-1)^n f d_P. No strict B-action on P is asserted.
4. The scalar restriction of the displayed mate is the Hom pullback map induced by
   evaluation. Each finite-free Hom term is a finite power of N. Exact inverse image
   commutes with these powers and with the constant scalar matrices of d_P, hence the
   comparison is invertible after forgetting to A. Restriction reflects isomorphisms
   by the cohomology-sheaf criterion, so it is invertible over B.
5. For closed immersions, support kernels give the closed adjunction with module
   coefficients: the abelian-sheaf adjunction restricts to linear morphisms. Derive it
   on bounded-below injectives.
6. Restriction commutes sectionwise with closed direct image. Conjugating this identity
   under the composite adjunctions gives the closed comparison and its counit law.
7. Mate pasting gives both composition laws and the identity law.
8. Apply pullback at Spec(O_X,x), then the closed comparison at Spec(kappa(x)); applying
   a geometric inverse image and its comparison gives the geometric-fibre version.
9. A rank-one local system and its dual give inverse exact tensor functors. Locally
   trivializing the line identifies Hom(B,I) tensor L_B with Hom(B,I tensor L), by
   h tensor (b tensor l) ↦ (b' ↦ h(bb') tensor l). These local isomorphisms glue and
   commute with the complex differentials. Degree-zero evaluation, the signed Hom
   differential and the pasted adjunctions commute with cohomological shifts.
Only bounded-below K and finite rank in each degree of P were used: constructibility,
finite Tor amplitude and finite projective dimension are unnecessary. -/
theorem finite_coefficient_coinduction_locality
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{u + 1} A) (ComplexShape.up ℤ) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)))
    (hε : QuasiIso ε)
    (hP : ∀ n : ℤ, 0 < n → IsZero (P.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (P.X n ≅ ModuleCat.of A (Fin r → A)))
    {Y X : Scheme.{u}} (g : Y ⟶ X) :
    IsIso (finiteCoinductionPullbackMap φ g) ∧
      (finiteCoinductionPullbackMap φ g).CommShift ℤ := by
  sorry

/-- Identity and composition coherence of the canonical pullback comparisons.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: take the adjunct of both sides. Both are the inverse image of the evaluation
counit; the mate-pasting identity identifies them, including the identity case (Step 7). -/
theorem finiteCoinductionPullbackMap_comp {Z Y X : Scheme.{u}}
    (h : Z ⟶ Y) (g : Y ⟶ X) :
    (finiteCoinductionPullbackMap φ (h ≫ g)) ≫
      Functor.whiskerRight (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) h g).hom
        (coextendScalars φ Z).rightDerivedFunctorPlus =
    Functor.whiskerLeft (coextendScalars φ X).rightDerivedFunctorPlus
        (upperStarCompDerivedPlus (ModuleCat.{u + 1} B) h g).hom ≫
      Functor.whiskerRight (finiteCoinductionPullbackMap φ g)
        (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategoryPlus ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus
        (finiteCoinductionPullbackMap φ h) := by
  sorry

/-- Identity coherence of the pullback comparison.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: the mate of the identity square is the identity, by the triangle identities;
use the canonical identity identifications of exact inverse image (Step 7). -/
theorem finiteCoinductionPullbackMap_id (X : Scheme.{u}) :
    finiteCoinductionPullbackMap φ (𝟙 X) ≫
        Functor.whiskerRight (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) X).hom
          (coextendScalars φ X).rightDerivedFunctorPlus =
      Functor.whiskerLeft (coextendScalars φ X).rightDerivedFunctorPlus
        (upperStarIdDerivedPlus (ModuleCat.{u + 1} B) X).hom := by
  sorry

/-- The support-kernel closed adjunction exists with arbitrary constant ring coefficients.
Source: Stacks 09XQ, proof; Gabber XVII 6.2.1.1
(blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: the supported-kernel adjunction for abelian sheaves restricts to linear morphisms:
its formulas commute with scalar multiplication. Closed direct image is exact on
underlying abelian sheaves. This proves Step 5, before deriving the adjunction. -/
theorem coinduction_supported_closed_adjunction (R : Type (u + 1)) [CommRing R]
    {Z O X : Scheme.{u}} (i : Z ⟶ X) (j : O ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hcompl : IsCompl (Set.range i.base) (Set.range j.base)) :
    Nonempty (lowerStar (ModuleCat.{u + 1} R) i ⊣
      supportedClosedInverseImageCoefficients R i j) := by
  sorry

/-- The closed comparison has the pasted counit normalization and respects shifts.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: conjugate the sectionwise scalar/direct-image identity under the two composite
adjunctions. The conjugate-iso counit identity gives the displayed equation. Derivation
and conjugation commute with shifts, by degree-zero counits (Steps 6 and 9). -/
theorem finiteCoinductionClosedIso_counit {Z O X : Scheme.{u}}
    (i : Z ⟶ X) (j : O ⟶ X) [IsClosedImmersion i]
    (aA : lowerStar (ModuleCat.{u + 1} A) i ⊣ supportedClosedInverseImageCoefficients A i j)
    (aB : lowerStar (ModuleCat.{u + 1} B) i ⊣ supportedClosedInverseImageCoefficients B i j) :
    (∀ K : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ((lowerStar (ModuleCat.{u + 1} B) i).mapDerivedCategoryPlus ⋙
          (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus).map
          ((finiteCoinductionClosedIso φ i j aA aB).hom.app K) ≫
        (coinductionScalarClosedImageIsoPlus φ i).hom.app _ ≫
        ((Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ).derivedPlus.comp
          aA.derivedPlus).counit.app K =
      (aB.derivedPlus.comp
        (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).derivedPlus).counit.app K) ∧
      (finiteCoinductionClosedIso φ i j aA aB).hom.CommShift ℤ := by
  sorry


/-- Extension of a line from A to B: sheafify the sectionwise module B tensor_A L.
Source: Stacks, Modules on Sites, tensor product construction; Gabber XVII 6.2.1.1
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def coinductionCoefficientLine (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
    (L.obj ⋙ ModuleCat.extendScalars φ)

/-- Rank-one twisting commutes naturally with coefficient coinduction and with shifts.
The local triviality condition says precisely that L is locally isomorphic to A_X.
Right deriving tensor by a line agrees with ordinary tensor: that tensor functor is
an exact equivalence, with inverse tensor by its dual.
Source: Gabber XVII 6.2.1.1, coefficient expansion
(blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: trivialize L on a covering sieve. Tensor by L and its dual are inverse exact
functors, hence preserve injectives. On injectives the balanced B-linear map sends
h tensor (b tensor l) to (b' ↦ h(bb') tensor l). In a trivialization it is the identity
on Hom(B,I). Thus it is an isomorphism locally and hence globally. It is natural in
I, commutes with differentials and with the signed shift maps. Deriving on bounded-below
injectives and inverting gives the displayed natural isomorphism (Step 9). -/
theorem finiteCoinduction_rank_one_twist (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : ∀ U : X.Etale, ∃ S : Sieve U,
      S ∈ X.smallEtaleTopology U ∧
      ∀ (V : X.Etale) (f : V ⟶ U), S f →
        Nonempty (L.over V ≅ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).over V)) :
    ∃ e : (tensorRight L).rightDerivedFunctorPlus ⋙
        (coextendScalars φ X).rightDerivedFunctorPlus ≅
      (coextendScalars φ X).rightDerivedFunctorPlus ⋙
        (tensorRight (coinductionCoefficientLine φ X L)).rightDerivedFunctorPlus,
      e.hom.CommShift ℤ := by
  sorry

/-- The costalk comparison is the pullback mate at Spec(O_X,x), followed by the normalized
closed comparison at Spec(kappa(x)). Its definition uses these actual canonical maps.
Source: Gabber XVII 6.2.1.1, supported cohomology
(blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def finiteCoinductionCostalkMap (X : Scheme.{u}) (x : X)
    {O : Scheme.{u}} (j : O ⟶ Spec (X.presheaf.stalk x))
    (aA : lowerStar (ModuleCat.{u + 1} A) (Spec.map (X.residue x)) ⊣
      supportedClosedInverseImageCoefficients A (Spec.map (X.residue x)) j)
    (aB : lowerStar (ModuleCat.{u + 1} B) (Spec.map (X.residue x)) ⊣
      supportedClosedInverseImageCoefficients B (Spec.map (X.residue x)) j) :
    (coextendScalars φ X).rightDerivedFunctorPlus ⋙
        (upperStar (ModuleCat.{u + 1} B) (X.fromSpecStalk x)).mapDerivedCategoryPlus ⋙
        (supportedClosedInverseImageCoefficients B
          (Spec.map (X.residue x)) j).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) (X.fromSpecStalk x)).mapDerivedCategoryPlus ⋙
        (supportedClosedInverseImageCoefficients A
          (Spec.map (X.residue x)) j).rightDerivedFunctorPlus ⋙
        (coextendScalars φ (Spec (X.residueField x))).rightDerivedFunctorPlus :=
  Functor.whiskerRight (finiteCoinductionPullbackMap φ (X.fromSpecStalk x))
      (supportedClosedInverseImageCoefficients B
        (Spec.map (X.residue x)) j).rightDerivedFunctorPlus ≫
    Functor.whiskerLeft
      (upperStar (ModuleCat.{u + 1} A) (X.fromSpecStalk x)).mapDerivedCategoryPlus
      (finiteCoinductionClosedIso φ (Spec.map (X.residue x)) j aA aB).hom

/-- Costalk locality, also after geometric inverse image. These are isomorphisms in the
B-coefficient category; neither constructibility nor a finite resolution length is assumed.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: apply the pullback locality theorem at the localization, followed by the closed
comparison. For the fibre, apply geometric inverse image and then its pullback comparison.
Both steps are invertible and commute with shifts by Steps 7--9 of the node. -/
theorem finiteCoinduction_costalk_locality
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{u + 1} A) (ComplexShape.up ℤ) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)))
    (hε : QuasiIso ε)
    (hP : ∀ n : ℤ, 0 < n → IsZero (P.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (P.X n ≅ ModuleCat.of A (Fin r → A)))
    (X : Scheme.{u}) (x : X) {O : Scheme.{u}}
    (j : O ⟶ Spec (X.presheaf.stalk x))
    (aA : lowerStar (ModuleCat.{u + 1} A) (Spec.map (X.residue x)) ⊣
      supportedClosedInverseImageCoefficients A (Spec.map (X.residue x)) j)
    (aB : lowerStar (ModuleCat.{u + 1} B) (Spec.map (X.residue x)) ⊣
      supportedClosedInverseImageCoefficients B (Spec.map (X.residue x)) j) :
    IsIso (finiteCoinductionCostalkMap φ X x j aA aB) ∧
      (finiteCoinductionCostalkMap φ X x j aA aB).CommShift ℤ ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (e : Spec (.of Ω) ⟶ Spec (X.residueField x)),
        IsIso (Functor.whiskerRight (finiteCoinductionCostalkMap φ X x j aA aB)
            (upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategoryPlus ≫
          Functor.whiskerLeft
            ((upperStar (ModuleCat.{u + 1} A) (X.fromSpecStalk x)).mapDerivedCategoryPlus ⋙
              (supportedClosedInverseImageCoefficients A
                (Spec.map (X.residue x)) j).rightDerivedFunctorPlus)
            (finiteCoinductionPullbackMap φ e)) ∧
        (Functor.whiskerRight (finiteCoinductionCostalkMap φ X x j aA aB)
            (upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategoryPlus ≫
          Functor.whiskerLeft
            ((upperStar (ModuleCat.{u + 1} A) (X.fromSpecStalk x)).mapDerivedCategoryPlus ⋙
              (supportedClosedInverseImageCoefficients A
                (Spec.map (X.residue x)) j).rightDerivedFunctorPlus)
            (finiteCoinductionPullbackMap φ e)).CommShift ℤ := by
  sorry

/-- The derived restriction/coinduction adjunction, with its evaluation counit. Restriction
is the exact sectionwise scalar restriction, so this is the derived adjunction of the node.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality). -/
noncomputable def finiteCoinductionAdjunction (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⊣
      (coextendScalars φ X).rightDerivedFunctorPlus :=
  (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).derivedPlus

/-- Composition coherence of closed comparisons, with the composite closed right adjoint
identified by the composite closed adjunction. Conjugating the composite scalar square
is exactly the paste of the two normalized closed comparisons.
Source: Gabber XVII 6.2.1.1 (blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: restriction commutes sectionwise with both closed direct images. The composite
square is their paste. The mate-pasting identity, applied to the three composite
adjunctions, identifies the conjugate of this paste with the paste of the conjugates.
Their counit equations paste as well. Canonical closed-composition identifications are
those of these composite adjunctions, so this is the closed-composition clause (Step 7). -/
theorem finiteCoinductionClosedIso_comp {Z Y X O₁ O₂ : Scheme.{u}}
    (i : Z ⟶ Y) (k : Y ⟶ X) (j₁ : O₁ ⟶ Y) (j₂ : O₂ ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion k]
    (aAi : lowerStar (ModuleCat.{u + 1} A) i ⊣
      supportedClosedInverseImageCoefficients A i j₁)
    (aBi : lowerStar (ModuleCat.{u + 1} B) i ⊣
      supportedClosedInverseImageCoefficients B i j₁)
    (aAk : lowerStar (ModuleCat.{u + 1} A) k ⊣
      supportedClosedInverseImageCoefficients A k j₂)
    (aBk : lowerStar (ModuleCat.{u + 1} B) k ⊣
      supportedClosedInverseImageCoefficients B k j₂) :
    conjugateIsoEquiv
      ((aBi.derivedPlus.comp aBk.derivedPlus).comp
        (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).derivedPlus)
      ((Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ).derivedPlus.comp
        (aAi.derivedPlus.comp aAk.derivedPlus))
      (Functor.isoWhiskerLeft (lowerStar (ModuleCat.{u + 1} B) i).mapDerivedCategoryPlus
          (coinductionScalarClosedImageIsoPlus φ k) ≪≫
        Functor.isoWhiskerRight (coinductionScalarClosedImageIsoPlus φ i)
          (lowerStar (ModuleCat.{u + 1} A) k).mapDerivedCategoryPlus).symm =
    Functor.isoWhiskerRight (finiteCoinductionClosedIso φ k j₂ aAk aBk)
        (supportedClosedInverseImageCoefficients B i j₁).rightDerivedFunctorPlus ≪≫
      Functor.isoWhiskerLeft
        (supportedClosedInverseImageCoefficients A k j₂).rightDerivedFunctorPlus
        (finiteCoinductionClosedIso φ i j₁ aAi aBi) := by
  sorry

/-- Forgetting the B-action on coinduction gives derived internal Hom from the constant
A-module sheaf B_X. This relates the sectionwise coextension construction to the
recorded internal-Hom interface, naturally in K.
Source: Gabber XVII 6.2.1.1; Stacks, internal Hom on sites
(blueprint: lem-per-finite-coefficient-coinduction-locality).
Proof: a map out of the constant module B is locally the same as an A-linear map B
into the sections. Thus sectionwise coextension, after restriction, is internal Hom
from B_X. For a bounded-below injective representative I the complex of these sheaf
Homs computes RHom(B_X,K). The canonical localization comparisons give the natural
isomorphism, independent of I; degree-zero evaluation makes it commute with shifts
(Steps 1--3). -/
theorem finiteCoinduction_underlying_rhom (X : Scheme.{u}) :
    Nonempty ((coextendScalars φ X).rightDerivedFunctorPlus ⋙
        (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        _root_.DerivedCategory.Plus.ι ≅
      _root_.DerivedCategory.Plus.ι ⋙
        (derivedHom (ModuleCat.{u + 1} A) X).obj
          (op ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
                ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)))))
      ) := by
  sorry

end AlgebraicGeometry.Etale
