/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Homology.Additive
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.FlatConstructibleTensor
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.QuasiExcellentEtaleDirectImageFiniteness
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.RingTheory.FiniteFreeResolution
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities

/-!
# Constant-coefficient projection over excellent schemes

Source: Bhatt--Scholze, Lemma 6.7.17, printed p. 57
(blueprint: lem-per-excellent-etale-constant-projection).

## Main declarations

* `excellentConstantComplexPullbackIso`: canonical constant inverse-image identification.
* `excellentConstantComplexProjectionMap`: the natural counit projection map.
* `excellentConstantComplexProjectionMap_naturality`: naturality in the input complex.
* `excellent_etale_constant_projection`: preservation and the two projection isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Canonical identification of the derived inverse image of a constant complex with
that constant complex on the source. Exactness of constant sheaves makes its value on
Q(P) the termwise constant complex, via mapDerivedCategoryFactors.
Source: Bhatt--Scholze, Lemma 6.7.17, and the constant inverse-image identification
(blueprint: lem-per-excellent-etale-constant-projection). -/
def excellentConstantComplexPullbackIso
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}} (g : V ⟶ X) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
        L(upperStar (ModuleCat.{u + 1} A) g) ≅
      (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (upperStar (ModuleCat.{u + 1} A) g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g)

/-- The counit projection map with its target identified with tensoring by the constant
complex on V. It is natural in the coefficient complex; naturality in K comes from the
published bifunctorial projection map and the fixed constant inverse-image isomorphism.
Source: Bhatt--Scholze, Lemma 6.7.17, the displayed projection formula
(blueprint: lem-per-excellent-etale-constant-projection). -/
def excellentConstantComplexProjectionMap
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}} (g : V ⟶ X)
    (K : DerivedCategoryModule A V) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
        (derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ⟶
      (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
        (derivedTensor (ModuleCat.{u + 1} A) V).obj K ⋙
          (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor :=
  Functor.whiskerLeft
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) g).app K) ≫
    (Functor.associator
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
      ((derivedTensor (ModuleCat.{u + 1} A) V).obj K ⋙
        (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor)).inv ≫
    Functor.whiskerRight (excellentConstantComplexPullbackIso A g).hom
      ((derivedTensor (ModuleCat.{u + 1} A) V).obj K ⋙
        (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor)

/-- Naturality in the input of the constant-complex counit projection. Naturality in
the coefficient complex is the naturality field of excellentConstantComplexProjectionMap.
Source: Bhatt--Scholze, Lemma 6.7.17, naturality of its canonical projection map
(blueprint: lem-per-excellent-etale-constant-projection).
Proof: apply naturality of rightDerivedLowerStarProjectionMap in K. Compose with
Rg_* of tensoring by the natural constant pullback identification. Functoriality of
derived tensor and direct image gives exactly the displayed square. -/
theorem excellentConstantComplexProjectionMap_naturality
    (A : Type (u + 1)) [CommRing A] {V X : Scheme.{u}} (g : V ⟶ X)
    {K K' : DerivedCategoryModule A V} (f : K ⟶ K')
    (P : _root_.DerivedCategory (ModuleCat.{u + 1} A)) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map f)).app
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj P) ≫
        (excellentConstantComplexProjectionMap A g K').app P =
      (excellentConstantComplexProjectionMap A g K).app P ≫
        (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} A) V).map f).app
            ((constantSheaf V.smallEtaleTopology
              (ModuleCat.{u + 1} A)).mapDerivedCategory.obj P)) := by
  sorry

/-- Ordinary direct image preserves bounded constructible finite-Tor complexes and
satisfies the constant-coefficient projection formula, including nonperfect coefficients.
The target uses the canonical identification of the inverse image of a constant
complex with the constant complex on V. Both maps are natural counit transposes.

Source: Bhatt--Scholze, Lemma 6.7.17, printed p. 57
(blueprint: lem-per-excellent-etale-constant-projection).

Proof:
1. Use lem-sf-etale-flat-constructible to represent L by a bounded flat constructible
complex. By lem-pc-bounded-above-flat-kflat-site it is K-flat. Tensoring with a finite
constant module remains bounded constructible, by lem-fd-flat-constructible-tensor
and thm-constructible-serre.
2. Apply lem-per-quasi-excellent-etale-direct-image-finiteness with F_ell coefficients.
Filter every constructible Z/ell^m sheaf by powers of ell. Each quotient is a
constructible F_ell sheaf. Restriction commutes with bounded-below direct image by
lem-sbc-canonical-restrict-scalars-functor-comparisons; the Serre property and finite
induction give bounded constructible direct images for these sheaves.
3. Use lem-sf-derived-truncation-triangle and
lem-pc-right-derived-functor-triangulated to extend this to bounded constructible
complexes. Fix upper bounds c and u for Rg_*L and Rg_*(L tensor F_ell).
4. Finite residue-field filtrations and lem-kun-derived-tensor-triangulated give the
same bound u for Rg_*(L tensor N) for every finite constant module N.
5. The counit projection is the identity on the coefficient unit. Naturality,
finite sums, shifts (lem-weil-pbc-derived-adjunction-shift), and brutal truncation
triangles give invertibility on bounded finite free complexes. The tensor comparison
is lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
6. By lem-weil-pbc-finite-free-resolution-noetherian resolve a finite module M in
nonpositive degrees. The finite prefix Q_t in degrees -t+1 through 0 maps to M;
its cone is N_t[t], with N_t a finite syzygy. Exact constants preserve this triangle.
7. The two approximation cones have upper bounds c-t and u-t. The first follows by
a nonpositive free resolution of N_t and a good truncation of Rg_*L; the second is
Step 4. For each q choose t with max(c,u)-t < q-1. The cohomology exact sequences
and the natural projection square prove invertibility in degree q, hence in all degrees.
8. Brutal truncation triangles extend this from finite modules to every bounded
complex of finite modules, with no finite projective dimension assumption.
9. Step 2 gives constructibility of Rg_*L; Step 7 identifies its residue-field tensor
with a bounded complex. Apply lem-exc-residue-tor-test with Q_ell coefficients to
obtain Tor amplitude against all module sheaves.
10. The B-linear coefficient map is the scalar extension of the A-counit, transposed
under the B geometric adjunction. Its restriction is the Step 7 projection, by
lem-pur-sheaf-ring-derived-coefficient-adjunction and
lem-sbc-restrict-scalars-derived-adjunction-identities. Exact scalar restriction
reflects isomorphisms. The maps are natural, since their defining counits and tensor
comparisons are natural; no functorial free resolution is required. -/
theorem excellent_etale_constant_projection
    (ell : ℕ) [Fact ell.Prime] (m : ℕ) (hm : 1 ≤ m)
    {V X : Scheme.{u}} [IsNoetherian V] [IsNoetherian X]
    (g : V ⟶ X) [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (hV : ∀ U : V.affineOpens, IsExcellent Γ(V, U.1))
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U.1))
    (hVinvertible : ∀ v : V, IsUnit (ell : V.presheaf.stalk v))
    (hXinvertible : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (L : DerivedCategoryModule (ULift.{u + 1} (ZMod (ell ^ m))) V)
    (hL : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ell ^ m))) V L)
    (hTor : ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (ZMod (ell ^ m))) V a b L) :
    (DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ell ^ m))) X
      (Functor.obj
        (Functor.rightDerivedFunctor
          (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ m)))) g)) L) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1} (ZMod (ell ^ m))) X a b
          (Functor.obj
            (Functor.rightDerivedFunctor
              (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ m)))) g)) L)) ∧
    (∀ P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ m)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) →
      (∀ i : ℤ, Module.Finite (ULift.{u + 1} (ZMod (ell ^ m))) (P.X i)) →
      IsIso ((excellentConstantComplexProjectionMap
        (ULift.{u + 1} (ZMod (ell ^ m))) g L).app (_root_.DerivedCategory.Q.obj P))) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m),
      IsIso (finiteCoefficientDirectImageMap
        ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).ulift) g L)) := by
  sorry

end AlgebraicGeometry.Etale
