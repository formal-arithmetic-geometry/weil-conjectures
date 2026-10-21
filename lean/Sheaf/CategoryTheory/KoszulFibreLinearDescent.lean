/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Linear

/-!
# Scalar-linear descent of the explicit Koszul fibre

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
derived.tex, Tags 07KC and 08TC; the explicit coordinate and scalar refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent).

The proposition below packages all the clauses of this single statement. Its witnesses
are constrained by the actual product, differential, diagonal maps, and degree-zero unit.
There is no choice of a cone in a triangulated category in this specification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable (O : Sheaf J CommRingCat.{u})

/-- The displayed product B(M), using the existing strict negative Koszul tower.
Index m means exponent m+1. The dual tower is canonically the ordered tensor of
[O --b_j^(m+1)--> O] in degrees [-r,0], including the empty tensor O[0].
Source: Stacks 0A0E (blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreProduct (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :=
  ∏ᶜ (fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op m))

/-- One minus the actual quotient-tower transition shift on B(M).
Source: Stacks 08TC (blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreEndomorphism (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :=
  towerTransitionEndomorphism
    (K := fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op m)) (fun m ↦
    ((ringedKoszulTensorTower O r b).obj M).map (homOfLE (Nat.le_succ m)).op)

/-- The product of a tensor identity at every tower level, on a chain map.
Source: Stacks 0A0E, explicit refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreProductMap (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {M N : ringedSiteComplex O} (a : M ⟶ N) :=
  Limits.Pi.map
    (f := fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj M).obj (op m))
    (g := fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).obj N).obj (op m))
    (fun m : ℕ ↦ ((ringedKoszulTensorTower O r b).map a).app (op m))

/-- The actual degree-zero inclusions into the product B(M).
Source: Stacks 0A0E (blueprint: lem-sbc-koszul-fibre-linear-descent). -/
abbrev koszulFibreProductUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (M : ringedSiteComplex O) :
    M ⟶ koszulFibreProduct O r b M :=
  Pi.lift (fun m : ℕ ↦ ringedKoszulTensorUnitComponent O r b M (op m))

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- The exact coordinate specification and all descent conclusions of the Koszul fibre
statement. The two `letI` declarations install the previously constructed coefficient
structure and finite biproducts; neither introduces an assumption or chooses an object.
The existential functor is determined up to the unique coordinate isomorphism by its
objects, differentials, maps and unit. In particular, this is not an arbitrary functor
with the right isomorphism classes of values. The derived-limit clause includes its
actual first projection and actual localized tower transitions. The tower comparison
identifies these ordinary tensors, including their transitions, with derived tensors.

Source: Stacks 0A0E, 07KC and 08TC, explicit scalar and coordinate refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent). -/
def KoszulFibreLinearDescentData (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) : Prop :=
  letI := scalarLocalizationCoefficientLinear A O α
  letI := HasFiniteBiproducts.of_hasFiniteProducts
    (C := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  ∃ (F : ringedSiteComplex O ⥤ ringedSiteComplex O)
    (η : 𝟭 (ringedSiteComplex O) ⟶ F)
    (χ : ∀ (M : ringedSiteComplex O) (i : ℤ),
      (F.obj M).X i ≅ (koszulFibreProduct O r b M).X i ⊞
        (koszulFibreProduct O r b M).X (i - 1))
    (π : ∀ M : ringedSiteComplex O, F.obj M ⟶ koszulFibreProduct O r b M),
    (∀ (M : ringedSiteComplex O) (i : ℤ),
      (F.obj M).d i (i + 1) ≫ (χ M (i + 1)).hom =
        (χ M i).hom ≫ biprod.lift
          (biprod.fst ≫ (koszulFibreProduct O r b M).d i (i + 1))
          (biprod.fst ≫ (koszulFibreEndomorphism O r b M).f i ≫
            eqToHom (congrArg (koszulFibreProduct O r b M).X
              (Int.add_sub_cancel i 1).symm) -
            biprod.snd ≫ (koszulFibreProduct O r b M).d (i - 1) ((i + 1) - 1))) ∧
    (∀ (M N : ringedSiteComplex O) (a : M ⟶ N) (i : ℤ),
      (F.map a).f i ≫ (χ N i).hom = (χ M i).hom ≫
        biprod.map ((koszulFibreProductMap O r b a).f i)
          ((koszulFibreProductMap O r b a).f (i - 1))) ∧
    (∀ (M : ringedSiteComplex O) (i : ℤ),
      (η.app M).f i ≫ (χ M i).hom =
        biprod.lift ((koszulFibreProductUnit O r b M).f i) 0) ∧
    (∀ (M : ringedSiteComplex O) (i : ℤ), (π M).f i = (χ M i).hom ≫ biprod.fst) ∧
    (∀ (M N : ringedSiteComplex O) (a a' : M ⟶ N),
      Nonempty (Homotopy a a') → Nonempty (Homotopy (F.map a) (F.map a'))) ∧
    (∀ (M N : ringedSiteComplex O) (a : M ⟶ N), QuasiIso a → QuasiIso (F.map a)) ∧
    F.Additive ∧ F.Linear A ∧
    (∃ (z : F.obj 0 ≅ 0), η.app 0 ≫ z.hom = 0) ∧
    (∀ M N : ringedSiteComplex O,
      IsIso (Functor.biprodComparison F M N) ∧
      η.app (M ⊞ N) ≫ Functor.biprodComparison F M N = biprod.map (η.app M) (η.app N)) ∧
    (∀ (M N M' N' : ringedSiteComplex O) (a : M ⟶ M') (a' : N ⟶ N'),
      F.map (biprod.map a a') ≫ Functor.biprodComparison F M' N' =
        Functor.biprodComparison F M N ≫ biprod.map (F.map a) (F.map a')) ∧
    ∃ (D : ringedSiteDerived O ⥤ ringedSiteDerived O)
      (κ : 𝟭 (ringedSiteDerived O) ⟶ D)
      (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ D),
      D.Additive ∧ D.Linear A ∧
      (∀ M : ringedSiteComplex O,
        DerivedCategory.Q.map (η.app M) ≫ (e.app M).hom =
          κ.app (DerivedCategory.Q.obj M)) ∧
      (∀ (M N : ringedSiteDerived O) (a : M ⟶ N) (t : A),
        D.map (t • a) = t • D.map a) ∧
      (∀ M : ringedSiteComplex O,
        Nonempty (((ringedKoszulTensorTower O r b).obj M ⋙ DerivedCategory.Q) ≅
          (ringedKoszulDualTower O r b ⋙ DerivedCategory.Q ⋙
            (SheafOfModules.KFlatFixedTensor.derivedTensor O).obj
              (DerivedCategory.Q.obj M)))) ∧
      (∀ M : ringedSiteComplex O,
        ∃ _hp : HasProduct (fun m : ℕ ↦ DerivedCategory.Q.obj
            (((ringedKoszulTensorTower O r b).obj M).obj (op m))),
          ∃ (p : D.obj (DerivedCategory.Q.obj M) ⟶ ∏ᶜ (fun m : ℕ ↦
              DerivedCategory.Q.obj (((ringedKoszulTensorTower O r b).obj M).obj (op m))))
            (δ : (∏ᶜ (fun m : ℕ ↦ DerivedCategory.Q.obj
              (((ringedKoszulTensorTower O r b).obj M).obj (op m)))) ⟶
                (D.obj (DerivedCategory.Q.obj M))⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun m ↦ DerivedCategory.Q.map
                (((ringedKoszulTensorTower O r b).obj M).map
                  (homOfLE (Nat.le_succ m)).op))
              (D.obj (DerivedCategory.Q.obj M)) p δ ∧
            ∀ m : ℕ, (e.app M).hom ≫ p ≫ Pi.π _ m =
              DerivedCategory.Q.map (π M ≫ Pi.π _ m)) ∧
      HasZeroObject (ObjectProperty.FullSubcategory
        (fun M : ringedSiteDerived O ↦ IsIso (κ.app M))) ∧
      HasBinaryBiproducts (ObjectProperty.FullSubcategory
        (fun M : ringedSiteDerived O ↦ IsIso (κ.app M))) ∧
      Functor.Linear A (ObjectProperty.ι
        (fun M : ringedSiteDerived O ↦ IsIso (κ.app M)))

/-- The explicit product fibre descends to an additive A-linear completion functor,
with its specified unit and additive full subcategory of complete objects.

Source: Stacks Project, algebraization.tex, Tag 0A0E, lemma-derived-completion-koszul;
derived.tex, Tags 07KC and 08TC; explicit scalar-linear refinement
(blueprint: lem-sbc-koszul-fibre-linear-descent).

Proof (the node's ten steps):
1. The two-term transition square is b^m b = b^(m+1). Tensor the factors, with
   the signed total differential. Their terms are finite free, including r=0.
2. Bounded-above flat sheaf complexes are K-flat (lem-pc-bounded-above-flat-kflat-site).
   Fixed K-flat tensor preserves quasi-isomorphisms and computes derived tensor,
   naturally in the fixed argument (lem-weil-pbc-kflat-fixed-tensor-triangulated).
3. Set u=1-s. The mixed terms in d_F squared cancel because u is a chain map.
   Products of a tensor 1 commute with u. Check identities, composition, addition
   and scalar multiplication at every product projection.
4. Tensor a chain homotopy with 1. The cross signs are (-1)^(p-1) and (-1)^p.
   The fibre homotopy is (h_B,-h_B); its mixed term u h_B-h_B u is zero.
5. Exact countable products compute derived products
   (lem-weil-derived-countable-products-core). Thus B(a) is a quasi-isomorphism;
   apply lem-pe-roos-coordinates-quasi-iso to the diagonal fibre map.
6. Descend QF by lem-weil-pbc-localization-universal-property. Additivity descends
   by lem-pur-additive-localization-descent. The canonical derived A-action and Q's
   linearity are lem-weil-linear-abelian-derived-category; use
   lem-sfb-linear-localization-descent to cover every derived morphism.
7. The actual projections make QB the derived product. In cone coordinates the
   chain isomorphism is (x,y) to (-y,x), with inverse (v,w) to (w,-v).
   Rotate its cone triangle, obtaining the Roos triangle of def-weil-derived-limit.
8. The degree-zero inclusions give e:M to B(M), with ue=0. The unit is (e,0).
   Check naturality at projections, then descend it by localization's universal
   property. This fixes the unit, without claiming uniqueness from level maps alone.
9. Distribute tensor and products over zero and binary sums in both fibre coordinates.
   These canonical comparisons are natural and identify the units; localization
   preserves the identities, and Q is additive.
10. The zero unit is invertible. A sum of invertible units is invertible by the
    preceding comparison. Fullness gives inherited Hom A-modules and bilinear
    composition. This proves the stated additive full subcategory. -/
theorem koszulFibreLinearDescent (A : Type v) [CommRing A]
    (α : A →+* RingCat.sectionsSubring (O.obj ⋙ forget₂ CommRingCat RingCat))
    (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [CountableAB4Star (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] :
    KoszulFibreLinearDescentData O A α r b := by
  sorry

end CategoryTheory
