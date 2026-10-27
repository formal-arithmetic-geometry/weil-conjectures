/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Balanced finite Tate scalar comparisons and pullback

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, free rank-one summands
(blueprint: lem-sp-finite-tate-balanced-scalar-pullback).

The Boolean index selects the constant line (`false`) or the first root line (`true`).
The ordinary maps and inverses are specified on sheafification generators. The derived
maps are normalized by the published scalar counit, and the squares use the published
K-flat-normalized scalar/pullback comparison. No flatness of the coefficient map occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The two existing finite Tate sheaves, indexed without including higher powers.
Source: blueprint Charts, free rank-one summands; Stacks 03PK
(blueprint: lem-sp-finite-tate-balanced-scalar-pullback). -/
def finiteTateBalancedSheaf (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (i : Bool) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  Scheme.finiteEtaleTateSheaf A N T hA (if i then 1 else 0)

/-- Constant or root-tensor sections generating the two existing sheaves locally.
In the constant case the root variable is ignored; it may always be the identity root.
Source: Stacks 03EK and 03PK
(blueprint: lem-sp-finite-tate-balanced-scalar-pullback). -/
def finiteTateBalancedGenerator (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (i : Bool) (W : T.Etaleᵒᵖ)
    (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W) :
    (finiteTateBalancedSheaf A N hA T i).obj.obj W :=
  match i with
  | false => (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a
  | true => Scheme.finiteEtaleTateOneGenerator A N T hA W a z

/-- Degree-zero embedding of the two existing finite Tate sheaves.
Source: Stacks 06YU (blueprint: lem-sp-finite-tate-balanced-scalar-pullback). -/
def finiteTateBalancedObject (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (i : Bool) : DerivedCategoryModule A T :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj (finiteTateBalancedSheaf A N hA T i)

/-- The canonical derived roots/unit pullback identification, with the degree-zero
localization comparison included. Source: Stacks 03PK and 0D6D
(blueprint: lem-sp-finite-tate-balanced-scalar-pullback). -/
def finiteTateBalancedPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (N : Γ(T', ⊤))) (i : Bool) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        (finiteTateBalancedObject A N hA T i) ≅ finiteTateBalancedObject A N hA T' i :=
  (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.finiteEtaleTwistPullbackData A N hN hA).c f hT hT'
        (if i then 1 else 0))

/-- Shift a specified comparison using the published exact scalar functor comparison.
Source: Stacks 06YU (blueprint: lem-sp-finite-tate-balanced-scalar-pullback). -/
def finiteTateBalancedShiftIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) {K : DerivedCategoryModule A T}
    {L : DerivedCategoryModule B T} (e : (scalarExtension φ T).obj K ≅ L) (n : ℤ) :
    (scalarExtension φ T).obj (K⟦n⟧) ≅ L⟦n⟧ :=
  (FiniteSmoothPurity.scalarShiftIso φ T n).app K ≪≫ (shiftFunctor _ n).mapIso e

/-- The balanced coefficient identifications of the constant and first finite Tate line,
with ordinary inverse formulas, their derived normalizations, their finite sums and shifts,
and their actual derived pullback squares.

Source: main-20261015 blueprint, Charts in sk-lem-sp-reduction-exceptional.proof.md;
Stacks 03EK, 03EL, 03PK, 06YQ, 06YT, 06YU, 07A4, 0D6D and 0G7E
(blueprint: lem-sp-finite-tate-balanced-scalar-pullback).

Proof plan:
1. The finite-twist-line lemma makes both inputs flat whenever N is invertible.
   The K-flat closure lemma makes their degree-zero complexes K-flat. The derived
   change-of-rings counit computes their extension by ordinary extension, even when B/A
   is nonflat (lem-pur-derived-change-of-rings).
2. On ordinary tensors use a tensor b maps to phi(a)b, and inverse b maps to 1 tensor b.
   The A-balancing relation proves both composites are identities.
3. For the root line use (z tensor a) tensor b maps to z tensor phi(a)b, and inverse
   z tensor b maps to (z tensor 1) tensor b. Inner Z/N-balancing is preserved because
   the residue scalar acts on roots by powers; outer balancing follows from
   multiplicativity of phi. These inverse B-linear maps commute with restrictions and
   sheafify. The generator and inverse-generator equations below specify these maps.
4. Exact constant-coefficient inverse image identifies constant coefficients by their
   constant sections. Its coefficient square commutes. The normalized ringed-derived
   monoidal comparisons, cochain pullback/tensor coherence, and preservation of K-flat
   representatives identify scalarPullbackIso with ordinary scalar association.
5. On an inverse-image root tensor, the two twist-square composites both give
   z' tensor phi(c_A(a)) c_B(b), since c_B(phi(a)b)=phi(c_A(a))c_B(b).
   Equality on these generators gives equality after sheafification, hence equality of
   actual derived morphisms. The pullback data used below are the roots-normalized
   data of lem-asd-etale-finite-twist-pullback.
6. The unit square is the same computation without z. Both sides send the generator
   a tensor b to phi(c_A(a))c_B(b), with the canonical unit comparison.
7. Shift these equal chain maps; B is in degree zero so no additional Koszul sign
   occurs. The exact scalar shift comparison specifies the shifted theta. Additivity
   preserves finite biproducts: define the sum map by its components and use the
   biproduct identities to construct its inverse. This gives both displayed inclusion
   and projection equations, including the empty sum. -/
theorem finiteTateBalancedScalarPullback
    (N : ℕ) (hN : 0 < N) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    ∃ (s : ∀ (T : Scheme.{u}) (i : Bool),
        (ProEtale.etaleSheafExtendScalars φ T).obj (finiteTateBalancedSheaf A N hA T i) ≅
          finiteTateBalancedSheaf B N hB T i)
      (θ : ∀ (T : Scheme.{u}), (∀ t : T, IsUnit (N : T.presheaf.stalk t)) →
        ∀ i : Bool, (scalarExtension φ T).obj (finiteTateBalancedObject A N hA T i) ≅
          finiteTateBalancedObject B N hB T i),
    (∀ (T : Scheme.{u}) (i : Bool) (W : T.Etaleᵒᵖ) (a : A)
        (z : (T.rootsOfUnitySheaf N).obj.obj W),
      ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
        (s T i).hom).hom.app W (finiteTateBalancedGenerator A N hA T i W a z) =
      finiteTateBalancedGenerator B N hB T i W (φ a) z) ∧
    (∀ (T : Scheme.{u}) (i : Bool) (W : T.Etaleᵒᵖ) (b : B)
        (z : (T.rootsOfUnitySheaf N).obj.obj W),
      (s T i).inv.hom.app W (finiteTateBalancedGenerator B N hB T i W b z) =
        b • @id (((ProEtale.etaleSheafExtendScalars φ T).obj
          (finiteTateBalancedSheaf A N hA T i)).obj.obj W)
          (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app
            (finiteTateBalancedSheaf A N hA T i)).hom.app W
              (finiteTateBalancedGenerator A N hA T i W 1 z))) ∧
    (∀ (T : Scheme.{u}) (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t)) (i : Bool),
      (θ T hT i).hom =
        FiniteSmoothPurity.scalarSingleMap φ T (finiteTateBalancedSheaf A N hA T i) ≫
          (_root_.DerivedCategory.singleFunctor _ 0).map (s T i).hom) ∧
    (∀ {T T' : Scheme.{u}} (f : T' ⟶ T)
        (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
        (hT' : ∀ t : T', IsUnit (N : T'.presheaf.stalk t)),
      ∃ (hΓ : IsUnit (N : Γ(T, ⊤))) (hΓ' : IsUnit (N : Γ(T', ⊤))),
      ∀ (i : Bool) (n : ℤ),
        (shiftFunctor _ n).map
          ((scalarPullbackIso φ f).hom.app (finiteTateBalancedObject A N hA T i) ≫
            (scalarExtension φ T').map (finiteTateBalancedPullback A N hN hA f hΓ hΓ' i).hom ≫
              (θ T' hT' i).hom) =
        (shiftFunctor _ n).map
          ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.map (θ T hT i).hom ≫
            (finiteTateBalancedPullback B N hN hB f hΓ hΓ' i).hom)) ∧
    (∀ (T : Scheme.{u}) (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
        (J : Type w) [Fintype J] (i : J → Bool) (n : J → ℤ),
      ∃ c : (scalarExtension φ T).obj (⨁ fun j ↦
          (finiteTateBalancedObject A N hA T (i j))⟦n j⟧) ≅
            ⨁ fun j ↦ (finiteTateBalancedObject B N hB T (i j))⟦n j⟧,
        (∀ j : J,
          (scalarExtension φ T).map (biproduct.ι _ j) ≫ c.hom =
            (finiteTateBalancedShiftIso φ T (θ T hT (i j)) (n j)).hom ≫
              biproduct.ι (fun k ↦
                (finiteTateBalancedObject B N hB T (i k))⟦n k⟧) j) ∧
        (∀ j : J, c.hom ≫ biproduct.π _ j =
          (scalarExtension φ T).map (biproduct.π _ j) ≫
            (finiteTateBalancedShiftIso φ T (θ T hT (i j)) (n j)).hom)) := by
  sorry

end AlgebraicGeometry.Etale
