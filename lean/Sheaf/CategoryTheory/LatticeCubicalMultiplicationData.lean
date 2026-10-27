/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module


public import Sheaf.CategoryTheory.LatticeCubicalAugmentationEvaluation
public import Sheaf.CategoryTheory.LatticeFlatTwistedChainPairing
public import Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal

/-! # Cubical multiplication roof data

Source: current blueprint, direct-images proof, paragraph (3), agent lattice expansion,
steps 12--14 (blueprint: lem-sfb-lattice-cubical-multiplication-roof).

The roof constructions are first elaborated in an abstract monoidal category. Their
specialization uses the recorded signed cochain tensor, Koszul pairing, cubical model
and normalized equivalence between generalized-section and discrete lattice actions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace Profinite.DiscreteLattice.CubicalMultiplication

/-- The three evaluation-roof maps. All normalization conditions are imposed by the
concluding theorem; the structure itself assumes none of the claimed identities.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
structure Roof {V : Type v} [Category.{w} V] [MonoidalCategory V] (X L Z : V) where
  augmentation : L ⟶ 𝟙_ V
  diagonal : L ⟶ L ⊗ L
  evaluation : X ⊗ L ⟶ Z

namespace Roof
variable {V : Type v} [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {X L Z : V} (F : Roof X L Z)

/-- The actual middle interchange, with its ambient signed braiding and associators.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def comparison : (X ⊗ X) ⊗ L ⟶ (X ⊗ L) ⊗ (X ⊗ L) :=
  (𝟙 (X ⊗ X) ⊗ₘ F.diagonal) ≫ tensorμ X X L L

/-- The first denominator, with the canonical right unitor.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def a : (X ⊗ X) ⊗ L ⟶ X ⊗ X :=
  (𝟙 (X ⊗ X) ⊗ₘ F.augmentation) ≫ (ρ_ (X ⊗ X)).hom

/-- The second denominator, with the two canonical right unitors.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def b : (X ⊗ L) ⊗ (X ⊗ L) ⟶ X ⊗ X :=
  ((𝟙 X ⊗ₘ F.augmentation) ≫ (ρ_ X).hom) ⊗ₘ
    ((𝟙 X ⊗ₘ F.augmentation) ≫ (ρ_ X).hom)

/-- The first evaluation numerator uses the prescribed Koszul product.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def f (star : X ⊗ X ⟶ X) : (X ⊗ X) ⊗ L ⟶ Z :=
  (star ⊗ₘ 𝟙 L) ≫ F.evaluation

/-- The second numerator uses original algebra multiplication.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def g (mul : Z ⊗ Z ⟶ Z) : (X ⊗ L) ⊗ (X ⊗ L) ⟶ Z :=
  (F.evaluation ⊗ₘ F.evaluation) ≫ mul

/-- The exact chain-map, counit, common-denominator and unit equations of the node.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def Identities (star : X ⊗ X ⟶ X) (unit : 𝟙_ V ⟶ X)
    (mul : Z ⊗ Z ⟶ Z) (eta : 𝟙_ V ⟶ Z) : Prop :=
  (F.diagonal ≫ (F.augmentation ⊗ₘ 𝟙 L) ≫ (λ_ L).hom = 𝟙 L) ∧
  (F.diagonal ≫ (𝟙 L ⊗ₘ F.augmentation) ≫ (ρ_ L).hom = 𝟙 L) ∧
  (F.diagonal ≫ (F.augmentation ⊗ₘ F.augmentation) ≫ (λ_ (𝟙_ V)).hom =
    F.augmentation) ∧
  F.f star = F.comparison ≫ F.g mul ∧
  F.comparison ≫ F.b = F.a ∧
  (unit ⊗ₘ 𝟙 L) ≫ F.evaluation = (λ_ L).hom ≫ F.augmentation ≫ eta

/-- Equality of the two roofs with precisely the displayed localized denominators.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def Localized {W : Type v'} [Category.{w'} W] (Q : V ⥤ W)
    (star : X ⊗ X ⟶ X) (mul : Z ⊗ Z ⟶ Z) : Prop :=
  ∃ (a' : Q.obj ((X ⊗ X) ⊗ L) ≅ Q.obj (X ⊗ X))
    (b' : Q.obj ((X ⊗ L) ⊗ (X ⊗ L)) ≅ Q.obj (X ⊗ X)),
    a'.hom = Q.map F.a ∧ b'.hom = Q.map F.b ∧
    a'.inv ≫ Q.map (F.f star) = b'.inv ≫ Q.map (F.g mul)
end Roof

/-- Cache the existing signed tensor on action cochain complexes, without new data.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
instance (priority := 3000) complexMonoidal (R : CategoryTheory.CondensedBar.Ring.{u})
    (r : ℕ) : MonoidalCategory (CochainComplex (Equivariant R.toMon r) ℤ) :=
  DerivedCup.actionComplexMonoidal R.toMon r

/-- Cache the projection of the same canonical signed tensor.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
instance (priority := 3000) complexMonoidalStruct (R : CategoryTheory.CondensedBar.Ring.{u})
    (r : ℕ) : MonoidalCategoryStruct (CochainComplex (Equivariant R.toMon r) ℤ) :=
  (complexMonoidal R r).toMonoidalCategoryStruct

variable (R : CategoryTheory.CondensedBar.Ring.{u}) (r : ℕ)
    (J : CubicalEvaluation.DiscreteComparison R r)
    (C : CubicalEvaluation.CubicalModel R r)
    (K : KoszulModel R.toMon r) (B : DerivedCup.Algebra R.toMon r)

/-- The existing cubical complex in normalized discrete-action coordinates.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def lattice := (J.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj C.L

/-- The actual transported cell inclusion, zero for the wrong direction cardinality.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def cell (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)) :
    𝟙_ (Modules R.toMon) ⟶ ((lattice R r J C).X n).V :=
  CubicalEvaluation.cell R r C.L C.ι n v I ≫ J.underlying.inv.app (C.L.X n)

attribute [irreducible] lattice

/-- Ordinary tensor-total summand inclusion; wrong total degrees give zero.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def inclusion (X Y : CochainComplex (Equivariant R.toMon r) ℤ) (a b n : ℤ) :
    (X.X a).V ⊗ (Y.X b).V ⟶ ((X ⊗ Y).X n).V :=
  (HomologicalComplex.ιMapBifunctorOrZero X Y
    (curriedTensor (Equivariant R.toMon r)) (.up ℤ) a b n).hom

/-- The tensor of two actual cubical cells, in signed total degree n.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def cellTensor (n : ℤ) (v w : Fin r → ℤ) (A B' : Finset (Fin r)) :
    𝟙_ (Modules R.toMon) ⟶ ((lattice R r J C ⊗ lattice R r J C).X n).V :=
  (λ_ (𝟙_ (Modules R.toMon))).inv ≫
    (cell R r J C (-(A.card : ℤ)) v A ⊗ₘ cell R r J C (-(B'.card : ℤ)) w B') ≫
    inclusion R r (lattice R r J C) (lattice R r J C)
      (-(A.card : ℤ)) (-(B'.card : ℤ)) n

/-- The specified trivial-action Koszul complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def koszul := FlatTwisted.trivialKoszul K B

/-- The original algebra placed in degree zero.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def algebra := (HomologicalComplex.single (Equivariant R.toMon r) (.up ℤ) 0).obj B.X

/-- The specified Koszul coefficient inclusion.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def coefficient (p : ℤ) (A : Subsets r p) : B.X.V ⟶ ((koszul R r K B).X p).V :=
  biproduct.ι (fun _ : Subsets r p ↦ B.X.V) A ≫ (K.coordinates B.X p).inv

variable (P : FlatTwisted.Pairing K B)

/-- Inflate the original star with the canonical strong tensor comparison.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def star : koszul R r K B ⊗ koszul R r K B ⟶ koszul R r K B :=
  Functor.LaxMonoidal.μ ((DerivedCup.trivial R.toMon r).mapHomologicalComplex (.up ℤ))
    (K.functor.obj B.X) (K.functor.obj B.X) ≫
      ((DerivedCup.trivial R.toMon r).mapHomologicalComplex (.up ℤ)).map P.star

/-- Inflate the original unit with the canonical strong tensor comparison.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def unit : 𝟙_ (CochainComplex (Equivariant R.toMon r) ℤ) ⟶ koszul R r K B :=
  Functor.LaxMonoidal.ε ((DerivedCup.trivial R.toMon r).mapHomologicalComplex (.up ℤ)) ≫
    ((DerivedCup.trivial R.toMon r).mapHomologicalComplex (.up ℤ)).map P.unit

/-- The original algebra multiplication on the degree-zero tensor complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def mul : algebra R r B ⊗ algebra R r B ⟶ algebra R r B :=
  eqToHom (DerivedCup.cochainTensor_eq R.toMon r _ _).symm ≫
    DerivedCup.singleMultiplication R.toMon r B

/-- The original algebra unit on degree-zero complexes.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def eta : 𝟙_ (CochainComplex (Equivariant R.toMon r) ℤ) ⟶ algebra R r B :=
  (HomologicalComplex.single (Equivariant R.toMon r) (.up ℤ) 0).map (MonObj.one (X := B.X))

attribute [irreducible] koszul star unit mul eta

/-- The supported source summand of the multiplication evaluation numerator.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def supported (p q : ℕ) (A : Subsets r (p : ℤ)) (A' : Subsets r (q : ℤ))
    (v : Fin r → ℤ) (I : Subsets r ((p : ℤ) + q)) :
    (B.X.V ⊗ B.X.V) ⊗ 𝟙_ (Modules R.toMon) ⟶
      (((koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C).X 0).V :=
  (((coefficient R r K B p A ⊗ₘ coefficient R r K B q A') ≫
    inclusion R r (koszul R r K B) (koszul R r K B) p q ((p : ℤ) + q)) ⊗ₘ
    cell R r J C (-((p : ℤ) + q)) v I.val) ≫
      inclusion R r (koszul R r K B ⊗ koszul R r K B) (lattice R r J C)
        ((p : ℤ) + q) (-((p : ℤ) + q)) 0

/-- The precise coefficient, zero unless the directions form the specified partition.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def value (p q : ℕ) (A : Subsets r (p : ℤ)) (A' : Subsets r (q : ℤ))
    (v : Fin r → ℤ) (I : Subsets r ((p : ℤ) + q)) :
    (B.X.V ⊗ B.X.V) ⊗ 𝟙_ (Modules R.toMon) ⟶ B.X.V :=
  if Disjoint A.val A'.val ∧ A.val ∪ A'.val = I.val then
    (CubicalEvaluation.cSign (p + q) * IntegralLatticeCubical.partitionSign r A.val A'.val) •
      ((ρ_ (B.X.V ⊗ B.X.V)).hom ≫
        (B.X.ρ (Multiplicative.ofAdd v) ⊗ₘ
          B.X.ρ (Multiplicative.ofAdd (v + IntegralLatticeCubical.directionSum r A.val))) ≫
            (MonObj.mul (X := B.X)).hom)
  else 0

/-- A product component in the already specified Koszul coordinates.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-multiplication-roof). -/
def productCoordinate (p q : ℤ) (A : Subsets r p) (A' : Subsets r q)
    (I : Subsets r (p + q)) : B.X.V ⊗ B.X.V ⟶ B.X.V :=
  (((biproduct.ι (fun _ : Subsets r p ↦ B.X.V) A ≫ (K.coordinates B.X p).inv) ⊗ₘ
      (biproduct.ι (fun _ : Subsets r q ↦ B.X.V) A' ≫ (K.coordinates B.X q).inv)) ≫
    HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl) ≫ P.star.f (p + q) ≫
      (K.coordinates B.X (p + q)).hom ≫ biproduct.π _ I

/-- Normalization on the generating cells and Koszul coefficient summands.
These equations determine the three maps; no auxiliary existence choice is used in a definition.
Source: direct-images paragraph (3), cubical comparison steps 1--3
(blueprint: def-sfb-lattice-cubical-multiplication-data). -/
def Normalized
    (F : Roof (koszul R r K B) (lattice R r J C) (algebra R r B)) : Prop :=
    (∀ v : Fin r → ℤ, cell R r J C 0 v ∅ ≫ (F.augmentation.f 0).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (𝟙_ (Equivariant R.toMon r))).hom.hom = 𝟙 _) ∧
    (∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)), (I.card : ℤ) = -n →
      cell R r J C n v I ≫ (F.diagonal.f n).hom =
        ∑ A ∈ I.powerset, IntegralLatticeCubical.partitionSign r A (I \ A) •
          cellTensor R r J C n v
            (v + IntegralLatticeCubical.directionSum r A) A (I \ A)) ∧
    (∀ (p : ℕ) (A : Subsets r (p : ℤ)) (v : Fin r → ℤ) (I : Subsets r (p : ℤ)),
      (coefficient R r K B p A ⊗ₘ cell R r J C (-(p : ℤ)) v I.val) ≫
        inclusion R r (koszul R r K B) (lattice R r J C) p (-(p : ℤ)) 0 ≫
        (F.evaluation.f 0).hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B.X).hom.hom =
      if A = I then CubicalEvaluation.cSign p •
        ((ρ_ B.X.V).hom ≫ B.X.ρ (Multiplicative.ofAdd v)) else 0) ∧
    (F.diagonal ≫ (F.augmentation ⊗ₘ 𝟙 (lattice R r J C)) ≫
      (λ_ (lattice R r J C)).hom = 𝟙 _) ∧
    (F.diagonal ≫ (𝟙 (lattice R r J C) ⊗ₘ F.augmentation) ≫
      (ρ_ (lattice R r J C)).hom = 𝟙 _) ∧
    (F.diagonal ≫ (F.augmentation ⊗ₘ F.augmentation) ≫
      (λ_ (𝟙_ (CochainComplex (Equivariant R.toMon r) ℤ))).hom = F.augmentation)

/-- Acyclic-tensor tests and the canonical derived tensor comparisons for the three
ordinary tensor representatives used in the roof.
Source: direct-images paragraph (3), step 5
(blueprint: def-sfb-lattice-cubical-multiplication-data). -/
def TensorRepresentatives : Prop :=
    (∀ W : CochainComplex (Equivariant R.toMon r) ℤ,
      (W = koszul R r K B ⊗ koszul R r K B ∨
        W = (koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C ∨
        W = (koszul R r K B ⊗ lattice R r J C) ⊗ (koszul R r K B ⊗ lattice R r J C)) →
      ∀ V : CochainComplex (Equivariant R.toMon r) ℤ,
        V.Acyclic → (W ⊗ V).Acyclic) ∧
    (∀ W V : CochainComplex (Equivariant R.toMon r) ℤ,
      (W = koszul R r K B ⊗ koszul R r K B ∨
        W = (koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C ∨
        W = (koszul R r K B ⊗ lattice R r J C) ⊗ (koszul R r K B ⊗ lattice R r J C)) →
      (V = koszul R r K B ⊗ koszul R r K B ∨
        V = (koszul R r K B ⊗ koszul R r K B) ⊗ lattice R r J C ∨
        V = (koszul R r K B ⊗ lattice R r J C) ⊗ (koszul R r K B ⊗ lattice R r J C)) →
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} W V))

end Profinite.DiscreteLattice.CubicalMultiplication
