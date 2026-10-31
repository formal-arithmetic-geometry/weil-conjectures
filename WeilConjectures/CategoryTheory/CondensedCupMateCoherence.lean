/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedScalarTensor
import WeilConjectures.CategoryTheory.CondensedRestrictionMateNormalization
import WeilConjectures.CategoryTheory.ActionToposGeometricRestriction
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Tensor-of-counits coherence for condensed derived invariants

Source: current blueprint, direct-image stability proof, paragraph (3), dense-lattice
input; the agent-formulated cup and restriction mate calculation recorded in the DAG
(blueprint: lem-sfb-condensed-cup-mate-coherence).

The action restriction comparisons below retain their ordinary pure-tensor normalization
and their computation equation on total complexes. Scalar restriction uses the balanced
comparison and never requires a restricted K-flat complex to remain K-flat.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate)
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}} {G H : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Ordinary restriction tensorators are identity on underlying relative tensors and units.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def GroupTensorModel (v : H →ₜ* G) (c : (inflate (R := A.toMon) v).CoreMonoidal) : Prop :=
  (∀ M N : Equivariant A G, (c.μIso M N).hom.val =
    ((actionTensor A H).forgetCore.μIso
      ((inflate (R := A.toMon) v).obj M) ((inflate (R := A.toMon) v).obj N)).inv ≫
        ((actionTensor A G).forgetCore.μIso M N).hom) ∧
  c.εIso.hom.val = (actionTensor A H).forgetCore.εIso.inv ≫
    (actionTensor A G).forgetCore.εIso.hom

/-- The ordinary restriction comparison is uniquely fixed by its underlying identity.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence).
Proof: restriction changes only the section action. The tensor identity is equivariant
for the diagonal actions. The unit identity is equivariant for the trivial regular
module. The faithful forgetful functor verifies coherence and uniqueness. -/
theorem groupTensorExist (v : H →ₜ* G) :
    ∃! c : (inflate (R := A.toMon) v).CoreMonoidal, GroupTensorModel (A := A) v c := by
  sorry

/-- The unique ordinary identity comparison for action restriction.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def groupTensor (A : CondensedBar.Ring.{u}) (v : H →ₜ* G) :
    (inflate (R := A.toMon) v).CoreMonoidal := Classical.choose (groupTensorExist v)

/-- Ordinary restriction with its uniquely normalized strong tensor structure.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
instance groupOrdinaryMonoidal (v : H →ₜ* G) : (inflate (R := A.toMon) v).Monoidal :=
  (groupTensor A v).toMonoidal

/-- The derived restriction comparison is fixed on each total-complex summand and unit.
The equation uses the canonical localization tensor maps, even when not invertible.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def GroupDerivedTensorModel (v : H →ₜ* G) (c : (groupDerived A v).CoreMonoidal) : Prop :=
  (∀ P Q : CochainComplex (Equivariant A G) ℤ,
    ∃ k : ((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q),
      (∀ (p q n : ℤ) (h : p + q = n),
        HomologicalComplex.ιTensorObj
            (((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj P)
            (((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫
          k.f n = Functor.LaxMonoidal.μ (inflate (R := A.toMon) v) (P.X p) (Q.X q) ≫
            (inflate (R := A.toMon) v).map (HomologicalComplex.ιTensorObj P Q p q n h)) ∧
      (c.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
          (groupDerived A v).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) =
        ((inflate (R := A.toMon) v).mapDerivedCategoryFactors.hom.app P ⊗ₘ
          (inflate (R := A.toMon) v).mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj P)
          (((inflate (R := A.toMon) v).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map k ≫
        (inflate (R := A.toMon) v).mapDerivedCategoryFactors.inv.app (P ⊗ Q)) ∧
  c.εIso.hom ≫ (groupDerived A v).map (Functor.LaxMonoidal.ε DerivedCategory.Q) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map
          (Functor.LaxMonoidal.ε (inflate (R := A.toMon) v)) ≫
          ((HomologicalComplex.singleMapHomologicalComplex (inflate (R := A.toMon) v)
            (.up ℤ) 0).app (𝟙_ (Equivariant A G))).inv) ≫
      (inflate (R := A.toMon) v).mapDerivedCategoryFactors.inv.app
        (𝟙_ (CochainComplex (Equivariant A G) ℤ))

/-- Exact restriction has the unique derived identity tensor and regular-unit comparisons.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence).
Proof: realize restriction as the exact pullback between the ringed action sites, by
lem-sfb-action-topos-geometric-restriction. The ringed derived comparison theorem
supplies the K-flat tensorator, whose computation square is the displayed square.
The summand-normalized total map is unique by the total coproduct universal property.
Flat resolutions determine all components, and localizing the regular unit fixes the
unit; hence the strong comparison is unique. -/
theorem groupDerivedTensorExist (v : H →ₜ* G) :
    ∃! c : (groupDerived A v).CoreMonoidal, GroupDerivedTensorModel v c := by
  sorry

/-- Canonical strong derived restriction, selected by its full computation normalization.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def groupDerivedTensor (A : CondensedBar.Ring.{u}) (v : H →ₜ* G) :
    (groupDerived A v).CoreMonoidal := Classical.choose (groupDerivedTensorExist v)

/-- The representative-normalized derived restriction tensor structure.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
instance groupDerivedMonoidal (v : H →ₜ* G) : (groupDerived A v).Monoidal :=
  (groupDerivedTensor A v).toMonoidal

/-- Scalar restriction of actions has the balanced underlying comparison and ring-map unit.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def ScalarActionTensorModel (a : A ⟶ A')
    (m : (scalarAction (G := G) a).functor.LaxMonoidal) : Prop :=
  (∀ M N : Equivariant A' G,
    (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (scalarAction a).functor m M N).val ≫
        (scalarAction a).underlying.hom.app (M ⊗ N) =
      ((actionTensor A G).forgetCore.μIso
        ((scalarAction a).functor.obj M) ((scalarAction a).functor.obj N)).inv ≫
      ((scalarAction a).underlying.hom.app M ⊗ₘ (scalarAction a).underlying.hom.app N) ≫
      Functor.LaxMonoidal.μ (scalarModules a) M.module N.module ≫
      (scalarModules a).map ((actionTensor A' G).forgetCore.μIso M N).hom) ∧
  (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (scalarAction a).functor m).val ≫
      (scalarAction a).underlying.hom.app (𝟙_ (Equivariant A' G)) =
    (actionTensor A G).forgetCore.εIso.inv ≫ Functor.LaxMonoidal.ε (scalarModules a) ≫
      (scalarModules a).map (actionTensor A' G).forgetCore.εIso.hom

/-- The balanced scalar comparison is uniquely equivariant for the diagonal action.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence).
Proof: the underlying balanced map sends x tensor y to the same pure tensor over A'.
The diagonal action commutes with it. The scalar unit is the regular ring map, which
has trivial action. The faithful forgetful functor detects the lax coherence equations
and uniqueness, using the scalarTensorExist balanced universal property. -/
theorem scalarActionTensorExist (a : A ⟶ A') :
    ∃! m : (scalarAction (G := G) a).functor.LaxMonoidal, ScalarActionTensorModel a m := by
  sorry

/-- The unique balanced ordinary action-scalar tensor structure.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
instance scalarActionLax (a : A ⟶ A') : (scalarAction (G := G) a).functor.LaxMonoidal :=
  Classical.choose (scalarActionTensorExist a)

/-- The scalar-action comparison uses the same summand and localization equations as
scalarBase, with its canonical balanced action comparison. No restricted complex is
assumed K-flat over the smaller coefficient ring.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def ScalarActionDerivedTensorModel (a : A ⟶ A')
    (m : (scalarDerived a G).LaxMonoidal) : Prop :=
  (∀ P Q : CochainComplex (Equivariant A' G) ℤ,
    ∃ k : ((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q),
      (∀ (p q n : ℤ) (h : p + q = n),
        HomologicalComplex.ιTensorObj
            (((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj P)
            (((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj Q) p q n h ≫
          k.f n = Functor.LaxMonoidal.μ (scalarAction (G := G) a).functor (P.X p) (Q.X q) ≫
            (scalarAction (G := G) a).functor.map (HomologicalComplex.ιTensorObj P Q p q n h)) ∧
      @Functor.LaxMonoidal.μ _ _ _ _ _ _ (scalarDerived a G) m
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          (scalarDerived a G).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) =
        ((scalarAction (G := G) a).functor.mapDerivedCategoryFactors.hom.app P ⊗ₘ
          (scalarAction (G := G) a).functor.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj P)
          (((scalarAction (G := G) a).functor.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map k ≫
        (scalarAction (G := G) a).functor.mapDerivedCategoryFactors.inv.app (P ⊗ Q)) ∧
  @Functor.LaxMonoidal.ε _ _ _ _ _ _ (scalarDerived a G) m ≫
      (scalarDerived a G).map (Functor.LaxMonoidal.ε DerivedCategory.Q) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.single _ (.up ℤ) 0).map
          (Functor.LaxMonoidal.ε (scalarAction (G := G) a).functor) ≫
          ((HomologicalComplex.singleMapHomologicalComplex (scalarAction (G := G) a).functor
            (.up ℤ) 0).app (𝟙_ (Equivariant A' G))).inv) ≫
      (scalarAction (G := G) a).functor.mapDerivedCategoryFactors.inv.app
        (𝟙_ (CochainComplex (Equivariant A' G) ℤ))

/-- Unique derived scalar-action lax structure with the balanced computation equation.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence).
Proof: on K-flat A'-models invert the target A'-tensor localization comparison; retain
the generally noninvertible A-tensor localization comparison on the restricted models.
Compose it with the summand-normalized balanced chain map. The ordinary equations descend
to lax associativity and both unit equations. K-flat localization determines the natural
transformation uniquely. This is the action-site version of scalarLax, with no flatness
hypothesis on a and no flatness assertion about scalar-restricted models. -/
theorem scalarActionDerivedTensorExist (a : A ⟶ A') :
    ∃! m : (scalarDerived a G).LaxMonoidal, ScalarActionDerivedTensorModel a m := by
  sorry

/-- The uniquely normalized derived scalar restriction on actions.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
instance scalarActionDerivedLax (a : A ⟶ A') : (scalarDerived a G).LaxMonoidal :=
  Classical.choose (scalarActionDerivedTensorExist a)

/-- The tensor and unit transposes specifying the lax invariant functor structure.
Source: paragraph (3) (blueprint: lem-sfb-condensed-cup-mate-coherence). -/
def CounitMateModel (m : (derived A G).LaxMonoidal) : Prop :=
  (∀ X Y : DerivedCategory.{u + 1} (Equivariant A G),
    ((adjunction A G).homEquiv _ _).symm
        (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (derived A G) m X Y) =
      Functor.OplaxMonoidal.δ (trivialDerived A G)
        ((derived A G).obj X) ((derived A G).obj Y) ≫
          ((adjunction A G).counit.app X ⊗ₘ (adjunction A G).counit.app Y)) ∧
  ((adjunction A G).homEquiv _ _).symm
      (@Functor.LaxMonoidal.ε _ _ _ _ _ _ (derived A G) m) =
    Functor.OplaxMonoidal.η (trivialDerived A G)

/-- Tensor-of-counits coherence, group and arbitrary coefficient functoriality, and
preservation of every ordered finite cup product, including its empty unit.
Source: current direct-images proof paragraph (3), dense-lattice input, DAG proof
steps 1--12 (blueprint: lem-sfb-condensed-cup-mate-coherence).
Proof:
1. Present base and action modules on their ringed sites. The action-site pullbacks
   are trivial inflation and continuous-group restriction. Apply the normalized ringed
   derived comparisons to get the prescribed strong symmetric tensorators; their
   ordinary pure-tensor identity fixes the derived model and regular unit.
2. Apply lem-sfb-monoidal-adjunction-mates to the actual adjunction. The Hom bijection
   gives the displayed transposes, uniqueness, lax associativity and both unit laws.
   lem-sfb-monoidal-adjunction-unit-counit makes the actual unit and counit monoidal.
3. Use lem-sfb-condensed-restriction-mate-normalization to transpose the two group
   tensor composites. The monoidal equation for L_H -> U L_G and naturality of the
   restriction tensorator cancel the two U tensorators, leaving the same tensor of
   counits. Injectivity of the Hom bijection gives the tensor equation.
4. The same transpose calculation on the regular unit gives group unit preservation.
5. Apply lem-sfb-derived-scalar-lax-normalization on base and action sites. The scalar
   structures are the fixed balanced ones, with the generally noninvertible tensor
   localization comparison retained. No coefficient flatness is used.
6. The normalized scalar-extension/trivial-action square has a monoidal left
   comparison. lem-sfb-condensed-scalar-restriction-interchange identifies its right
   conjugate with the computation-unit-normalized scalarComparison.
7. The composite-adjunction unit and counit are composites of whiskered monoidal
   units and counits, by def-weil-pbc-composite-adjunction.
8. Expand the conjugate using def-weil-pbc-adjunction-conjugate. Its three factors
   are the monoidal composite unit, inverse left comparison and composite counit.
   Their tensor and unit equations compose to the scalar monoidality equation.
9. Apply the invariant lax structure to the coefficient-unit algebra: its lax
   associativity and unit equations give the cup algebra laws. The group equations
   give a map of these algebras under coefficientRestriction.
10. The regular scalar map is the scalar lax unit and is multiplicative on pure
    tensors. Applying F and then the monoidal scalar comparison gives coefficient
    multiplicativity and its actual unit equation.
11. Induct on right-associated length. Length zero is the unit equation; the
    successor uses binary multiplicativity, tensor naturality and the induction
    hypothesis. The order is unchanged and no braiding is used.
12. Precompose these derived-arrow equalities with tensors of homogeneous class
    arrows using the fixed signed shift extractions. The group and scalar comparisons
    commute with shifts. By lem-weil-pbc-derived-tensor-shift-descent the second-factor
    extraction on degree p has sign (-1)^(np) on both sides; the first is unsigned.
    The ordered equalities therefore retain exactly the specified comparisons. -/
theorem cupMateCoherence (v : H →ₜ* G) (a : A ⟶ A') :
    (∀ X Y : DerivedCategory.{u + 1} (Modules A),
      Functor.LaxMonoidal.μ (trivialDerived A G) X Y ≫
          (trivialDerived A G).map
            ((DerivedCategory.braidedCategory' (Modules A)).braiding X Y).hom =
        ((DerivedCategory.braidedCategory' (Equivariant A G)).braiding
            ((trivialDerived A G).obj X) ((trivialDerived A G).obj Y)).hom ≫
          Functor.LaxMonoidal.μ (trivialDerived A G) Y X) ∧
    (∀ m : (derived A G).LaxMonoidal,
      CounitMateModel m ↔ m = derivedLax (A := A) (G := G)) ∧
    NatTrans.IsMonoidal (adjunction A G).unit ∧
    NatTrans.IsMonoidal (adjunction A G).counit ∧
    NatTrans.IsMonoidal (groupMap A v) ∧
    NatTrans.IsMonoidal (scalarComparison (G := G) a).hom ∧
    NatTrans.CommShift (groupMap A v) ℤ ∧
    NatTrans.CommShift (scalarComparison (G := G) a).hom ℤ ∧
    ((cup (A := A) (G := G) ▷ cohomology A G) ≫ cup (A := A) (G := G) =
      (α_ (cohomology A G) (cohomology A G) (cohomology A G)).hom ≫
        (cohomology A G ◁ cup (A := A) (G := G)) ≫ cup (A := A) (G := G)) ∧
    ((cupUnit (A := A) (G := G) ▷ cohomology A G) ≫ cup (A := A) (G := G) =
      (λ_ (cohomology A G)).hom) ∧
    ((cohomology A G ◁ cupUnit (A := A) (G := G)) ≫ cup (A := A) (G := G) =
      (ρ_ (cohomology A G)).hom) ∧
    (cup (A := A) (G := G) ≫ groupCupMap (A := A) v =
      (groupCupMap (A := A) v ⊗ₘ groupCupMap (A := A) v) ≫ cup (A := A) (G := H)) ∧
    (cupUnit (A := A) (G := G) ≫ groupCupMap (A := A) v =
      cupUnit (A := A) (G := H)) ∧
    (cup (A := A) (G := G) ≫ coefficientCupMap (G := G) a =
      (coefficientCupMap (G := G) a ⊗ₘ coefficientCupMap (G := G) a) ≫
        Functor.LaxMonoidal.μ (scalarBase a) (cohomology A' G) (cohomology A' G) ≫
        (scalarBase a).map (cup (A := A') (G := G))) ∧
    (cupUnit (A := A) (G := G) ≫ coefficientCupMap (G := G) a =
      Functor.LaxMonoidal.ε (scalarBase a) ≫
        (scalarBase a).map (cupUnit (A := A') (G := G))) ∧
    (∀ n : ℕ,
      orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) n ≫
          groupCupMap (A := A) v =
        tensorPowerMap (groupCupMap (A := A) v) n ≫
          orderedProduct (cupUnit (A := A) (G := H)) (cup (A := A) (G := H)) n) ∧
    (∀ n : ℕ,
      orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) n ≫
          coefficientCupMap (G := G) a =
        tensorPowerMap (coefficientCupMap (G := G) a) n ≫
          orderedProduct
            (Functor.LaxMonoidal.ε (scalarBase a) ≫
              (scalarBase a).map (cupUnit (A := A') (G := G)))
            (Functor.LaxMonoidal.μ (scalarBase a) (cohomology A' G) (cohomology A' G) ≫
              (scalarBase a).map (cup (A := A') (G := G))) n) := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
