/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedActionTensor
public import Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Products


/-! # Cubical evaluation inputs and zero maps

Source: current blueprint, direct-images proof, paragraph (3), agent lattice expansion
(blueprint: lem-sfb-koszul-functor-preserves-zero).

All existential data below are pinned by coproduct coordinates, action, boundary and
local evaluation formulas. No object is chosen from the concluding existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar
open CategoryTheory.CondensedDerivedRestriction
namespace Profinite.DiscreteLattice.CubicalEvaluation

/-- Cache the existing canonical sheaf tensor instance in the fixed coefficient sizes.
This is an alias of the imported instance, with no new tensor data.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
instance (priority := 2000) sheafMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- The discrete lattice in the site's object universe.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
abbrev D (r : ℕ) := Multiplicative (Fin r → ULift.{u} ℤ)

/-- Cache the existing topological-group instance for the discrete lattice.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
instance (priority := 2000) latticeTopologicalGroup (r : ℕ) :
    IsTopologicalGroup (D.{u} r) := inferInstance

/-- The canonical lift of an integral lattice vector.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def vector {r : ℕ} (v : Fin r → ℤ) : D.{u} r := Multiplicative.ofAdd (fun i ↦ ⟨v i⟩)

variable (A : CondensedBar.Ring.{u}) (r : ℕ)

/-- Cache the existing relative internal-module tensor in this coefficient category.
It unfolds to the imported canonical tensor and changes no mathematical construction.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
instance (priority := 2000) moduleMonoidal : MonoidalCategory (CondensedBar.Modules A) :=
  inferInstance

section

-- Use the canonical instances directly in these definitions, avoiding alias conversions.
attribute [-instance] sheafMonoidal latticeTopologicalGroup moduleMonoidal

/-- Evaluation on constant lattice sections compares the two recorded action categories.
The normalization retains all section actions, rather than forgetting their continuity.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
structure DiscreteComparison where
  equivalence : CondensedBar.Equivariant A (D r) ≌ DiscreteLattice.Equivariant A.toMon r
  underlying : equivalence.functor ⋙ Action.forget _ _ ≅ CondensedBar.forgetAction
  additive : equivalence.functor.Additive
  action : ∀ (M : CondensedBar.Equivariant A (D r)) (S : Profinite.{u})
      (v : Fin r → ℤ) (x : sections A (equivalence.functor.obj M).V S),
    (underlying.hom.app M).hom.hom.app (op S)
        (((equivalence.functor.obj M).ρ (Multiplicative.ofAdd v)).hom.hom.app (op S) x) =
      (M.act S (ContinuousMap.const S (vector v))).toFun
        ((underlying.hom.app M).hom.hom.app (op S) x)

attribute [instance] DiscreteComparison.additive

/-- The Koszul functor preserves zero maps in the stated subset coordinates.
Source: paragraph (3), proof step 3
(blueprint: lem-sfb-koszul-functor-preserves-zero).
Proof: every matrix entry of the map of a zero morphism is zero by KoszulModel.maps.
Finite biproduct extensionality then identifies the map with the zero chain map. -/
@[instance] theorem koszulZero (K : KoszulModel A.toMon r) :
    K.functor.PreservesZeroMorphisms := by
  constructor
  intro P Q
  apply HomologicalComplex.hom_ext
  intro a
  apply (cancel_epi (K.coordinates P a).inv).1
  apply (cancel_mono (K.coordinates Q a).hom).1
  apply biproduct.hom_ext'
  intro I
  apply biproduct.hom_ext
  intro J
  simpa only [Category.assoc, Action.zero_hom, ite_self, HomologicalComplex.zero_f,
    zero_comp, comp_zero] using K.maps (0 : P ⟶ Q) a I J

/-- Total coproducts exist in the fixed coefficient universe.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
instance hasTotal (B : HomologicalComplex₂ (CondensedBar.Modules A) (.up ℤ) (.up ℤ)) :
    B.HasTotal (.up ℤ) := fun _ ↦ inferInstance

/-- The actual Koszul-first bicomplex, using the recorded finite Koszul complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def bicomplex (B : DiscreteComparison A r) (K : KoszulModel A.toMon r)
    (P : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ) :=
  HomologicalComplex₂.flip
    ((K.functor.mapHomologicalComplex (.up ℤ)).obj
      ((B.equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P))

/-- Direct-sum total with differential d_K + (-1)^a d_P.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def total (B : DiscreteComparison A r) (K : KoszulModel A.toMon r) :
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ ⥤
      CochainComplex (CondensedBar.Modules A) ℤ :=
  B.equivalence.functor.mapHomologicalComplex (.up ℤ) ⋙
    K.functor.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor _ (.up ℤ) (.up ℤ) (.up ℤ)

/-- Cubical labels, empty outside degrees zero through r.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
abbrev Cells (r : ℕ) (a : ℤ) := (Fin r → ℤ) × IntegralLatticeCubical.Directions r a

/-- The underlying internal-module complex, with the existing forgetful functor.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def forgetComplex :
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ ⥤
      CochainComplex (CondensedBar.Modules A) ℤ :=
  (CondensedBar.forgetAction (A := A) (G := D r)).mapHomologicalComplex (.up ℤ)

/-- The degreewise trivial-action functor on actual complexes.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def trivialComplex : CochainComplex (CondensedBar.Modules A) ℤ ⥤
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ :=
  (CondensedAction.trivial (R := A.toMon) (P := D r)).mapHomologicalComplex (.up ℤ)

/-- The canonical underlying comparison for the equivariant tensor unit complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def unitComparison :
    (forgetComplex A r).obj (HomologicalComplex.tensorUnit
      (CondensedBar.Equivariant A (D r)) (.up ℤ)) ≅
        HomologicalComplex.tensorUnit (CondensedBar.Modules A) (.up ℤ) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (CondensedBar.forgetAction (A := A) (G := D r)) (.up ℤ) 0).app (𝟙_ _)) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso
        (actionTensor A (D r)).forgetCore.εIso.symm

attribute [irreducible] unitComparison

/-- A cubical cell, zero when its direction set has the wrong cardinality.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def cell (L : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ)
    (ι : ∀ n : ℤ, Cells r (-n) → (𝟙_ (CondensedBar.Modules A) ⟶ (L.X n).module))
    (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)) :
    𝟙_ (CondensedBar.Modules A) ⟶ (L.X n).module :=
  if h : (I.card : ℤ) = -n then ι n (v, ⟨I, h⟩) else 0

/-- The sign c_a, including its value one in degree zero.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def cSign (a : ℕ) : ℤ := (-1) ^ (a * (a + 1) / 2)

/-- The scaling theta_(a,b), with the integral input degree allowed to be negative.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def theta (a : ℕ) (b : ℤ) : ℤ := (-1 : ℤ) ^ (((a : ℤ) * b).natAbs) * cSign a

/-- Tensor coproducts exist for every pair of action complexes.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
instance tensorExists (P Q : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ) :
    HomologicalComplex.HasTensor P Q := fun _ ↦ inferInstance

/-- The diagonal tensor is closed, hence preserves the empty colimit.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
instance tensorEmpty (M : CondensedBar.Equivariant A (D r)) :
    PreservesColimit (Functor.empty.{0} _) (tensorLeft M) :=
  (Adjunction.ofIsLeftAdjoint (tensorLeft M)).leftAdjoint_preservesColimits
    |>.preservesColimitsOfShape.preservesColimit

/-- The actual tensor augmentation, followed by the canonical right unitor.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def tensorAugmentation
    {L : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ}
    (ε : L ⟶ HomologicalComplex.tensorUnit _ (.up ℤ))
    (P : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ) :
    HomologicalComplex.tensorObj P L ⟶ P :=
  HomologicalComplex.tensorHom (𝟙 P) ε ≫ (HomologicalComplex.rightUnitor P).hom


attribute [irreducible] total bicomplex

end

end Profinite.DiscreteLattice.CubicalEvaluation
