/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison

/-! # Coordinate cup products for a trivial discrete lattice

Source: main-20261015 direct-images proof, paragraph (3), algebraic dense-lattice input;
agent expansion, exact internal-module reference wanted
(blueprint: lem-sfb-discrete-lattice-cup-exterior).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
namespace Profinite.DiscreteLatticeCup

/-- The discrete integer lattice in the site's universe, with its ordered coordinates.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
abbrev Lattice (r : ℕ) := ULift.{u} (Multiplicative (Fin r → ℤ))

variable (A : CategoryTheory.CondensedBar.Ring.{u})

/-- The regular internal module in degree zero, in the recorded ordinary derived category.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def regular : DerivedCategory.{u + 1} (Modules A) :=
  (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)

/-- A summand R[-q]; negative shifts put the coefficient in positive cochain degree q.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def shiftedRegular (q : ℕ) : DerivedCategory.{u + 1} (Modules A) :=
  (regular A)⟦(-(q : ℤ))⟧

/-- The coordinate character is uniquely specified on sections with constant ith coordinate.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior).
Proof: a continuous integer-valued function on a profinite set has finite image. Partition
into its clopen fibres and glue the sections n times 1 of A. Sheaf uniqueness proves
naturality, additivity and uniqueness, by the common refinement of the fibre partitions.
The empty test object has the unique section. This constructs the sectionwise map
(n_1,...,n_r) to n_i times 1 without a topological presentation of A. -/
theorem coordinateCharacter_exists (r : ℕ) (i : Fin r) :
    ∃! a : Character A (Lattice.{u} r),
      ∀ (S : Profinite.{u}) (g : C(S, Lattice.{u} r)) (n : ℤ),
        (∀ s : S, Multiplicative.toAdd (g s).down i = n) →
          a.app S g = (n : sectionRing A S) := by
  sorry

/-- The actual condensed coordinate map, determined by its values on clopen fibres.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def coordinateCharacter (r : ℕ) (i : Fin r) : Character A (Lattice.{u} r) :=
  Classical.choose (coordinateCharacter_exists A r i)

/-- The positive normalized connecting class of the ith coordinate character.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def coordinateClass (r : ℕ) (i : Fin r) :
    shiftedRegular A 1 ⟶ cohomology A (Lattice.{u} r) :=
  characterClass (coordinateCharacter A r i)

/-- The inverse regular multiplication, through the canonical tensor unit.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def regularSplit : regular A ⟶ regular A ⊗ regular A :=
  (λ_ (regular A)).inv ≫ (baseUnitIso A).hom ▷ regular A

/-- The canonical identification R[-(p+q)] with R[-p] tensor R[-q], without permutations.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def splitShift (p q : ℕ) :
    shiftedRegular A (p + q) ⟶ shiftedRegular A p ⊗ shiftedRegular A q :=
  eqToHom (congrArg (fun n : ℤ ↦ (regular A)⟦n⟧) (by omega)) ≫
    (regularSplit A)⟦(-(p : ℤ) + -(q : ℤ))⟧' ≫
    (DerivedCategory.shiftTensorShiftIso (Modules A) (regular A) (regular A)
      (-(p : ℤ)) (-(q : ℤ))).inv

/-- Ordered cups of coordinate classes; the empty word is the derived unit.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def orderedCup (r : ℕ) : (l : List (Fin r)) →
    shiftedRegular A l.length ⟶ cohomology A (Lattice.{u} r)
  | [] => (shiftFunctorZero _ ℤ).hom.app (regular A) ≫
      (baseUnitIso A).inv ≫ cupUnit
  | i :: l =>
      eqToHom (congrArg (shiftedRegular A) (Nat.add_comm l.length 1)) ≫
      splitShift A 1 l.length ≫
      (coordinateClass A r i ⊗ₘ orderedCup r l) ≫ cup

/-- Finite biproducts of complexes use their degreewise finite products.
Source: the ordinary complex category (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
instance complexBiproducts : HasFiniteBiproducts (CochainComplex (Modules A) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The single-term complex attached to one subset of the ordered basis.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def exteriorSummand {r : ℕ} (I : Finset (Fin r)) : CochainComplex (Modules A) ℤ :=
  ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj
    (Mod.regular A.X))⟦(-(I.card : ℤ))⟧

/-- The actual zero-differential exterior complex, as a finite sum of single-term shifts.
Its degree q has one copy of R for each q-element subset of the ordered basis.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def exteriorComplex (r : ℕ) : CochainComplex (Modules A) ℤ :=
  ⨁ (fun I : Finset (Fin r) ↦ exteriorSummand A I)

/-- Localization of the displayed zero-differential complex.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def exteriorObject (r : ℕ) : DerivedCategory.{u + 1} (Modules A) :=
  DerivedCategory.Q.obj (exteriorComplex A r)

/-- The cup map on a subset, in strictly increasing order; the empty subset gives the unit.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def subsetCup (r : ℕ) (I : Finset (Fin r)) :
    shiftedRegular A I.card ⟶ cohomology A (Lattice.{u} r) :=
  eqToHom (congrArg (shiftedRegular A) (I.length_sort (· ≤ ·)).symm) ≫
    orderedCup A r (I.sort (· ≤ ·))

/-- The specified derived arrow: localize the finite sum, then take its ordered cup maps.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def cupMap (r : ℕ) : exteriorObject A r ⟶ cohomology A (Lattice.{u} r) :=
  Functor.biproductComparison DerivedCategory.Q (fun I : Finset (Fin r) ↦
      exteriorSummand A I) ≫
    biproduct.desc (fun I : Finset (Fin r) ↦
      (DerivedCategory.Q.commShiftIso (-(I.card : ℤ))).hom.app
        ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj (Mod.regular A.X)) ≫
      subsetCup A r I)

/-- The coordinate-cup exterior arrow is an isomorphism for every commutative condensed ring.
Source: paragraph (3), algebraic dense-lattice input; agent expansion, reference wanted
(blueprint: lem-sfb-discrete-lattice-cup-exterior).
Proof: (1) Apply lem-sfb-discrete-lattice-koszul-resolution to R with trivial action:
all T_i-1 vanish, giving this exact subset-indexed zero-differential complex. Choose the
triangulated multiplicative comparison of lem-sfb-lattice-koszul-triangulated-cup-comparison.
(2) For coordinate i use the unipotent extension R to R plus R to R, with generator j
acting by (x,y) to (x+1_{j=i}y,y). Split underlying modules by y to (0,y).
(3) lem-sc-p1-split-ses-boundary-comparison computes its boundary as pi d s; its singleton
j component on 1 is 1_{j=i}. Connecting-morphism compatibility of that comparison and
lem-sfb-condensed-derived-restriction-calculus identify the actual derived character
class with the singleton inclusion followed by the comparison.
(4) The comparison's pairing multiplies increasingly ordered singleton inclusions to
the corresponding subset inclusion, with sign +1 and coefficient 1. The empty product
is the invariant unit. Induction identifies every subsetCup with that comparison.
(5) The finite biproduct universal property identifies cupMap with the comparison,
hence it is invertible. Rank zero has only the empty subset and gives the identity
under the unit identification. The zero ring gives zero objects throughout; no integer
is divided out and no flatness, completeness or characteristic assumption is used. -/
theorem discrete_lattice_cup_exterior (r : ℕ) : IsIso (cupMap A r) := by
  sorry

/-- The canonical inclusion of the unique empty-subset summand in rank zero.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior). -/
def rankZeroInclusion : regular A ⟶ exteriorObject A 0 :=
  DerivedCategory.Q.map
    ((shiftFunctorZero (CochainComplex (Modules A) ℤ) ℤ).inv.app
      ((HomologicalComplex.single (Modules A) (.up ℤ) 0).obj (Mod.regular A.X))) ≫
    DerivedCategory.Q.map
      (biproduct.ι (fun I : Finset (Fin 0) ↦ exteriorSummand A I) ∅)

/-- In rank zero the cup arrow is the identity of R[0] under the canonical unit
identifications, with both identifications retained in the statement.
Source: paragraph (3) (blueprint: lem-sfb-discrete-lattice-cup-exterior).
Proof: the trivial group fixes every section, so its invariant-inclusion adjunction is
the identity adjunction. Its derived unit is therefore an isomorphism identifying
cupUnit with the regular-ring unit. The only subset of Fin 0 is empty. Expanding the
finite-sum inclusion and cupMap leaves the empty ordered cup, which is this same unit.
Composing with its normalized inverse gives the identity, including for the zero ring. -/
theorem rank_zero_identity :
    ∃ e : cohomology A (Lattice.{u} 0) ≅ regular A,
      cupUnit ≫ e.hom = (baseUnitIso A).hom ∧
      rankZeroInclusion A ≫ cupMap A 0 ≫ e.hom = 𝟙 (regular A) := by
  sorry

end Profinite.DiscreteLatticeCup
