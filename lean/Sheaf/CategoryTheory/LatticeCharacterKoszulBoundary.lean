/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison

/-! # Coordinate characters and positive Koszul boundaries

Source: blueprint direct-image stability proof, paragraph (3), algebraic lattice
normalization, expanded in the node's six proof steps; Stacks Tags 011J and 0152
(blueprint: lem-sfb-lattice-character-koszul-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace Profinite.DiscreteLattice
namespace CharacterBoundary

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)

/-- The existing exact identity derived functor has its canonical shift comparison.
Source: the ordinary derived-category localization convention, paragraph (3)
(blueprint: lem-sfb-lattice-character-koszul-boundary). -/
instance raiseCommShift : (RestrictionCup.raise R).CommShift ℤ := by
  unfold RestrictionCup.raise
  infer_instance

/-- The existing positive character class, transported by the recorded normalized bridge.
Only the localization universe and action presentation change; no class is chosen.
Source: paragraph (3), node proof step 5
(blueprint: lem-sfb-lattice-character-koszul-boundary). -/
def transportCharacterClass (B : RestrictionCup.Bridge R r)
    (a : CategoryTheory.CondensedDerivedRestriction.Character
      (RestrictionCup.ring R) (ULift.{u} (Group r))) :
    ((DerivedCategory.singleFunctor.{u + 2} (Modules R) 0).obj
        (𝟙_ (Modules R)))⟦(-1 : ℤ)⟧ ⟶
      (derivedInvariants R r).obj ((DerivedCategory.singleFunctor _ 0).obj
        (RestrictionCup.regularAlgebra R r).X) :=
  ((RestrictionCup.raiseFactors R).inv.app
      ((CochainComplex.singleFunctor (Modules R) 0).obj (𝟙_ (Modules R))))⟦(-1 : ℤ)⟧' ≫
    ((RestrictionCup.raise R).commShiftIso (-1 : ℤ)).inv.app _ ≫
      (RestrictionCup.raise R).map
        (CategoryTheory.CondensedDerivedRestriction.characterClass a) ≫
      (RestrictionCup.cohomologyIso R r B).hom

/-- The coordinate extension uses the actual biproduct module. The formula determines
its action on every lattice vector, and the two maps are the actual coordinate maps.
These are specifications of the objects asserted to exist by the theorem below.
Source: paragraph (3), node proof step 1
(blueprint: lem-sfb-lattice-character-koszul-boundary). -/
structure Extension (i : Fin r) where
  action : Group r →* End ((𝟙_ (Modules R)) ⊞ (𝟙_ (Modules R)))
  formula : ∀ g : Group r, action g = 𝟙 _ +
    (Multiplicative.toAdd g i) • (biprod.snd ≫ biprod.inl)
  inclusion : (RestrictionCup.regularAlgebra R r).X ⟶
    Action.mk ((𝟙_ (Modules R)) ⊞ (𝟙_ (Modules R))) action
  inclusion_hom : inclusion.hom = biprod.inl
  projection : Action.mk ((𝟙_ (Modules R)) ⊞ (𝟙_ (Modules R))) action ⟶
    (RestrictionCup.regularAlgebra R r).X
  projection_hom : projection.hom = biprod.snd
  zero : inclusion ≫ projection = 0

/-- The extension sequence, with its fixed equivariant endpoint maps.
Source: paragraph (3), node proof steps 1--2
(blueprint: lem-sfb-lattice-character-koszul-boundary). -/
def sequence {i : Fin r} (E : Extension R r i) : ShortComplex (Equivariant R r) :=
  ShortComplex.mk E.inclusion E.projection E.zero

/-- Subset inclusions into the trivial-coefficient Koszul model. Concentration of the
source in degree a and the displayed matrix fix each chain map uniquely.
Source: paragraph (3), node proof steps 2 and 4
(blueprint: lem-sfb-lattice-character-koszul-boundary). -/
structure Inclusions (K : KoszulModel R r) where
  map : ∀ (a : ℤ) (_I : Subsets r a),
    (CochainComplex.singleFunctor (Modules R) a).obj (𝟙_ (Modules R)) ⟶
      K.functor.obj (RestrictionCup.regularAlgebra R r).X
  coordinates : ∀ (a : ℤ) (I J : Subsets r a),
    (map a I).f a ≫ (K.coordinates (RestrictionCup.regularAlgebra R r).X a).hom ≫
      biproduct.π _ J =
    (HomologicalComplex.singleObjXSelf (.up ℤ) a (𝟙_ (Modules R))).hom ≫
      if I = J then 𝟙 _ else 0

/-- The unipotent coordinate extension is exact, its Koszul rows have the specified
underlying splitting, and its canonical derived boundary is the positive singleton.
Every triangulated, invariant-normalized comparison has the same character equality.

Source: direct-image stability proof paragraph (3), algebraic dense-lattice normalization;
Stacks Tags 011J, 014I, 014Q and 0152
(blueprint: lem-sfb-lattice-character-koszul-boundary).

Proof, following all six node steps:
1. On the actual biproduct set n(x,y)=(x+n_i y,y). Addition of n_i gives the group law;
negation gives the inverse. The inclusion (x,0) and projection y are equivariant. The
underlying split sequence is exact and forgetting detects exactness
(lem-sfb-condensed-derived-restriction-calculus).
2. Apply the finite Koszul functor. Its diagonal map matrices give termwise exactness.
Take the finite sums of the second inclusion and first projection for s and pi on
all subset coordinates. They obey pi a=1, p s=1 and a pi+s p=1. Outside [0,r] the
biproducts are zero. The endpoint differentials vanish since their actions are trivial
(lem-sfb-discrete-lattice-koszul-resolution).
3. Apply lem-sc-p1-split-ses-boundary-comparison: the canonical cone boundary is the
localization of homOfDegreewiseSplit, whose components are s d pi. This uses the
positive split-boundary convention and the cone's negative third projection.
4. For a target subset J the only contribution is i in J, with sign given by the
number of elements of J below i. In degree zero the singleton i has coefficient +1,
and all other singleton coefficients vanish. Shifting down gives the singleton
inclusion, with the canonical Q/shift and inverse-shift identifications.
5. The connecting and invariant-normalization clauses of
lem-sfb-lattice-koszul-triangulated-cup-comparison identify this boundary applied to
the invariant unit with the derived character class. The normalized action bridge
transports exactly the extension of the existing coordinate character. Its defect
on (0,1) is (+d_i,0), so the imported characterClass has this positive sign. Shift
down to obtain the asserted equality of actual derived morphisms, for any comparison.
6. There is no i at rank zero. At rank one the middle differential is (x,y)↦(y,0),
so the boundary is +1. Zero rings give zero maps. The finite integral formulas apply
also in characteristic two, without flatness or completeness assumptions. -/
theorem lattice_character_koszul_boundary (i : Fin r) (K : KoszulModel R r)
    (M : TriangulatedCup.TriangulatedModel R r K) (c : Comparison R r K)
    (hc : TriangulatedCup.ComparisonProperties R r K M c)
    (B : RestrictionCup.Bridge R r)
    (a : CategoryTheory.CondensedDerivedRestriction.Character
      (RestrictionCup.ring R) (ULift.{u} (Group r)))
    (ha : ∀ (S : Profinite.{u}) (g : C(S, ULift.{u} (Group r))) (n : ℤ),
      (∀ s : S, Multiplicative.toAdd (g s).down i = n) →
        a.app S g = (n : CategoryTheory.CondensedBar.sectionRing (RestrictionCup.ring R) S)) :
    ∃ (E : Extension R r i) (hE : (sequence R r E).ShortExact)
      (hK : ((sequence R r E).map K.functor).ShortExact)
      (σ : ∀ n : ℤ, (((sequence R r E).map K.functor).map
        (HomologicalComplex.eval (Modules R) (.up ℤ) n)).Splitting)
      (U : Inclusions R r K),
      (∀ j : Fin r, IsIso (E.action (generator j))) ∧
      (∀ j k : Fin r, Commute (E.action (generator j)) (E.action (generator k))) ∧
      (∀ (a b : ℤ), (K.functor.obj (RestrictionCup.regularAlgebra R r).X).d a b = 0) ∧
      (∀ (n : ℤ) (I J : Subsets r n),
        biproduct.ι _ I ≫ (K.coordinates _ n).inv ≫ (σ n).s ≫
          (K.coordinates _ n).hom ≫ biproduct.π _ J =
        if I = J then biprod.inr else 0) ∧
      (∀ (n : ℤ) (I J : Subsets r n),
        biproduct.ι _ I ≫ (K.coordinates _ n).inv ≫ (σ n).r ≫
          (K.coordinates _ n).hom ≫ biproduct.π _ J =
        if I = J then biprod.fst else 0) ∧
      DerivedCategory.triangleOfSESδ hK =
        ShiftedHom.map (CochainComplex.homOfDegreewiseSplit
          ((sequence R r E).map K.functor) σ) DerivedCategory.Q ∧
      (∀ n : ℤ,
        (CochainComplex.homOfDegreewiseSplit ((sequence R r E).map K.functor) σ).f n =
          (σ n).s ≫ (K.functor.obj (sequence R r E).X₂).d n (n + 1) ≫ (σ (n + 1)).r) ∧
      (∀ j : Fin r,
        biproduct.ι _ (⟨∅, rfl⟩ : Subsets r 0) ≫
          (K.coordinates (RestrictionCup.regularAlgebra R r).X 0).inv ≫
          (CochainComplex.homOfDegreewiseSplit ((sequence R r E).map K.functor) σ).f 0 ≫
          (K.coordinates (RestrictionCup.regularAlgebra R r).X 1).hom ≫
          biproduct.π _ (⟨{j}, by simp⟩ : Subsets r 1) =
        if j = i then 𝟙 _ else 0) ∧
      (DerivedCategory.Q.map (U.map 0 ⟨∅, rfl⟩) ≫
          DerivedCategory.triangleOfSESδ hK)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory.{u + 2} (Modules R))
          (1 : ℤ) (-1 : ℤ) (add_neg_cancel 1)).hom.app _ =
        ((DerivedCategory.singleFunctors (Modules R)).shiftIso (-1) 1 0 (by decide)).hom.app
          (𝟙_ (Modules R)) ≫ DerivedCategory.Q.map (U.map 1 ⟨{i}, by simp⟩) ∧
      transportCharacterClass R r B a =
        ((DerivedCategory.singleFunctors (Modules R)).shiftIso (-1) 1 0 (by decide)).hom.app
          (𝟙_ (Modules R)) ≫ DerivedCategory.Q.map (U.map 1 ⟨{i}, by simp⟩) ≫
            c.iso.hom.app (RestrictionCup.regularAlgebra R r).X := by
  sorry

end CharacterBoundary
end Profinite.DiscreteLattice
