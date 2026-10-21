module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.Topology.LadicLattice
public import Sheaf.CategoryTheory.CondensedDerivedCup
public import Sheaf.CategoryTheory.CondensedUnipotentClass
import Sheaf.CategoryTheory.PolynomialDerivedBarComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.Paper.RationalPolynomialBarContraction
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar

/-! # The coordinate-cup exterior map for trivial ell-adic coefficients

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
trivial-representation analytic base case; exact all-continuous noncomplete-coefficient
reference WANTED (blueprint: lem-sfb-trivial-ladic-derived-exterior).

The exterior object is the finite direct sum of the shifted regular module, indexed by
all coordinate subsets. Its specified arrow is constructed from the positive connecting
character classes, the ordinary derived cup product, and the canonical tensor-shift maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar CategoryTheory.CondensedDerivedRestriction
open Profinite.CondensedAction Profinite.LadicLattice

namespace Profinite.TrivialLadicExterior

variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r : ℕ)

/-- The coordinate character on every profinite test object, with the actual inclusions
Z_ell into Q_ell into F and all continuous sections.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def coordinateSection (i : Fin r) (S : Profinite.{u}) (g : C(S, Lattice.{u} ell r)) :
    sectionRing (continuousScalarRing F) S :=
  ULift.up ⟨fun s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down i : ℚ_[ell]),
    (continuous_algebraMap ℚ_[ell] F).comp
      (continuous_subtype_val.comp ((continuous_apply i).comp
        (continuous_uliftDown.comp g.continuous)))⟩

/-- These sections form a natural additive condensed-group map.
Source: the specified coordinate inclusions in direct-images paragraph (3)
(blueprint: lem-sfb-trivial-ladic-derived-exterior).
Proof: the two field inclusions preserve zero and addition. Evaluate these identities
pointwise on each profinite S. Restriction is precomposition, so evaluating either side
of naturality at t gives exactly the same coordinate of g(f(t)). -/
theorem coordinateSection_laws (i : Fin r) :
    (∀ S, coordinateSection ell F r i S 1 = 0) ∧
    (∀ S g h, coordinateSection ell F r i S (g * h) =
      coordinateSection ell F r i S g + coordinateSection ell F r i S h) ∧
    (∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, Lattice.{u} ell r)),
      (continuousScalarRing F).X.obj.map f.op (coordinateSection ell F r i S g) =
        coordinateSection ell F r i T (g.comp f.hom.hom)) := by
  sorry

/-- The actual coordinate additive condensed character, with its sectionwise formula.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def coordinateCharacter (i : Fin r) :
    Character (continuousScalarRing F) (Lattice.{u} ell r) where
  app := coordinateSection ell F r i
  one := (coordinateSection_laws ell F r i).1
  mul := (coordinateSection_laws ell F r i).2.1
  naturality := (coordinateSection_laws ell F r i).2.2

variable (A : CategoryTheory.CondensedBar.Ring.{u})

/-- The shifted regular internal module A[-n], in the ordinary derived category.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def shiftedRegular (n : ℕ) : DerivedCategory.{u + 1} (Modules A) :=
  ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))⟦(-(n : ℤ))⟧

/-- The based exterior complex, using the equivalent finite sum of A[-|I|].
Each summand is concentrated in degree |I|, hence the differential is zero and all
terms outside 0,...,r vanish.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def exteriorObject : DerivedCategory.{u + 1} (Modules A) :=
  ⨁ fun I : Finset (Fin r) ↦ shiftedRegular A I.card

/-- The canonical tensor-shift identification splits off the first degree-one factor.
Source: ordered cup convention in direct-images paragraph (3)
(blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def splitShift (n : ℕ) :
    shiftedRegular A (n + 1) ≅ shiftedRegular A 1 ⊗ shiftedRegular A n :=
  (eqToIso (congrArg
    (fun n : ℤ ↦ (shiftFunctor (DerivedCategory.{u + 1} (Modules A)) n).obj
      ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))
    (show -((n + 1 : ℕ) : ℤ) = (-1 : ℤ) + -(n : ℤ) by omega))) ≪≫
    ((shiftFunctor _ ((-1 : ℤ) + -(n : ℤ))).mapIso
      ((λ_ ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))).symm ≪≫
        (whiskerRightIso (baseUnitIso A)
          ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))))) ≪≫
    (DerivedCategory.shiftTensorShiftIso (Modules A)
      ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))
      ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))
      (-1) (-(n : ℤ))).symm

/-- The unit on the zero-length summand and the ordered derived cup of the indicated
coordinate connecting classes on a nonempty list. No coordinates are permuted.
Source: the specified chi in direct-images paragraph (3)
(blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def orderedCoordinateCup : (indices : List (Fin r)) →
    shiftedRegular (continuousScalarRing F) indices.length ⟶
      cohomology (continuousScalarRing F) (Lattice.{u} ell r)
  | [] => (shiftFunctorZero _ ℤ).hom.app _ ≫ (baseUnitIso _).inv ≫ cupUnit
  | i :: indices => (splitShift (continuousScalarRing F) indices.length).hom ≫
      (characterClass (coordinateCharacter ell F r i) ⊗ₘ orderedCoordinateCup indices) ≫ cup

/-- The increasing subset order specifies the actual cup arrow on its summand.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def subsetCup (I : Finset (Fin r)) :
    shiftedRegular (continuousScalarRing F) I.card ⟶
      cohomology (continuousScalarRing F) (Lattice.{u} ell r) :=
  eqToHom (by rw [Finset.length_sort]) ≫ orderedCoordinateCup ell F r (I.sort (· ≤ ·))

/-- The specified coordinate-cup map, obtained from its summand arrows by the finite
coproduct universal property, including the empty-subset unit.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def exteriorMap : exteriorObject r (continuousScalarRing F) ⟶
    cohomology (continuousScalarRing F) (Lattice.{u} ell r) :=
  biproduct.desc (subsetCup ell F r)

/-- The rank-zero source has only the empty-subset summand, canonically A[0].
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior). -/
def rankZeroSourceIso : exteriorObject 0 A ≅
    (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X) :=
  biproductUniqueIso (fun I : Finset (Fin 0) ↦ shiftedRegular A I.card) ≪≫
    (shiftFunctorZero _ ℤ).app _

/-- The assertion for the specified arrow over both the finite intermediate field and
its norm-topological algebraic closure, without completion or filtered-union topology.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior).
Proof:
1. lem-sfb-polynomial-derived-bar-comparison supplies P and its evaluation map eta.
   lem-sfb-rational-polynomial-bar-contraction sends e_I to the ordered monomial.
2. Extend its rational projection and homotopy internally, coefficient by coefficient.
   Every basis monomial has finite image, so no infinite sum or completion is used.
   The identities pi=1 and dh+hd=1-ip give an internal chain homotopy equivalence i.
3. The polynomial derived-bar comparison makes eta i an isomorphism for precisely E
   and Omega with their norm topologies, retaining the derived internal-Hom columns.
4. lem-sfb-condensed-derived-invariant-bar identifies C with the bar by epsilon.
   Thus theta = eta i followed by epsilon inverse is a derived isomorphism.
5. lem-sfb-internal-bar-ordered-cup identifies its I component with the ordered cup
   component of chi times a sign depending only on |I|, and fixes the empty unit.
   The diagonal sign automorphism sigma is its own inverse; theta = sigma followed
   by chi on every summand. Hence chi is an isomorphism, before taking cohomology.
6. Rank zero is the trivial group and its unit is the identity, as stated separately
   in rankZeroNormalization. Both coefficient choices use the same polynomial formulas. -/
theorem trivial_ladic_derived_exterior (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E] (r : ℕ) :
    IsIso (exteriorMap ell E r) ∧ IsIso (exteriorMap ell Ω r) := by
  sorry

/-- Under the canonical empty-summand identification and the trivial-group invariant
unit identification, the rank-zero arrow is the identity A[0]. The target identification
is normalized by the actual unit, so the existential does not allow an arbitrary map.
Source: direct-images paragraph (3) (blueprint: lem-sfb-trivial-ladic-derived-exterior).
Proof: for the one-element group every section is fixed after all base changes.
The invariant inclusion and invariant functor identify with identity and are exact.
Their derived unit is therefore the identity on A[0]. The source has just its empty
summand, and biproduct descent is the unit there. Composing with the unit-normalized
identification gives the displayed identity. -/
theorem rankZeroNormalization :
    ∃ e : cohomology (continuousScalarRing F) (Lattice.{u} ell 0) ≅
        (DerivedCategory.singleFunctor (Modules (continuousScalarRing F)) 0).obj
          (Mod.regular (continuousScalarRing F).X),
      ((baseUnitIso (continuousScalarRing F)).inv ≫ cupUnit) ≫ e.hom = 𝟙 _ ∧
      exteriorMap ell F 0 ≫ e.hom = (rankZeroSourceIso (continuousScalarRing F)).hom := by
  sorry

end Profinite.TrivialLadicExterior
