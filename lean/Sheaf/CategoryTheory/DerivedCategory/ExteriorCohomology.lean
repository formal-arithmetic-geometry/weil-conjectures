module

public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Exterior cohomology of a derived algebra

Source: the induced-product and exterior-algebra clauses of the agent-stated
bialgebra rigidity argument, Stacks More on Algebra, Tag 0BCC as minimal-model input.
(blueprint: def-sfb-derived-exterior-cohomology).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory

namespace DerivedCategory.ExteriorCohomology

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The regular module in degree n is the derived unit shifted by -n.
Source: the cochain degree convention in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def singleUnitShift (n : ℤ) :
    (singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R) ≅
      (𝟙_ (DerivedCategory (ModuleCat.{u} R)))⟦-n⟧ :=
  (((singleFunctors (ModuleCat.{u} R)).shiftIso (-n) n 0 (neg_add_cancel n)).app
    (ModuleCat.of R R)).symm ≪≫
  (shiftFunctor _ (-n)).mapIso (singleFunctorObjUnitIso (ModuleCat.{u} R))

/-- The canonical inverse of multiplication on the shifted regular modules.
Source: signed total tensor in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def singleDiagonal (p q : ℤ) :
    (singleFunctor (ModuleCat.{u} R) (p + q)).obj (ModuleCat.of R R) ⟶
      (singleFunctor (ModuleCat.{u} R) p).obj (ModuleCat.of R R) ⊗
        (singleFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R) :=
  (singleUnitShift (R := R) (p + q)).hom ≫
  eqToHom (congrArg (fun n : ℤ ↦ (𝟙_ (DerivedCategory (ModuleCat.{u} R)))⟦n⟧)
    (neg_add p q)) ≫
  (shiftFunctor _ (-p + -q)).map (λ_ (𝟙_ (DerivedCategory (ModuleCat.{u} R)))).inv ≫
  (shiftTensorShiftIso (ModuleCat.{u} R) (𝟙_ _) (𝟙_ _) (-p) (-q)).inv ≫
  ((singleUnitShift (R := R) p).inv ⊗ₘ (singleUnitShift (R := R) q).inv)

/-- The unique morphism from R in degree n representing a cohomology element.
Source: derived morphisms from a projective single, used in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def representative (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (x : (homologyFunctor (ModuleCat.{u} R) n).obj K) :
    (singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R) ⟶ K :=
  (homSingleEquivOfProjective (ModuleCat.of R R) n K).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x))

/-- The induced cup product, obtained by tensoring the unique representing morphisms.
No product on cohomology is independently chosen.
Source: induced-product clause of the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def cup {K : DerivedCategory (ModuleCat.{u} R)} (μ : K ⊗ K ⟶ K) (p q : ℤ)
    (x : (homologyFunctor (ModuleCat.{u} R) p).obj K)
    (y : (homologyFunctor (ModuleCat.{u} R) q).obj K) :
    (homologyFunctor (ModuleCat.{u} R) (p + q)).obj K :=
  (homSingleToHomology (ModuleCat.of R R) (p + q) K
    (singleDiagonal p q ≫ (representative K p x ⊗ₘ representative K q y) ≫ μ)).hom 1

/-- The cohomology class of the unit, evaluated on 1 in the regular module.
Source: unit normalization in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def unitClass {K : DerivedCategory (ModuleCat.{u} R)}
    (η : 𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ K) :
    (homologyFunctor (ModuleCat.{u} R) 0).obj K :=
  (homSingleToHomology (ModuleCat.of R R) 0 K
    ((singleFunctorObjUnitIso (ModuleCat.{u} R)).hom ≫ η)).hom 1

/-- Cup product in natural degrees, with the canonical index transport.
Source: exterior products in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def cupNat {K : DerivedCategory (ModuleCat.{u} R)} (μ : K ⊗ K ⟶ K) (p q : ℕ)
    (x : (homologyFunctor (ModuleCat.{u} R) (p : ℤ)).obj K)
    (y : (homologyFunctor (ModuleCat.{u} R) (q : ℤ)).obj K) :
    (homologyFunctor (ModuleCat.{u} R) ((p + q : ℕ) : ℤ)).obj K :=
  (eqToHom (congrArg (fun i : ℤ ↦ (homologyFunctor (ModuleCat.{u} R) i).obj K)
    (Int.natCast_add p q).symm)) (cup μ p q x y)

/-- Iterated multiplication in degree one, with the empty product given by the unit.
Source: pure-wedge normalization in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def product {K : DerivedCategory (ModuleCat.{u} R)}
    (η : 𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ K) (μ : K ⊗ K ⟶ K) :
    (n : ℕ) → (Fin n → (homologyFunctor (ModuleCat.{u} R) 1).obj K) →
      (homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj K
  | 0, _ => unitClass η
  | n + 1, v => cupNat μ n 1 (product η μ n (Fin.init v)) (v (Fin.last n))

/-- Cohomology is exterior on degree one precisely when multiplication gives linear
isomorphisms from every exterior power, with the specified values on pure wedges,
and all negative cohomology vanishes. This encodes the normalized graded algebra
isomorphism without choosing an unrelated ring structure on a direct sum.
Source: exterior-algebra clause of the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def IsExterior {K : DerivedCategory (ModuleCat.{u} R)}
    (η : 𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ K) (μ : K ⊗ K ⟶ K) : Prop :=
  (∀ i : ℤ, i < 0 → CategoryTheory.Limits.IsZero
    ((homologyFunctor (ModuleCat.{u} R) i).obj K)) ∧
  ∃ e : ∀ n : ℕ,
    (⋀[R]^n ((homologyFunctor (ModuleCat.{u} R) 1).obj K)) ≃ₗ[R]
      (homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj K,
    ∀ (n : ℕ) (v : Fin n → (homologyFunctor (ModuleCat.{u} R) 1).obj K),
      e n (exteriorPower.ιMulti R n v) = product η μ n v



end DerivedCategory.ExteriorCohomology

namespace DerivedCategory.ExteriorCohomology

variable [∀ A : CommRingCat.{u}, HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The scalar-extended unit, using the published normalized coefficient-unit comparison.
Source: scalar extension of the induced exterior cohomology in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def scalarUnit {A B : CommRingCat.{u}} (f : A ⟶ B)
    {K : PerfectScalar.D.{u, w} A} (η : 𝟙_ (PerfectScalar.D.{u, w} A) ⟶ K) :
    𝟙_ (PerfectScalar.D.{u, w} B) ⟶
      (PerfectScalar.B.{u, w} f).obj K :=
  (PerfectScalar.coherenceData.{u, w}.unit f).inv ≫ (PerfectScalar.B.{u, w} f).map η

/-- The scalar-extended multiplication, using the published balanced tensor comparison.
Source: scalar extension of the induced exterior cohomology in the rigidity argument
(blueprint: def-sfb-derived-exterior-cohomology). -/
def scalarMul {A B : CommRingCat.{u}} (f : A ⟶ B)
    {K : PerfectScalar.D.{u, w} A} (hK : IsPerfectRingComplex K) (μ : K ⊗ K ⟶ K) :
    (PerfectScalar.B.{u, w} f).obj K ⊗ (PerfectScalar.B.{u, w} f).obj K ⟶
      (PerfectScalar.B.{u, w} f).obj K :=
  (PerfectScalar.coherenceData.{u, w}.tensor f K K hK hK).inv ≫ (PerfectScalar.B.{u, w} f).map μ

end DerivedCategory.ExteriorCohomology
