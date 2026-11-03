/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteCoefficientSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.Semilinear.DerivedSystemMappingHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Actual coherent global Hom systems for continuous integral reductions

Source: Zheng, Construction 4.1; Stacks 0B6E.
(blueprint: def-sfb-coherent-integral-mapping-systems)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The scalar value is the genuine integral constant section followed by quotient reduction.
Source: blueprint coherent Hom system, step 5
(blueprint: def-sfb-coherent-integral-mapping-systems). -/
def scalarValue (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) : (coefficients l E X n).obj.obj U :=
  (coefficientMap l E X n).hom.app U
    ((constantSections X (Padic.coefficientExtensionIntegers l E)).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (Padic.coefficientExtensionIntegers l E)))).app U a))

/-- The actual scalar algebra on the coefficient sequence is fixed by all its section values.
Source: Zheng 4.1 and Stacks 0B6E
(blueprint: def-sfb-coherent-integral-mapping-systems).

Proof: send a in O at (n,U) to its constant continuous section and then its
class modulo ell^(n+1). Naturality in U follows from the sheafification unit
and the ring-sheaf maps. Naturality in n is coefficientMap_compatible, iterated
along the actual adjacent quotient maps. Pointwise ring operations preserve
zero, one, addition and multiplication, so these compatible sections form a
ring homomorphism. Equality at every (n,U) is equality of global sections,
which proves uniqueness. The construction includes the empty scheme.
-/
theorem scalarAlgebra_existsUnique (X : Scheme.{u}) :
    ∃! α : SystemAlgebra.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (coefficients l E X) (transitions l E X) (Padic.coefficientExtensionIntegers l E),
      ∀ (a : Padic.coefficientExtensionIntegers l E) (U : (ℕ × X.ProEt)ᵒᵖ),
        (α a).val U = scalarValue l E X U.unop.1 (op U.unop.2) a := by
  let J := Scheme.ProEt.topology X
  let O := Padic.coefficientExtensionIntegers l E
  let R := (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of O)
  let α (n : ℕ) : R ⟶ (coefficients l E X n).obj :=
    toSheafify J R ≫ (constantSections X O ≫ coefficientMap l E X n).hom
  have hα (n : ℕ) : α (n + 1) ≫ (transitions l E X n).hom = α n := by
    have hc := congrArg (fun g ↦ toSheafify J R ≫
      (sheafToPresheaf J CommRingCat.{u + 1}).map (constantSections X O ≫ g))
      (coefficientMap_compatible l E X n)
    simpa only [α, Functor.map_comp, sheafToPresheaf_map,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Category.id_comp] using hc
  let a : (Functor.const ℕᵒᵖ).obj R ⟶
      rings J (coefficients l E X) (transitions l E X) ⋙
        sheafToPresheaf J CommRingCat.{u + 1} :=
    NatTrans.ofOpSequence α (fun n ↦ by
      change (𝟙 R) ≫ α n = α (n + 1) ≫ _
      rw [Category.id_comp]
      simpa only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ,
        sheafToPresheaf_map] using (hα n).symm)
  let f : (Functor.const (ℕ × X.ProEt)ᵒᵖ).obj (CommRingCat.of O) ⟶
      (systemRing J (coefficients l E X) (transitions l E X)).obj :=
    Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := X.ProEt)).functor
      (Functor.uncurry.map a)
  let β : SystemAlgebra J (coefficients l E X) (transitions l E X) O :=
    { toFun := fun x ↦ ⟨fun U ↦ (f.app U).hom x, by
        intro U V g
        change ((systemRing J (coefficients l E X) (transitions l E X)).obj.map g).hom
          ((f.app U).hom x) = (f.app V).hom x
        have hn := f.naturality g
        change (𝟙 (CommRingCat.of O)) ≫ f.app V = f.app U ≫
          (systemRing J (coefficients l E X) (transitions l E X)).obj.map g at hn
        rw [Category.id_comp] at hn
        rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
        exact congrArg (fun h ↦ h.hom x) hn.symm⟩
      map_one' := by apply Subtype.ext; funext U; exact map_one (f.app U).hom
      map_mul' := fun x y ↦ by
        apply Subtype.ext; funext U; exact map_mul (f.app U).hom x y
      map_zero' := by apply Subtype.ext; funext U; exact map_zero (f.app U).hom
      map_add' := fun x y ↦ by
        apply Subtype.ext; funext U; exact map_add (f.app U).hom x y }
  refine ⟨β, fun _ _ ↦ rfl, ?_⟩
  intro γ hγ
  apply RingHom.ext
  intro x
  apply Subtype.ext
  funext U
  exact hγ x U

/-- The unique quotient-compatible action of the original integral scalar ring.
Source: Stacks 0B6E (blueprint: def-sfb-coherent-integral-mapping-systems). -/
def scalarAlgebra (X : Scheme.{u}) := (scalarAlgebra_existsUnique l E X).exists.choose

/-- The existing normalized calculus on the actual pro-etale quotient-ring system.
Source: Zheng 4.1, 4.10 (blueprint: def-sfb-coherent-integral-mapping-systems). -/
def calculus (X : Scheme.{u}) : Data.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (coefficients l E X) (transitions l E X) :=
  (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (coefficients l E X) (transitions l E X))).systems

/-- The ordinary unbounded integral proper direct image over the same continuous ring.
Source: the recorded pro-etale coefficient pushforward
(blueprint: def-sfb-coherent-integral-mapping-systems). -/
def integralPush {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  (CondensedRing.lowerStar
    (abelianPoint (Padic.coefficientExtensionIntegers l E)) p).rightDerivedFunctor

end AlgebraicGeometry.ProEtale.CoherentReduction
