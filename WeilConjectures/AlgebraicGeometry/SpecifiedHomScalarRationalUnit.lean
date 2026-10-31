/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.SpecifiedHomScalarRationalNaturality
import WeilConjectures.AlgebraicGeometry.SpecifiedHomScalarTower
/-! Rational unit coherence for the specified Hom comparison.
(blueprint: lem-zl-specified-hom-scalar-evaluation). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard
  rationalDerivedInternalHom rationalHomScalarComparison sfRationalScalarExtension
  sfRationalScalarUnit sfRationalScalarComp
attribute [local implicit_reducible] rationalHomScalarPair
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- The identity scalar comparison satisfies the Hom unit equation after rationalization.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: localize the integral unit equation and identify each normalized component. -/
theorem specifiedHomScalarRational_unit (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    ((rationalHomScalarComparison l E E (AlgHom.id ℚ_[l] E) X P).hom ≫
      (rationalDerivedInternalHom l E X).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l E E (AlgHom.id ℚ_[l] E) X P) (Y := P)
          (Prod.mkHom
            (((sfRationalScalarUnit l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app P.obj.1.unop).op)
            ((sfRationalScalarUnit l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app P.obj.2))) =
      (sfRationalScalarUnit l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((rationalDerivedInternalHom l E X).obj P)) := by
  -- The normalized rational tower forces the unit equation by cancellation.
  let T := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)
  let H := rationalDerivedInternalHom l E X
  let U := sfRationalScalarUnit l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
  let S := rationalHomScalarPair l E E (AlgHom.id ℚ_[l] E) X
  let c (Q : (constructibleRationalHomPairs l E X).FullSubcategory) :=
    rationalHomScalarComparison l E E (AlgHom.id ℚ_[l] E) X Q
  have hcomp (K : sfRationalConstructibleCategory l E X) :
      (sfRationalScalarComp l E E (AlgHom.id ℚ_[l] E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).hom.app K =
      T.map (U.hom.app K) :=
    (sfRationalScalar_coherence l E E (AlgHom.id ℚ_[l] E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).1 K
  have hcompInv (K : sfRationalConstructibleCategory l E X) :
      (sfRationalScalarComp l E E (AlgHom.id ℚ_[l] E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).inv.app K =
      T.map (U.inv.app K) := by
    have hi : (sfRationalScalarComp l E E (AlgHom.id ℚ_[l] E) X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id ℚ_[l] E)).app K =
        T.mapIso (U.app K) := Iso.ext (hcomp K)
    exact congrArg Iso.inv hi
  let k : S P ⟶ P := ObjectProperty.homMk
    (Prod.mkHom (U.inv.app P.obj.1.unop).op (U.hom.app P.obj.2))
  have hn : T.map (H.map k) ≫ (c P).hom =
      (c (S P)).hom ≫ H.map (ObjectProperty.homMk (X := S (S P)) (Y := S P)
        (Prod.mkHom (T.map (U.inv.app P.obj.1.unop)).op
          (T.map (U.hom.app P.obj.2)))) :=
    specifiedHomScalarRational_naturality l E E (AlgHom.id ℚ_[l] E) X
      (S P) P (U.inv.app P.obj.1.unop) (U.hom.app P.obj.2)
  have ht := specifiedHomScalarRational_tower l E E (AlgHom.id ℚ_[l] E)
    X P E (AlgHom.id ℚ_[l] E)
  simp only [AlgHom.comp_id, hcomp, hcompInv] at ht
  change T.map (c P).hom ≫ ((c (S P)).hom ≫ _) =
    T.map (U.hom.app (H.obj P)) ≫ (c P).hom at ht
  rw [← hn, ← Category.assoc, ← T.map_comp] at ht
  have he := (cancel_mono (c P).hom).mp ht
  let : T.Faithful := Functor.Faithful.of_iso U.symm
  exact T.map_injective he
end WeilConjectures
