/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZlShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PodCondensedAutomorphismCompactExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorShifts

/-! # Canonical shifts and composition of the semilinear Frobenius shriek exchange

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-reduction-to-the-relative-affine-line/sk-thm-dl-general-sheaf/
lem-zl-composition-weight-bound.proof.md, paragraph 1
(blueprint: lem-zl-frobenius-shriek-exchange-coherence).

Coefficients are the finite-subextension condensed ring `Profinite.padicAlgClRingObj ℓ`
and the categories are the ordinary bounded constructible categories. All schemes and maps
are those of `SepFinType`, so every scheme is separated of finite type and every map is
separated of finite type. `P_T` is the derived inverse image along the geometric
Frobenius `D.geometricFrobenius`, an automorphism of schemes which is not `k`-linear.

* `zlFsxGeometricCompactification`: the base change `c = (j, p)` of a model compactification
  `c₀` over `k₀`, i.e. `podGeometricCompactification`, read as a compactification of the
  geometric map `zlGeometricHom`.
* `zlFsxModelExchange`: the specified exchange `e_f^c = Rp_*(β_j) ∘ FrEx_{p,*} D(j_!)`,
  which is exactly `FrobeniusSquareExchange.compact` for the two Frobenius squares of `c`.
* `zlFsxComparison`: the canonical comparison `C_{d,c}` (`sfCompComparison`, the comparison of
  sk-prop-sf-comp-coherence normalized by refinement maps), on bounded constructible inputs.
* `zlFsxExchangeApp`: `e_f^d = (C_{d,c} P_X)⁻¹ ∘ e_f^c ∘ (P_Y C_{d,c})`.
* `zlFsxComposition`: `α_{g,f}` of clause (1) of sk-thm-sf-comp-composition
  (`sfCompComposition`), on bounded constructible inputs.

The fixed shift structures are the termwise ones of exact inverse images and of `D(j_!)`
(`modulePullbackDerivedCommShift`, `mapDerivedCategory`) and the canonical K-injective
shifts of total derived direct images.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The characteristic of the algebraic closure is the characteristic `p` of the datum.
Source: def-weil-finite-field-fiber, standing conventions
(blueprint: lem-zl-frobenius-shriek-exchange-coherence). -/
theorem zlFsx_ringChar : ringChar D.k = D.p := by
  haveI : Fact D.p.Prime := ⟨D.prime⟩
  letI := Fintype.ofFinite D.k₀
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

/-- The finite-subextension condensed ring is an admissible coefficient of the
localizing compact-support theory.
Source: sk-def-sfb-qlbar-condensed, used through sk-thm-sf-comp-composition
(blueprint: lem-zl-frobenius-shriek-exchange-coherence). -/
theorem zlFsx_admissible :
    IsLocalizingAdmissibleCoefficient ℓ (Profinite.padicAlgClRingObj.{u} ℓ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

/-- The geometric map of a composite is the composite of the geometric maps.
Source: geometric-fibre convention, lem-zl-shriek-composition
(blueprint: lem-zl-frobenius-shriek-exchange-coherence). -/
theorem zlFsx_geometricHom_comp {X₀ Y₀ Z₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀) :
    (zlGeometricHom D f₀).hom.left ≫ (zlGeometricHom D g₀).hom.left =
      (zlGeometricHom D (f₀ ≫ g₀)).hom.left := by
  have hc : zlGeometricHom D (f₀ ≫ g₀) = zlGeometricHom D f₀ ≫ zlGeometricHom D g₀ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [zlGeometricHom, Category.assoc]
  exact congrArg (fun f ↦ f.hom.left) hc.symm

/-- The base change `c = (j, p)` to `k` of a compactification `c₀ = (j₀, p₀)` over `k₀`;
this is `podGeometricCompactification`, as a compactification of the geometric map.
Source: lem-zl-frobenius-shriek-exchange-coherence, second paragraph
(blueprint: lem-zl-frobenius-shriek-exchange-coherence). -/
abbrev zlFsxGeometricCompactification {X₀ Y₀ : SepFinType D.k₀} {f₀ : X₀ ⟶ Y₀}
    (c₀ : Compactification f₀.hom.left) :
    Compactification (zlGeometricHom D f₀).hom.left :=
  podGeometricCompactification D c₀

/-- The canonical comparison `C_{c,d} : F_c ≅ F_d` of sk-prop-sf-comp-coherence, normalized by
the refinement maps, at a bounded constructible input. It is `sfCompComparison` of
sk-thm-sf-comp-composition at the inclusion of that input in the localizing closure.
Source: lem-zl-frobenius-shriek-exchange-coherence, second paragraph
(blueprint: lem-zl-frobenius-shriek-exchange-coherence). -/
def zlFsxComparison (hℓ : ℓ ≠ D.p) {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (c d : Compactification (zlGeometricHom D f₀).hom.left)
    (K : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj K.obj ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) d).obj K.obj :=
  haveI : Fact (ringChar D.k).Prime := ⟨by rw [zlFsx_ringChar D]; exact D.prime⟩
  haveI : Fact (ringChar D.k ≠ ℓ) := ⟨by rw [zlFsx_ringChar D]; exact fun h ↦ hℓ h.symm⟩
  (sfCompComparison ℓ D.k (Profinite.padicAlgClRingObj ℓ) (zlFsx_admissible ℓ)
    (zlGeometricHom D f₀) c d).app ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)

/-- The composition map `α_{g,f} : F_d F_c ≅ F_e` normalized in clause (1) of
sk-thm-sf-comp-composition (`sfCompComposition`), at a bounded constructible input; the
compactification `e` of the geometric map of `g₀ ∘ f₀` is read along
`zlFsx_geometricHom_comp`.
Source: lem-zl-frobenius-shriek-exchange-coherence, third paragraph
(blueprint: lem-zl-frobenius-shriek-exchange-coherence). -/
def zlFsxComposition (hℓ : ℓ ≠ D.p) {X₀ Y₀ Z₀ : SepFinType D.k₀}
    (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
    (c : Compactification (zlGeometricHom D f₀).hom.left)
    (d : Compactification (zlGeometricHom D g₀).hom.left)
    (e : Compactification (zlGeometricHom D (f₀ ≫ g₀)).hom.left)
    (K : BoundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (zlGeometricScheme D X₀).obj.left)) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) d).obj
        ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj
          K.obj) ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) e).obj K.obj :=
  haveI : Fact (ringChar D.k).Prime := ⟨by rw [zlFsx_ringChar D]; exact D.prime⟩
  haveI : Fact (ringChar D.k ≠ ℓ) := ⟨by rw [zlFsx_ringChar D]; exact fun h ↦ hℓ h.symm⟩
  (sfCompComposition ℓ D.k (Profinite.padicAlgClRingObj ℓ) (zlFsx_admissible ℓ)
    (zlGeometricHom D f₀) (zlGeometricHom D g₀) c d
    (e.copy (zlFsx_geometricHom_comp D f₀ g₀))).app
      ((zlDbcToLoc D ℓ (zlGeometricScheme D X₀)).obj K)

-- The statement elaborates several derived functors, their shift structures and subtype lifts.
set_option maxHeartbeats 2000000 in
end AlgebraicGeometry.ProEtale.CondensedRing
