/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.ZetaSeries
import WeilConjectures.PointCount
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg

/-!
# Affine data at a closed point of an integral scheme over a field

Source: Stacks Project, Morphisms, Tag 02JX, equality proof; expanded using
Tags 01RV, 01HV, 01HF, 00FV and 00P0.
(blueprint: lem-trf-closed-point-affine-dimension-data)

The chart ring is the actual ring of sections. Its structural map and the
structural map of the generic stalk are written using pullback and germs.
The stalk and residue-field comparisons are the canonical restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A closed point has an affine finite-type domain chart with the canonical
function-field, local-ring and residue-field comparisons and the common finite
Krull dimension and transcendence degree.

Source: Stacks Project, Morphisms, Tag 02JX, equality proof; Algebra, Tags 00FV
and 00P0; Morphisms, Tag 01RV; Schemes, Tags 01HV and 01HF.
(blueprint: lem-trf-closed-point-affine-dimension-data)

Proof:
1. Choose an affine chart of the locally finite-type morphism containing `x`.
   Its section ring is a finitely generated K-algebra. Since the chart is
   nonempty and X is integral, that ring is a nonzero domain.
2. Closedness of x restricts to the chart. The closure of its prime m is V(m),
   so no prime strictly contains m. A maximal ideal containing m then equals m.
3. Apply lem-sc-integral-function-field-affine-fraction: the generic point is
   in the chart, and its stalk is the fraction field with the germ map.
   Germs of structural constant sections show that this map respects K.
4. Apply lem-weil-pbc-affine-open-stalk-localization. The restriction stalk
   isomorphism preserves germs of constants, hence respects K. A ring
   isomorphism preserves units and maximal ideals, so it induces the canonical
   K-isomorphism of residue fields.
5. The residue field of A_m is A/m: a/s maps to its residue quotient, with
   kernel mA_m and surjective image. The images of algebra generators generate
   A/m. Apply lem-weil-pbc-zariski-lemma and transport through step 4.
6. Apply lem-weil-pbc-finite-type-domain-dimension-trdeg to A, its fraction
   field from step 3, and its maximal ideal m from step 2. It gives a natural
   number r equal to the transcendence degree, dim A, and dim A_m. -/
theorem closed_point_affine_dimension_data
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
      (hηU : genericPoint X ∈ U),
      IsDomain Γ(X, U) ∧
      RingHom.FiniteType
        ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) ∧
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsMaximal ∧
      Function.Injective (X.presheaf.germ U (genericPoint X) hηU) ∧
      (∀ b : Γ(X, U), b ≠ 0 →
        IsUnit (X.presheaf.germ U (genericPoint X) hηU b)) ∧
      (∀ z : X.functionField, ∃ a b : Γ(X, U), b ≠ 0 ∧
        z = X.presheaf.germ U (genericPoint X) hηU a *
          (X.presheaf.germ U (genericPoint X) hηU b)⁻¹) ∧
      (∀ c : K,
        X.presheaf.germ U (genericPoint X) hηU
            (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of K)).inv c)) =
          X.presheaf.germ ⊤ (genericPoint X) (Set.mem_univ _)
            (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) ∧
      ∃ (e : U.toScheme.presheaf.stalk ⟨x, hxU⟩ ≅ X.presheaf.stalk x)
        (eκ : U.toScheme.residueField ⟨x, hxU⟩ ≅ X.residueField x),
        e = U.stalkIso ⟨x, hxU⟩ ∧
        eκ.inv = U.ι.residueFieldMap ⟨x, hxU⟩ ∧
        (∀ c : K,
          e.hom (U.toScheme.presheaf.germ ⊤ ⟨x, hxU⟩ (Set.mem_univ _)
              ((U.ι ≫ f).appTop ((Scheme.ΓSpecIso (.of K)).inv c))) =
            X.presheaf.germ ⊤ x (Set.mem_univ _)
              (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) ∧
        (∀ c : K,
          eκ.hom ((U.ι ≫ f).residueFieldAlgebraMap ⟨x, hxU⟩ c) =
            f.residueFieldAlgebraMap x c) ∧
        @Module.Finite K (X.residueField x) _ _
          (f.residueFieldAlgebraMap x).toAlgebra.toModule ∧
        ∃ r : ℕ,
          @Algebra.trdeg K X.functionField _ _
              ((X.presheaf.germ ⊤ (genericPoint X) (Set.mem_univ _)).hom.comp
                (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)).toAlgebra =
            (r : Cardinal) ∧
          ringKrullDim Γ(X, U) = (r : WithBot ℕ∞) ∧
          ringKrullDim (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) =
            (r : WithBot ℕ∞) := by
  classical
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) (by simp)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hmax := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  have hft : RingHom.FiniteType
      ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) :=
    (f.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have hinj := germ_injective_of_isIntegral X (genericPoint X) hηU
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  have hconst (c : K) :
      X.presheaf.germ U (genericPoint X) hηU
          (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of K)).inv c)) =
        X.presheaf.germ ⊤ (genericPoint X) (Set.mem_univ _)
          (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c)) := by
    exact X.presheaf.germ_res_apply (homOfLE (by simp)) _ _ _
  refine ⟨U, hU, hxU, hηU, inferInstance, hft, hmax, hinj, ?_, ?_, hconst, ?_⟩
  · intro b hb
    exact isUnit_iff_ne_zero.mpr (fun h ↦ hb (hinj (by simpa using h)))
  · intro z
    obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective Γ(X, U) z
    exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, by
      simpa only [div_eq_mul_inv, RingHom.algebraMap_toAlgebra,
        Scheme.germToFunctionField] using he.symm⟩
  · refine ⟨U.stalkIso ⟨x, hxU⟩, (asIso (U.ι.residueFieldMap ⟨x, hxU⟩)).symm,
      rfl, rfl, ?_, ?_, f.finite_residueField_of_isClosed x hx, ?_⟩
    · intro c
      apply (ConcreteCategory.bijective_of_isIso (U.stalkIso ⟨x, hxU⟩).inv).injective
      rw [← ConcreteCategory.comp_apply (U.stalkIso ⟨x, hxU⟩).hom,
        Iso.hom_inv_id]
      simp only [ConcreteCategory.id_apply]
      rw [U.stalkIso_inv]
      simpa [Scheme.Hom.comp_appTop] using
        (U.ι.germ_stalkMap_apply ⊤ ⟨x, hxU⟩ (by trivial)
          (f.appTop ((Scheme.ΓSpecIso (.of K)).inv c))).symm
    · intro c
      change inv (U.ι.residueFieldMap ⟨x, hxU⟩)
        ((U.ι ≫ f).residueFieldAlgebraMap ⟨x, hxU⟩ c) = _
      rw [Scheme.Hom.residueFieldAlgebraMap_comp]
      simpa only [RingHom.comp_apply, ← ConcreteCategory.comp_apply,
        ConcreteCategory.id_apply, Scheme.Opens.ι_apply] using
        ConcreteCategory.congr_hom
          (IsIso.hom_inv_id (U.ι.residueFieldMap ⟨x, hxU⟩)) (f.residueFieldAlgebraMap x c)
    · let : Algebra K Γ(X, U) :=
        ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
      let : Algebra.FiniteType K Γ(X, U) := hft
      let : Algebra K X.functionField :=
        ((X.presheaf.germ ⊤ (genericPoint X) (Set.mem_univ _)).hom.comp
          (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)).toAlgebra
      let : IsScalarTower K Γ(X, U) X.functionField :=
        IsScalarTower.of_algebraMap_eq' (by ext c; exact (hconst c).symm)
      obtain ⟨r, hr, htr, hlocal⟩ :=
        finiteType_domain_ringKrullDim_eq_trdeg (k := K) (S := Γ(X, U))
      let e := (FractionRing.algEquiv Γ(X, U) X.functionField).restrictScalars K
      exact ⟨r, e.trdeg_eq.symm.trans htr, hr, hlocal _⟩

end AlgebraicGeometry
