/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.ZetaSeries
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.PointCount
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-!
# Dimension of an irreducible closed subset

Source: Stacks Project, Varieties, Tags 0A21 and 0B1C,
`lemma-dimension-locally-algebraic` (6), applied to the reduced induced closed subscheme
(blueprint: lem-sc-closed-irreducible-dimension-trdeg).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The affine-chart part of Stacks 0A21(6), with the canonical residue-field algebra. -/
private theorem integral_dimension_trdeg
    {K : Type u} [Field K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim Y = (d : WithBot ℕ∞) ∧
      @Algebra.trdeg K (Y.residueField (genericPoint Y)) _ _
        (f.residueFieldAlgebraMap (genericPoint Y)).toAlgebra = (d : Cardinal) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨genericPoint Y, hyU⟩⟩
  let φ : K →+* Γ(Y, U) :=
    (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := φ.toAlgebra
  have : Algebra.FiniteType K Γ(Y, U) := hU.algebra_finiteType_of_field f
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : Algebra K Y.functionField := ((Y.germToFunctionField U).hom.comp φ).toAlgebra
  have : IsScalarTower K Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨d, hd, htr, -⟩ :=
    finiteType_domain_ringKrullDim_eq_trdeg (k := K) (S := Γ(Y, U))
  refine ⟨d, ?_, ?_⟩
  · rw [← topologicalKrullDim_opens_eq f U, hU.topologicalKrullDim_eq]
    exact hd
  · let := (f.residueFieldAlgebraMap (genericPoint Y)).toAlgebra
    let e : Y.functionField ≃ₐ[K] Y.residueField (genericPoint Y) :=
      { RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
          ⟨(Y.residue (genericPoint Y)).hom.injective, Y.residue_surjective _⟩ with
        commutes' c := by
          change Y.residue (genericPoint Y)
            (Y.germToFunctionField U (φ c)) = f.residueFieldAlgebraMap _ c
          have hm :
              CommRingCat.ofHom (algebraMap (CommRingCat.of K)
                (f (genericPoint Y)).asIdeal.ResidueField) ≫
                  (Scheme.Spec.residueFieldIso (.of K) (f (genericPoint Y))).inv ≫
                    f.residueFieldMap (genericPoint Y) =
                (Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ U (by simp) ≫
                  Y.presheaf.germ U (genericPoint Y) hyU ≫ Y.residue _ := by
            rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
              Scheme.residue_residueFieldMap, Scheme.Hom.appLE]
            simp only [Category.assoc]
            rw [Y.presheaf.germ_res_assoc, Scheme.Hom.germ_stalkMap_assoc]
          exact (congrArg (fun g ↦ g.hom c) hm).symm }
    rw [← e.trdeg_eq,
      ← ((FractionRing.algEquiv Γ(Y, U) Y.functionField).restrictScalars K).trdeg_eq]
    exact htr

/-- A nonempty irreducible closed subset of a finite type scheme over a field has dimension
 equal to the transcendence degree of its generic residue field. Both are represented by
 the same natural number, with their respective casts.
Source: Stacks Project, Varieties, Tags 0A21 and 0B1C, part (6).
(blueprint: lem-sc-closed-irreducible-dimension-trdeg)

Proof:
1. Give `C` its reduced induced closed subscheme structure `Y` using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. The closed immersion identifies `Y`
   homeomorphically with `C` (`def-weil-closed-immersion`), so `Y` is integral
   (`def-pc-integral-scheme`) and its generic point lies over `η`. The dimensions agree by
   `lem-weil-pbc-homeomorphism-krull-dimension`.
2. The closed immersion is locally of finite type by
   `lem-weil-pbc-immersion-base-change-lft`. Composing with the structure morphism preserves
   this property by `lem-weil-pbc-proper-fp-permanence` (e).
3. Choose a nonempty affine neighbourhood `Spec A` of the generic point in `Y`. Its ring is
   a finite type domain over `K` (`def-weil-finite-type-morphism`, `def-pc-integral-scheme`).
   By `lem-sc-integral-locally-algebraic-opens-dimension` it has dimension `dim Y`; use
   `lem-weil-pbc-homeomorphism-krull-dimension` and `def-weil-pbc-krull-dimension-ring` to
   identify this with `dim A`.
4. By `lem-sc-integral-function-field-affine-fraction`, the generic stalk is a fraction
   field of `A`, compatibly with `K`. It is a field, so quotienting by its maximal ideal
   zero identifies it with the generic residue field (`def-weil-residue-field`).
5. Apply `lem-weil-pbc-finite-type-domain-dimension-trdeg` to obtain the finite common
   value of `dim A` and the transcendence degree of that fraction field.
6. The isomorphism of generic residue fields from
   `lem-weil-pbc-closed-immersion-residue-field-iso` respects `K`. It preserves polynomial
   relations, hence algebraic independence and transcendence degree
   (`def-kun-transcendence-degree`). Substitute into step 5. -/
theorem topologicalKrullDim_closed_irreducible_eq_trdeg
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (C : Set X) (hC : IsClosed C) (hCi : IsIrreducible C)
    (η : X) (hηC : η ∈ C) (hη : closure ({η} : Set X) = C) :
    ∃ d : ℕ, topologicalKrullDim C = (d : WithBot ℕ∞) ∧
      @Algebra.trdeg K (X.residueField η) _ _
        ((X ↘ Spec (.of K)).residueFieldAlgebraMap η).toAlgebra = (d : Cardinal) := by
  classical
  let T : TopologicalSpace.Closeds X := ⟨C, hC⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let Y := I.subscheme
  let i : Y ⟶ X := I.subschemeι
  have hrange : Set.range i = C := by
    exact (Scheme.IdealSheafData.reduced_induced_closed_subscheme X T).2.2.2.2.2.1
  let e : Y ≃ₜ C := i.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.mp hCi
  have : IrreducibleSpace Y := e.irreducibleSpace_iff.mpr inferInstance
  have : IsReduced Y :=
    (Scheme.IdealSheafData.reduced_induced_closed_subscheme X T).2.2.2.1
  have : IsIntegral Y :=
    (isIntegral_iff_irreducibleSpace_and_isReduced Y).mpr ⟨inferInstance, inferInstance⟩
  have hgeneric : i (genericPoint Y) = η := by
    have h := (genericPoint_spec Y).image i.continuous
    rw [Set.image_univ, hrange, hC.closure_eq] at h
    exact h.eq hη
  obtain ⟨d, hd, htr⟩ := integral_dimension_trdeg Y (i ≫ (X ↘ Spec (.of K)))
  refine ⟨d, ?_, ?_⟩
  · exact (e.isHomeomorph.topologicalKrullDim_eq e).symm.trans hd
  · let f := X ↘ Spec (.of K)
    let := (f.residueFieldAlgebraMap (i (genericPoint Y))).toAlgebra
    let := ((i ≫ f).residueFieldAlgebraMap (genericPoint Y)).toAlgebra
    have : IsIso (i.residueFieldMap (genericPoint Y)) :=
      Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion i _
    let er : X.residueField (i (genericPoint Y)) ≃ₐ[K]
        Y.residueField (genericPoint Y) :=
      { (asIso (i.residueFieldMap (genericPoint Y))).commRingCatIsoToRingEquiv with
        commutes' c := by
          change _ = (i ≫ f).residueFieldAlgebraMap (genericPoint Y) c
          rw [Scheme.Hom.residueFieldAlgebraMap_comp]
          rfl }
    have hr := er.trdeg_eq.trans htr
    subst η
    exact hr

end AlgebraicGeometry
