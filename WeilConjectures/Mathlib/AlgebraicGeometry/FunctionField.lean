/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties

/-!
# The dimension of an integral scheme of finite type over a field

The dimension of an integral scheme of finite type over a field `k` is the transcendence degree
over `k` of its function field. Both sides are computed on a single affine chart: the ring of
sections of a nonempty affine open is a finitely generated `k`-algebra which is a domain with
fraction field the function field, so its Krull dimension is that transcendence degree; and since
this answer does not depend on the chart, it is also the dimension of the whole scheme.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_trdeg_functionField`: `dim X` is the transcendence
  degree of `X.functionField` over `k`, for `X` an integral scheme with a morphism to `Spec k`
  that is locally of finite type.
* `AlgebraicGeometry.IsAffineOpen.ringKrullDim_eq_trdeg_functionField`: the same for the ring of
  sections of a nonempty affine open, which is the affine case of the above.

Both are stated for the `k`-algebra structure on the function field induced by the given morphism
to `Spec k`, namely `AlgebraicGeometry.Scheme.Hom.functionFieldAlgebra`.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The `R`-algebra structure on the sections over an open subset of a scheme over `Spec R`. -/
@[instance_reducible] noncomputable def Scheme.Hom.sectionsAlgebra (f : X ⟶ Spec R)
    (U : X.Opens) : Algebra R Γ(X, U) :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- The `R`-algebra structure on the function field of an irreducible scheme over `Spec R`. -/
@[instance_reducible] noncomputable def Scheme.Hom.functionFieldAlgebra [IrreducibleSpace X]
    (f : X ⟶ Spec R) :
    Algebra R X.functionField :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra

/-- The restriction maps to the function field are maps of `R`-algebras. -/
lemma Scheme.Hom.isScalarTower_functionField [IrreducibleSpace X] (f : X ⟶ Spec R) (U : X.Opens)
    [Nonempty U] :
    letI := f.sectionsAlgebra U
    letI := f.functionFieldAlgebra
    IsScalarTower R Γ(X, U) X.functionField := by
  let _ := f.sectionsAlgebra U
  let _ := f.functionFieldAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  change ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom =
    (X.germToFunctionField U).hom.comp
      ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appLE]
  simp [Scheme.germToFunctionField]

/-- The sections over an affine open of a scheme locally of finite type over `Spec R` form a
finitely generated `R`-algebra. -/
lemma Scheme.Hom.finiteType_sections (f : X ⟶ Spec R) [LocallyOfFiniteType f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    Algebra.FiniteType R Γ(X, U) := by
  have h1 : RingHom.FiniteType (f.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE (@LocallyOfFiniteType) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.FiniteType ((Scheme.ΓSpecIso R).inv).hom :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

/-- The dimension of an affine open of a scheme is the Krull dimension of its ring of sections. -/
lemma IsAffineOpen.topologicalKrullDim_eq {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim U.toScheme = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph

variable {k : Type u} [Field k] [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- The Krull dimension of the ring of sections of a nonempty affine open of an integral scheme
of finite type over a field `k` is the transcendence degree of the function field over `k`.

Indeed those sections form a finitely generated `k`-algebra which is a domain with fraction field
the function field. -/
theorem IsAffineOpen.ringKrullDim_eq_trdeg_functionField {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] :
    letI := f.functionFieldAlgebra
    ringKrullDim Γ(X, U) = Cardinal.toNat (Algebra.trdeg k X.functionField) := by
  let _ := f.sectionsAlgebra U
  let _ := f.functionFieldAlgebra
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sections hU
  have : IsScalarTower k Γ(X, U) X.functionField := f.isScalarTower_functionField U
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact ringKrullDim_eq_trdeg_of_isFractionRing k Γ(X, U) X.functionField

/-- **The dimension of an integral scheme of finite type over a field is the transcendence degree
of its function field.**

Every nonempty affine open has dimension the transcendence degree of the function field, and the
dimension of `X` is the supremum of the dimensions of its affine opens. -/
theorem topologicalKrullDim_eq_trdeg_functionField :
    letI := f.functionFieldAlgebra
    topologicalKrullDim X = Cardinal.toNat (Algebra.trdeg k X.functionField) := by
  let _ := f.functionFieldAlgebra
  have hchart : ∀ x : X, ∃ U : X.Opens, ∃ _ : IsAffineOpen U, ∃ _ : Nonempty U, x ∈ U :=
    fun x ↦ ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _,
      ⟨⟨x, X.affineCover.covers x⟩⟩, X.affineCover.covers x⟩
  have key : ∀ (U : X.Opens) (hU : IsAffineOpen U) (_ : Nonempty U),
      topologicalKrullDim U.toScheme =
        (Cardinal.toNat (Algebra.trdeg k X.functionField) : WithBot ℕ∞) := by
    intro U hU hne
    have := hne
    rw [hU.topologicalKrullDim_eq, hU.ringKrullDim_eq_trdeg_functionField f]
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun x ↦ ?_
    obtain ⟨U, hU, hne, hx⟩ := hchart x
    have := hne
    obtain ⟨y, hy⟩ : ∃ y : U.toScheme, U.ι.base y = x := ⟨⟨x, hx⟩, rfl⟩
    refine le_trans ?_ (le_of_eq (key U hU hne))
    rw [← hy, coheight_eq_of_isOpenImmersion U.ι, topologicalKrullDim_eq_krullDim]
    exact Order.coheight_le_krullDim y
  · obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨U, hU, hne, hx⟩ := hchart x
    rw [← key U hU hne]
    exact U.ι.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

end AlgebraicGeometry
