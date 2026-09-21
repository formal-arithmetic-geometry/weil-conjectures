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
* `AlgebraicGeometry.IsAffineOpen.ringKrullDim_eq_topologicalKrullDim`: consequently the sections
  over a nonempty affine open have Krull dimension the dimension of the whole scheme.
* `AlgebraicGeometry.topologicalKrullDim_eq_coheight_add_topologicalKrullDim_closure`: **the
  dimension formula**, `dim X = codim z + dim (closure {z})` for a point `z` of an integral
  scheme of finite type over a field. The inequality `≤` is the dimension formula
  `height p + dim (A ⧸ p) = dim A` of `Ideal.height_add_ringKrullDim_quotient` read on an affine
  chart around `z`, the subset `Spec (A ⧸ p)` being embedded in the closure of `z`; the
  inequality `≥` holds in any sober space, and is
  `coheight_add_topologicalKrullDim_closure_le`.

The first two are stated for the `k`-algebra structure on the function field induced by the given
morphism to `Spec k`, namely `AlgebraicGeometry.Scheme.Hom.functionFieldAlgebra`.

Everything here assumes `X` integral. To use the dimension formula on an irreducible component
`Z` of a scheme that is not itself integral, equip `Z` with its reduced induced structure
`(AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Z).subscheme`, which is integral by
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal` and has the
dimension of `Z` by
`AlgebraicGeometry.Scheme.IdealSheafData.topologicalKrullDim_subscheme_vanishingIdeal`.
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
  have hchart : ∀ x : X, ∃ U : X.Opens, ∃ _ : IsAffineOpen U, ∃ _ : Nonempty U, x ∈ U := by
    intro x
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
    exact ⟨U, hU, ⟨⟨x, hx⟩⟩, hx⟩
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

include f in
/-- **The dimension of an integral scheme of finite type over a field is computed on any nonempty
affine chart**: the Krull dimension of the sections over a nonempty affine open is the dimension
of the whole scheme. -/
theorem IsAffineOpen.ringKrullDim_eq_topologicalKrullDim {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : ringKrullDim Γ(X, U) = topologicalKrullDim X := by
  let _ := f.functionFieldAlgebra
  rw [hU.ringKrullDim_eq_trdeg_functionField f, topologicalKrullDim_eq_trdeg_functionField f]

include f in
/-- **The dimension formula on the closure of a point.**

If `X` is an integral scheme locally of finite type over a field `k` and `z` is a point of `X`,
then `dim X = codim z + dim (closure {z})`, the codimension of `z` being `Order.coheight z`. -/
theorem topologicalKrullDim_eq_coheight_add_topologicalKrullDim_closure (z : X) :
    topologicalKrullDim X =
      (coheight z : WithBot ℕ∞) + topologicalKrullDim (closure {z} : Set X) := by
  refine le_antisymm ?_ (coheight_add_topologicalKrullDim_closure_le z)
  -- both terms on the right are read on an affine chart `U` around `z`
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top z)
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  let _ := f.sectionsAlgebra U
  have : Algebra.FiniteType k Γ(X, U) := f.finiteType_sections hU
  set p := hU.primeIdealOf ⟨z, hzU⟩
  have hzp : hU.fromSpec p = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  -- the closure of `z` inside the chart is the image of `Spec (A ⧸ p)`, a subset of `closure {z}`
  have hquot : ringKrullDim (Γ(X, U) ⧸ p.asIdeal) ≤
      topologicalKrullDim (closure {z} : Set X) := by
    -- `Spec (A ⧸ p)` is closed in `Spec A`, which is open in `X`, so the composite is inducing
    let g : PrimeSpectrum (Γ(X, U) ⧸ p.asIdeal) → PrimeSpectrum Γ(X, U) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal)
    have hg : Topology.IsClosedEmbedding g :=
      PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    refine (hU.fromSpec.isOpenEmbedding.isInducing.comp
      hg.isInducing).topologicalKrullDim_le_of_range_subset ?_
    -- and its image is the closure of `p`, whose image in `X` is contained in the closure of `z`
    rintro _ ⟨q, rfl⟩
    have hq : g q ∈ closure {p} := by
      rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.mem_zeroLocus,
        ← Ideal.mk_ker (I := p.asIdeal)]
      exact Ideal.ker_le_comap _
    have himg := image_closure_subset_closure_image (s := {p}) hU.fromSpec.continuous ⟨g q, hq, rfl⟩
    rwa [Set.image_singleton, hzp] at himg
  rw [← hU.ringKrullDim_eq_topologicalKrullDim f,
    ← Ideal.height_add_ringKrullDim_quotient k p.asIdeal,
    hU.coheight_eq_height_primeIdealOf ⟨z, hzU⟩]
  exact add_le_add le_rfl hquot

end AlgebraicGeometry
