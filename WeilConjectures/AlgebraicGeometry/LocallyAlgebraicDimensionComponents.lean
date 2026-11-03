/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Irreducible
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.RingTheory.DimensionAtPointComponents

/-!
# Local dimension as the maximum of component dimensions

Source: Stacks Project, Varieties, Tag 0B1B, the first equality in part (5) of
Lemma 33.20.3 (Tag 0A21).
(blueprint: lem-trf-locally-algebraic-dimension-components)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem dimensionAt_le_of_isInducing {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {g : A → B}
    (hg : Topology.IsInducing g) (a : A) :
    topologicalKrullDimAt a ≤ topologicalKrullDimAt (g a) := by
  refine le_iInf₂ fun U ha ↦ ?_
  let V : TopologicalSpace.Opens A := ⟨g ⁻¹' U, U.isOpen.preimage hg.continuous⟩
  exact (iInf₂_le V ha).trans (hg.restrictPreimage (U : Set B)).topologicalKrullDim_le

private theorem dimensionAt_homeomorph {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (a : A) :
    topologicalKrullDimAt a = topologicalKrullDimAt (e a) := by
  refine le_antisymm (dimensionAt_le_of_isInducing e.isInducing a) ?_
  simpa only [e.symm_apply_apply] using
    dimensionAt_le_of_isInducing e.symm.isInducing (e a)

/-- For a scheme locally of finite type over a field, local topological dimension is the
attained maximum of the dimensions of its irreducible components through the point.
Components carry the subspace topology. The existential clause also asserts nonemptiness.

Source: Stacks Project, Varieties, Tag 0B1B, the first equality in part (5) of
Lemma 33.20.3 (Tag 0A21).
(blueprint: lem-trf-locally-algebraic-dimension-components)

Proof:
1. Pulling back open neighbourhoods along an inducing map and using dimension monotonicity
   shows that local dimension decreases under inducing maps. Applying this in both directions
   proves invariance under homeomorphisms.
2. Give each component C through x its reduced induced closed subscheme structure j : Y → X.
   This is irreducible and locally of finite type over k. For y mapping to x, the irreducible
   locally algebraic dimension theorem gives dim C = dim Y = dim_y Y. Step 1 bounds this by
   dim_x X, proving the first clause.
3. Choose an affine neighbourhood U = Spec B of x. Its coordinate ring is finite type over k.
   Homeomorphism invariance and open-subspace invariance identify dim_x X with dim_p Spec B.
   The affine component formula supplies a component D through p attaining this dimension.
4. The image of D under Spec B ≅ U → X is irreducible, hence lies in a component C of X.
   This C contains x, and the induced embedding D → C gives dim_x X = dim D ≤ dim C.
   The bound from step 2 gives the reverse inequality, so C attains the maximum.
   If X is empty, there is no x and the assertion is vacuous. -/
theorem topologicalKrullDimAt_eq_max_component_dimension
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    (∀ C : Set X, C ∈ irreducibleComponents X → x ∈ C →
      topologicalKrullDim C ≤ topologicalKrullDimAt x) ∧
    (∃ C : Set X, C ∈ irreducibleComponents X ∧ x ∈ C ∧
      topologicalKrullDim C = topologicalKrullDimAt x) := by
  classical
  have hbound (C : Set X) (hC : C ∈ irreducibleComponents X) (hxC : x ∈ C) :
      topologicalKrullDim C ≤ topologicalKrullDimAt x := by
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨C, isClosed_of_mem_irreducibleComponents C hC⟩ : TopologicalSpace.Closeds X)
    let j := I.subschemeι
    have hrange : Set.range j = C := by
      simp [j, I]
    let e : I.subscheme ≃ₜ C :=
      j.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    have : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.mp hC.1
    have : IrreducibleSpace I.subscheme := e.irreducibleSpace_iff.mpr inferInstance
    let : I.subscheme.Over (Spec (.of k)) := ⟨j ≫ f⟩
    have : LocallyOfFiniteType (I.subscheme ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (j ≫ f))
    obtain ⟨y, hy⟩ := (hrange ▸ hxC : x ∈ Set.range j)
    calc
      topologicalKrullDim C = topologicalKrullDim I.subscheme :=
        (e.isHomeomorph.topologicalKrullDim_eq e).symm
      _ = topologicalKrullDimAt y :=
        ((dimension_locally_algebraic (k := k) I.subscheme).2 y).symm
      _ ≤ topologicalKrullDimAt (j y) :=
        dimensionAt_le_of_isInducing j.isEmbedding.isInducing y
      _ = topologicalKrullDimAt x := congrArg topologicalKrullDimAt hy
  refine ⟨hbound, ?_⟩
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let R := Γ(X, U)
  let : Algebra k R :=
    ((f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k R := hU.algebra_finiteType_of_field f
  let e : U ≃ₜ Spec (.of R) := hU.isoSpec.hom.homeomorph
  let p : PrimeSpectrum R := e ⟨x, hxU⟩
  have : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨qs, hqs, hne, n, hn, _, ⟨D, hD, hpD, hDn⟩, _⟩ :=
    dimension_at_point_components (k := k) p.asIdeal
  have hlocal : topologicalKrullDimAt p = topologicalKrullDimAt x :=
    (dimensionAt_homeomorph e ⟨x, hxU⟩).symm.trans
      (U.isOpen.topologicalKrullDimAt_eq hxU)
  let g : PrimeSpectrum R → X := fun q ↦ (e.symm q).val
  have hg : Topology.IsOpenEmbedding g := U.isOpenEmbedding'.comp e.symm.isOpenEmbedding
  obtain ⟨C, hC, hDC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (g '' D) (hD.1.image g hg.continuous.continuousOn)
  have hgp : g p = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hxU⟩)
  have hxC : x ∈ C := hgp ▸ hDC ⟨p, hpD, rfl⟩
  have hdim : topologicalKrullDim D ≤ topologicalKrullDim C :=
    ((hg.isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal).codRestrict
      (fun q : D ↦ hDC ⟨q.val, q.property, rfl⟩)).topologicalKrullDim_le
  refine ⟨C, hC, hxC, le_antisymm (hbound C hC hxC) ?_⟩
  exact hlocal.symm.le.trans (hn.le.trans (hDn.symm.le.trans hdim))

end AlgebraicGeometry
