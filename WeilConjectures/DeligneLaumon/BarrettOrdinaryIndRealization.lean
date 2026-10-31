/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Ordinary constructible realization and inverse image

Source: Barrett, arXiv:2005.10859, Theorem 1.1; Categories and Sheaves, §15.3.
(blueprint: lem-zl-barrett-ordinary-ind-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v wX wY
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The ordinary realization before adjoining Frobenius or testing isomorphisms.
Source: Barrett, arXiv:2005.10859, Theorem 1.1 and §3; Categories and Sheaves,
§15.3; the finite-open-cover extension in lem-zl-barrett-ind-realization, steps 1–2.
(blueprint: lem-zl-barrett-ordinary-ind-realization).

Proof: at each finite coefficient extension over Q_l, Barrett identifies bounded
constructible complexes on a separated geometric fibre with the bounded derived
category of its constructible heart. Compose with the exact Yoneda embedding into
ind-objects. A bounded roof and the finitely many exactness relations needed for its
composition descend to one filtered stage; this proves full faithfulness of the
bounded derived Yoneda embedding. The construction sends a heart object to its
Yoneda image in degree zero and commutes with cohomology. Applying it to a heart
object in any degree proves the displayed coverage by single complexes.

Exact inverse image on hearts extends by filtered colimits to the specified Kan
extension L. Filtered colimits are exact in the ind-category, so L is exact; it
preserves all colimits, hence has its ind right adjoint. Applying inverse image
termwise gives the comparison with L on bounded complexes. The Kan unit identifies
its restriction to the heart. Coefficient extension has the same termwise formula,
so roofs, maps, and comparison equations descend to common coefficient stages.
For a nonseparated finite-type fibre, use a finite affine open cover and its finite
Cech resolution. Intersections are separated and quasi-compact. The restrictions
of the comparisons agree on overlaps by their common termwise construction; the
finite resolutions glue full faithfulness, heart and cohomology formulas, and the
inverse-image comparison. Shifting the heart complexes gives coverage in every
integer degree. Empty fibres and zero objects use the same construction. -/
theorem zlBarrettOrdinaryIndRealization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [HasDerivedCategory.{wX} (Ind (zlSmallHeart D l Ω hl X₀))]
    [HasDerivedCategory.{wY} (Ind (zlSmallHeart D l Ω hl Y₀))] (f : X₀ ⟶ Y₀) :
    let L := zlIndMap (zlSmallPull D l hl Ω f)
    ∃ (_ha : L.Additive) (_hlim : PreservesFiniteLimits L)
      (_hcolim : PreservesFiniteColimits L) (_hadj : L.IsLeftAdjoint)
      (JX : generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber X₀).left ⥤
        DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl X₀)))
      (JY : generalAlgebraicallyClosedConstructibleCategory l Ω
        (D.geometricFiber Y₀).left ⥤
        DerivedCategory.Plus (Ind (zlSmallHeart D l Ω hl Y₀))),
      Nonempty JX.FullyFaithful ∧ Nonempty JY.FullyFaithful ∧
      (∀ A : zlSmallHeart D l Ω hl X₀,
        Nonempty (JX.obj (AsSmall.down.obj A).obj ≅
          (DerivedCategory.Plus.singleFunctor _ 0).obj (Ind.yoneda.obj A))) ∧
      (∀ (K : generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber Y₀).left) (n : ℤ),
        ∃ A : zlSmallHeart D l Ω hl Y₀,
          Nonempty (Ind.yoneda.obj A ≅
            (DerivedCategory.Plus.homologyFunctor _ n).obj (JY.obj K))) ∧
      (∀ (A : zlSmallHeart D l Ω hl Y₀) (n : ℤ),
        ∃ B, Nonempty (JY.obj B ≅
          (DerivedCategory.Plus.singleFunctor _ n).obj (Ind.yoneda.obj A))) ∧
      Nonempty (zlPull D l hl Ω f ⋙ JX ≅ JY ⋙ L.mapDerivedCategoryPlus) := by
  sorry

end WeilConjectures
