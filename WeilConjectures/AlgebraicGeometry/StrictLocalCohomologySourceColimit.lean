/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
import WeilConjectures.AlgebraicGeometry.DerivedCohomologyGermIso

/-! # Canonical derived sections and strict-local cohomology germs

 The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical strict-local source cocone is colimiting. -/
theorem isColimit_strictLocalCohomologySourceLegs {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (IsColimit (Cocone.mk _ (strictLocalCohomologySourceLegs s L n))) := by
  let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
  have : N.Initial := (Scheme.strictHenselizationAffineProperties s).1
  let P := strictLocalCohomologyPresheaf L n
  let c := ((Scheme.pointSmallEtale s).presheafFiberCocone P).whisker N.op
  have hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P)
  let u := (Scheme.pointSmallEtale s).presheafFiber.map
    (strictLocalCohomologyGermMap L n) ≫ (strictLocalCohomologySourceIso s L n).hom
  have := isIso_strictLocalCohomologyGermMap s L n
  have : IsIso u := by dsimp [u]; infer_instance
  refine ⟨hc.ofIsoColimit (Cocone.ext (asIso u) (fun j ↦ ?_))⟩
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Etale
