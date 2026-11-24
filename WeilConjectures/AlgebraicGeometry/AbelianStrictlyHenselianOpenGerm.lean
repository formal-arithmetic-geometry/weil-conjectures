/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Abelian sections on a strictly henselian open neighbourhood

## References

* Stacks Project, Tags 03QO, 03S2 and 03Q1
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Sections of an abelian etale sheaf on a strictly henselian open neighbourhood
identify with its geometric stalk at the closed point (Stacks, Tags 03QO, 03S2 and 03Q1). -/
theorem strictlyHenselianOpen_abelian_germ_isIso
    {T : Scheme.{u}} (U : T.Opens)
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) (e : U.toScheme ≅ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (t : Spec (.of Ω) ⟶ U.toScheme) (ht : t ≫ U.ι = s)
    (hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}) :
    IsIso ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) F.obj) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, (max u v) + 1, u, (max u v) + 1} _
  let H := (sheafCompose T.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1})).obj F
  have hb := strictlyHenselianOpen_toPresheafFiber_bijective.{u, (max u v) + 1}
    U hR e s t ht hclosed H
  have hi : IsIso ((pointSmallEtale s).toPresheafFiber
      (Etale.mk U.ι) (Over.homMk t ht) H.obj) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have hcomp := (pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app
    (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1})
    (Etale.mk U.ι) (Over.homMk t ht) F.obj
  have hf : IsIso ((CategoryTheory.forget AddCommGrpCat.{(max u v) + 1}).map
      ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) F.obj)) := by
    rw [← hcomp]
    change IsIso ((pointSmallEtale s).toPresheafFiber
      (Etale.mk U.ι) (Over.homMk t ht) H.obj ≫ _)
    infer_instance
  exact isIso_of_reflects_iso _ (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1})

end AlgebraicGeometry.Scheme
