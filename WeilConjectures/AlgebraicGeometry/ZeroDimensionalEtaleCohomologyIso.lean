/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalSectionsStalks

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical degree-zero comparison followed by the product of the chosen
geometric stalk germs is invertible.
-/
theorem zero_dimensional_etale_cohomology_iso
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Ω : C → Type u) [∀ x, Field (Ω x)] [∀ x, IsAlgClosed (Ω x)]
    (s : ∀ x : C, Spec (.of (Ω x)) ⟶ C)
    (hs : ∀ x : C, (s x).base.hom default = x) :
    IsIso ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}) F 0).hom ≫
          (Functor.rightDerivedZeroIsoSelf
            (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app F ≫
          F.ΓRes (op (Scheme.Etale.mk (𝟙 C))) ≫ Pi.lift (fun x : C =>
            (Scheme.pointSmallEtale (s x)).toPresheafFiber
              (Scheme.Etale.mk (𝟙 C))
              (Over.homMk (s x) (Category.comp_id (s x))) F.obj)) := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : IsSeparated (C ↘ Spec (.of k)) := inferInstanceAs (IsSeparated f)
  let : LocallyOfFiniteType (C ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  let : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  have hg := (Scheme.zeroDimensional_sections_stalks.{u, u}
    k C hdim Ω s hs).2.1 F
  have hr : IsIso (F.ΓRes (op (Scheme.Etale.mk (𝟙 C)))) :=
    F.isLimitConeΓ.isIso_π_app_of_isInitial _
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale C).op
  infer_instance

end AlgebraicGeometry
