/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.FinitePresentationColimit

/-! # Finitely presented models over a directed preorder

## References

* Stacks Project, Algebra, Tag 05N7, object clause
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ModuleCat

/-- The object clause of finite-presentation descent for a nonempty directed preorder. -/
theorem exists_finitePresentation_model_of_preorder_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (X : ModuleCat.{u} (colimit F : CommRingCat.{u}))
    (hX : Module.FinitePresentation (colimit F : CommRingCat.{u}) X) :
    ∃ (i : I) (M : ModuleCat.{u} (F.obj i)),
      Module.FinitePresentation (F.obj i) M ∧
      Nonempty ((extendScalars (colimit.ι F i).hom).obj M ≅ X) := by
  classical
  let T := ThinSkeleton I
  let E : T ⥤ I := ThinSkeleton.fromThinSkeleton I
  have : IsFiltered T := IsFiltered.of_equivalence (ThinSkeleton.equivalence I).symm
  have : Nonempty T := IsFiltered.nonempty
  have : IsDirected T (· ≤ ·) := IsFiltered.isDirectedOrder T
  let G := E ⋙ F
  let q : colimit G ≅ colimit F := Functor.Final.colimitIso E F
  let A := (colimit F : CommRingCat.{u})
  let B := (colimit G : CommRingCat.{u})
  let Y : ModuleCat.{u} B := (extendScalars q.inv.hom).obj X
  have : Module.FinitePresentation A X := hX
  let : Algebra A B := q.inv.hom.toAlgebra
  have hY : Module.FinitePresentation B Y := by
    change Module.FinitePresentation B (B ⊗[A] X)
    infer_instance
  obtain ⟨t, M, hM, ⟨eM⟩⟩ :=
    (finitePresentation_descent_directedColimit.{u, u, u, u} G).1 Y hY
  have hcomp : q.hom.hom.comp (colimit.ι G t).hom = (colimit.ι F (E.obj t)).hom :=
    congrArg CommRingCat.Hom.hom (Functor.Final.ι_colimitIso_hom E F t)
  let ecomp : (extendScalars (colimit.ι F (E.obj t)).hom).obj M ≅
      (extendScalars q.hom.hom).obj ((extendScalars (colimit.ι G t).hom).obj M) :=
    (eqToIso (congrArg (fun r ↦ (extendScalars r).obj M) hcomp)).symm ≪≫
      (extendScalarsComp (colimit.ι G t).hom q.hom.hom).app M
  have hinv : q.hom.hom.comp q.inv.hom = RingHom.id A :=
    congrArg CommRingCat.Hom.hom q.inv_hom_id
  let ecancel : (extendScalars q.hom.hom).obj Y ≅ X :=
    ((extendScalarsComp q.inv.hom q.hom.hom).app X).symm ≪≫
      eqToIso (congrArg (fun r ↦ (extendScalars r).obj X) hinv) ≪≫
      (extendScalarsId A).app X
  exact ⟨E.obj t, M, hM,
    ⟨ecomp ≪≫ (extendScalars q.hom.hom).mapIso eM ≪≫ ecancel⟩⟩

end ModuleCat
