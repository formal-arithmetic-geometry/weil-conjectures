/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Closed immersions descend over qcqs scheme limits

Source: Stacks Project, Limits of Spaces, Situation 084W and Tag 0850;
Morphisms of Spaces, Tag 05WT (blueprint: lem-sfb-space-qcqs-base-descend-closed-immersion).

All spaces are over the terminal scheme Spec Z, represented in universe u by Spec (ULift Z).
A limiting cone in schemes over this terminal scheme is equivalently a scheme limit.
Finite presentation uses the existing quasi-compactness and quasi-separatedness predicates,
and the existing local finite-presentation chart predicate.
Base changes are the canonical pullbacks of the given morphism in the presheaf slice.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A closed immersion at the limit descends to a stage and remains a closed immersion
at every later stage, without assuming that the qcqs base schemes are affine.
Source: Stacks Project, Situation 084W and Tag 0850; Tag 05WT
(blueprint: lem-sfb-space-qcqs-base-descend-closed-immersion).

Proof:
1. By [lem-sfb-space-fp-qcqs-source], both initial spaces are qcqs. Their structure
   maps are locally finitely presented; the target structure map is locally of finite
   type since finitely presented algebras are finitely generated. Apply
   [lem-sfb-space-relative-lfp-permanence] to obtain local finite presentation, hence
   local finite type, of the given map.
2. Choose a finite affine open cover of the initial base using [def-pc-scheme] and
   [def-weil-pbc-quasi-compact-scheme]. Restrict to the cofinal tail above the initial
   index. Pull these opens back to every stage and the limit. The stage opens are affine,
   since transition maps are affine; [lem-weil-pbc-limit-affine-transition] identifies
   their inverse limits with the corresponding opens of the limit base.
3. Restrict the spaces and map to each open. The affine bases are qcqs by
   [lem-weil-pbc-affine-scheme-qcqs]; [lem-sfb-space-qcqs-source-products] gives qcqs
   source and target. Local finite type restricts on the same scheme charts.
4. Closed immersions persist under arbitrary base change: each scheme test of the
   new map is a scheme test of the old map, by fibre-product associativity in
   [lem-trf-space-fibre-products-etale-covers]. Scheme base change preserves closed
   immersions by [lem-weil-pbc-proper-fp-permanence]. Thus each limit restriction is closed.
5. Apply [lem-sfb-space-descend-closed-immersion] to each affine base system. Choose
   a common upper bound of the finitely many resulting indices by directedness.
   Step 4 makes all restricted maps closed at that stage. For an empty affine cover,
   take the initial index itself.
6. Choose an etale scheme atlas of the stage target by [def-trf-algebraic-space] and
   restrict it to the base opens. These maps remain etale by
   [lem-weil-pbc-open-immersion-etale] and [lem-trf-space-chartwise-etale-permanence],
   and are jointly surjective. Their source pullbacks are schemes closed in the atlas
   opens, by step 5 and fibre-product associativity. Apply
   [lem-sfb-space-closed-immersion-atlas-locality], including for the empty cover, to
   obtain representability and closedness on every scheme test. Step 4 gives closedness
   at every later stage. No representability of the original stage map is assumed. -/
theorem eventually_closedImmersion_of_qcqs_scheme_limit
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (hqc : ∀ j : Jᵒᵖ, CompactSpace (D.obj j).left)
    (hqs : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (D.obj j).left)
    (haff : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left)
    (c : Cone D) (hc : IsLimit c) (j₀ : J)
    (Y₀ Z₀ : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (pY : Y₀.obj.obj ⟶ yoneda.obj (D.obj (op j₀)))
    (pZ : Z₀.obj.obj ⟶ yoneda.obj (D.obj (op j₀)))
    (h₀ : Over.mk pY ⟶ Over.mk pZ)
    (hYqc : MapIsQuasiCompact pY)
    (hYqs : MapIsQuasiSeparated pY)
    (hYlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y₀ (D.obj (op j₀)) pY)
    (hZqc : MapIsQuasiCompact pZ)
    (hZqs : MapIsQuasiSeparated pZ)
    (hZlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) Z₀ (D.obj (op j₀)) pZ)
    (hclosed : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (((Over.pullback (yoneda.map (c.π.app (op j₀)))).map h₀).left)) :
    ∃ (j : J) (hj : j₀ ≤ j),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (((Over.pullback (yoneda.map (D.map (homOfLE hj).op))).map h₀).left) ∧
      ∀ (k : J) (hk : j ≤ k),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
          (((Over.pullback
            (yoneda.map (D.map (homOfLE (le_trans hj hk)).op))).map h₀).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
