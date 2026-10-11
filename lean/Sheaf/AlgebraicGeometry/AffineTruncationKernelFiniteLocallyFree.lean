/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Finite local freeness of an affine truncation kernel

Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, proof of Lemma 36.13.6
(the DAG source calls this Tag 08ED)
(blueprint: lem-sc-affine-truncation-kernel-finite-locally-free).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry


/-- Below the Tor-amplitude bound, the image of the preceding differential restricts to
its successor's kernel, and is flat, finitely presented and finite locally free on U.
The kernel/image assertion is only on U, never on the entire affine scheme.
Source: Stacks Project, Tag 08EG, proof of Lemma 36.13.6
(blueprint: lem-sc-affine-truncation-kernel-finite-locally-free).

Proof:
1. The affine Tor-amplitude criterion (lem-pc-affine-tor-amplitude-criterion) identifies
   the sheaf and module formulations on principal opens contained in U.
2. Since r < a, cohomology vanishes at r on U. Thus the image of the preceding
   differential is the kernel of the next differential after restriction to U.
3. On each principal open D(f) contained in U, lem-sc-affine-truncation-kernel-flat
   gives a flat finitely presented localization of the image module. The finite
   presentation also follows by writing it as the cokernel of P^(r-2) → P^(r-1).
   By lem-weil-pbc-finitely-presented-flat-module-projective (Tag 00NX) it is finite
   projective. By lem-weil-pbc-finite-projective-standard-free-cover it has a finite
   standard-open free cover. These covers give finite local freeness on U; flatness
   and finite presentation are local and give the other two asserted properties. -/
theorem affine_truncationKernel_finiteLocallyFree (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) (hU : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hbounded : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i) ∧ Module.Finite A (P.X i))
    (E : schemeDerivedCategory U.toScheme) (hperfect : Scheme.IsPerfect U.toScheme E)
    (hrep : Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ _ _
          ((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
            SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv U))
          ⟨fun _ _ ↦ by simp⟩ (ComplexShape.up ℤ)).obj P) ≅ E))
    (a b : ℤ) (hab : a ≤ b)
    (htor : ∀ G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes U.toScheme E G i)
    (r : ℤ) (hr : r < a) :
    (∃ e : ((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r)) ≅
      kernel (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).map (P.d r (r + 1))),
      e.hom ≫ kernel.ι (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).map (P.d r (r + 1))) =
        ((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).map (image.ι (P.d (r - 1) r))) ∧
    SheafOfModules.IsFlat (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r))) ∧
    SheafOfModules.IsFinitePresentation (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r))) ∧
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj (image (P.d (r - 1) r))) := by
  sorry

end AlgebraicGeometry
