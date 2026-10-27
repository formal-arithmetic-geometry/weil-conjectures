/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-!
# Tensor products with locally free module objects

Let `Λ` be a commutative condensed ring and `X` a scheme. For a locally free module object `P`
over `Λ_X` (`ProEtale.IsLocallyFree`):

* the pullback `g^* P` along any morphism `g` is locally free
  (`ProEtale.IsLocallyFree.upperStar`);
* `P ⊗ N` is pro-étale locally finitely presented, resp. constructible, if `N` is
  (`ProEtale.IsLocallyFree.isLocallyFinitelyPresented_tensorObj`,
  `ProEtale.IsLocallyFree.isConstructibleModuleObject_tensorObj`);
* `P` is flat, so the derived tensor product `P[0] ⊗ᴸ N[n]` is `(P ⊗ N)[n]`
  (`ProEtale.IsLocallyFree.nonempty_singleFunctor_tensorObj_iso`);
* `P[q]` is dualizable in `D(Mod_{Λ_X})`, with dual `P'[-q]` for a locally free `P'`
  (`ProEtale.IsLocallyFree.exists_exactPairing_singleFunctor`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {Λ} in
/-- Local freeness is invariant under isomorphism. -/
lemma IsLocallyFree.of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsLocallyFree (condensedRingObj Λ X) N :=
  sorry

/-- The pullback `g^*` of module objects over `Λ` preserves local freeness. -/
lemma IsLocallyFree.upperStar {W X : Scheme.{u}} (g : W ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFree (condensedRingObj Λ X) M) :
    IsLocallyFree (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M) :=
  sorry

variable {Λ} in
/-- The tensor product of a locally free and a pro-étale locally finitely presented module object
is pro-étale locally finitely presented. -/
lemma IsLocallyFree.isLocallyFinitelyPresented_tensorObj {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (hN : IsLocallyFinitelyPresented (condensedRingObj Λ X) N) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) (P ⊗ N) :=
  sorry

variable {Λ} in
/-- The tensor product of a locally free and a constructible module object is constructible. -/
lemma IsLocallyFree.isConstructibleModuleObject_tensorObj {X : Scheme.{u}}
    {P N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (hN : IsConstructibleModuleObject (condensedRingObj Λ X) N) :
    IsConstructibleModuleObject (condensedRingObj Λ X) (P ⊗ N) :=
  sorry

variable {Λ} in
/-- A locally free module object `P` is flat, so the derived tensor product of `P[0]` and
`N[n]` is `(P ⊗ N)[n]`. -/
lemma IsLocallyFree.nonempty_singleFunctor_tensorObj_iso {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) (n : ℤ) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj P ⊗
        (DerivedCategory.singleFunctor _ n).obj N ≅
      (DerivedCategory.singleFunctor _ n).obj (P ⊗ N)) :=
  sorry

variable {Λ} in
/-- A locally free module object `P` placed in degree `q` is dualizable in `D(Mod_{Λ_X})`: it has
a left dual `P'[-q]` with `P'` locally free. -/
lemma IsLocallyFree.exists_exactPairing_singleFunctor {X : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : IsLocallyFree (condensedRingObj Λ X) P) (q : ℤ) :
    ∃ P' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      IsLocallyFree (condensedRingObj Λ X) P' ∧
        Nonempty (ExactPairing ((DerivedCategory.singleFunctor _ (-q)).obj P')
          ((DerivedCategory.singleFunctor _ q).obj P)) :=
  sorry

/-- The unit `Λ_X` of the module objects over `Λ_X` is locally free (indeed free of rank one). -/
lemma isLocallyFree_tensorUnit (X : Scheme.{u}) :
    IsLocallyFree (condensedRingObj Λ X)
      (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  sorry

end AlgebraicGeometry.ProEtale
