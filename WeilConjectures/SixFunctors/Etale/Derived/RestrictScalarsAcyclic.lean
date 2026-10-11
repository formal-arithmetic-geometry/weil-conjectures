/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.Sites.CechComplexModule
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars

/-!
# Restriction of scalars of injective étale sheaves is acyclic for the direct image

Let `φ : Λ →+* Λ'` be a morphism of rings and `g : T ⟶ S` a morphism of schemes. If `I` is an
injective étale sheaf of `Λ'`-modules on `T`, then its restriction of scalars to `Λ` is acyclic
for the direct image `g_*` on étale sheaves of `Λ`-modules: the higher direct images of a sheaf
of modules do not depend on the coefficient ring (compare [Stacks, Tag 03FD]).

The proof uses the Čech-acyclicity of `CategoryTheory.Presheaf.IsCechAcyclic`, which only
depends on the underlying abelian presheaf: it holds for injective sheaves of modules over any
ring, passes to cokernels of monomorphisms, and makes the sections of `g_*` of a short exact
sequence with Čech-acyclic kernel surjective; we conclude by
`CategoryTheory.Functor.rightAcyclic_of_epi_map_g`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option synthInstance.maxHeartbeats 400000 in
-- the instance `WEqualsLocallyBijective` on the small étale site takes long to synthesize
/-- The restriction of scalars along `φ : Λ →+* Λ'` of an injective étale sheaf of `Λ'`-modules
on `T` is acyclic for the direct image `g_*` on étale sheaves of `Λ`-modules. -/
theorem rightAcyclic_lowerStar_restrictScalars_obj_of_injective
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {T S : Scheme.{u}}
    (g : T ⟶ S) (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ')) [Injective I] :
    ((g)_*[ModuleCat.{u + 1} Λ]).rightAcyclic
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj I) :=
  Functor.rightAcyclic_of_epi_map_g ((g)_*[ModuleCat.{u + 1} Λ])
    (fun A ↦ Presheaf.IsCechAcyclic T.smallEtaleTopology (A.obj ⋙ forget₂ _ AddCommGrpCat))
    (fun A _ ↦ Sheaf.isCechAcyclic_of_injective A)
    (fun _ hS h₁ h₂ ↦ Sheaf.isCechAcyclic_X₃ hS h₁ h₂)
    (fun _ hS h₁ ↦ Sheaf.epi_of_surjective_app _ fun _ ↦
      Sheaf.surjective_app_of_isCechAcyclic hS h₁ _)
    (Sheaf.isCechAcyclic_of_injective I)

end AlgebraicGeometry.Etale
