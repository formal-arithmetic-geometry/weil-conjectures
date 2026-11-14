/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import WeilConjectures.AlgebraicGeometry.Modules.DualRetractionKey

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A local section induces a local retraction of the transpose.

Source: Stacks Project, Tag 0EKP, proof of (2) to (3), transpose compatibility.

Transport the given section through `overFunctorEquiv` to the over category.
`SheafOfModules.overHomObjIso` identifies the restricted duals with the internal Homs
of the restrictions. On every smaller open, precomposition with the section gives a
map in the reverse direction; these maps commute with restriction. Internal Hom
contravariant functoriality identifies the composite with precomposition by
`s ≫ f|_U`, which is the identity by `hs`. Conjugating by the internal-Hom restriction
isomorphisms and transporting back through `overEquiv` gives the desired retraction.
This works for arbitrary P and Q, including zero sheaves and the empty open.
-/
theorem isSplitMono_restrict_dualMap_of_local_section
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) (U : X.Opens)
    (s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P)
    (hs : s ≫ (restrictFunctor U.ι).map f = 𝟙 _) :
    IsSplitMono ((restrictFunctor U.ι).map (dualMap f))  := by
  let F := restrictFunctor U.ι
  obtain ⟨e, he⟩ := internalHom_restrict_scheme U
  let r : F.obj (dual P) ⟶ F.obj (dual Q) :=
    (e P (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf) s (𝟙 _) ≫
      (e Q (SheafOfModules.unit X.ringCatSheaf)).inv
  refine IsSplitMono.mk ⟨⟨r, ?_⟩⟩
  exact dual_retraction_key f U s e he hs

end AlgebraicGeometry.Scheme.Modules
