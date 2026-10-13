/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Transporting a supplied subscheme morphism to the open slice site

Source: Stacks Project, Sheaves Tag 00A0 (3).
(blueprint: new-lem-sc-open-stalk-unit-map-one-lift-bridge).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Transport an already constructed local morphism from the open subscheme to the slice site.

Source: Stacks Project, Sheaves Tag 00A0 (3), restriction to an open subspace.
(blueprint: new-lem-sc-open-stalk-unit-map-one-lift-bridge).

Proof: Put V = U.ι ''ᵁ A, so x belongs to V and V is contained in U. The open subscheme
V is canonically isomorphic to A.toScheme over U.toScheme. Restrict f along this isomorphism.
The natural isomorphism Modules.overMapCompOverEquiv identifies its source and target with
those of the images of the slice restrictions of F and N under Modules.overEquiv V.
Conjugate by these components and take the preimage under this fully faithful equivalence
to obtain k. Use the canonical restriction-stalk comparison, constructed from the same-germ
formula, for a. Every stalk element on V is represented by a section on a neighbourhood of
x; transfer that section to A and apply hf. The germ formulas for restriction and the
slice equivalence give S.map k followed by a_N = a_F followed by the scalar restriction
of q. Linearity holds because the composite of the two open-immersion stalk ring maps is
U.ι.stalkMap. Compose with a_N inverse to get the displayed equation. No local existence
of f is proved here; f and its germ equation are inputs, for arbitrary F and N. -/
theorem exists_open_stalk_hom_of_subscheme_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (F N : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (q : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨x, hxU⟩).obj
        ((Modules.overEquiv U).functor.obj F) ⟶
      (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨x, hxU⟩).obj
        ((Modules.overEquiv U).functor.obj N))
    (A : U.toScheme.Opens) (hxA : (⟨x, hxU⟩ : U.toScheme) ∈ A)
    (f : (Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj F) ⟶
      (Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj N))
    (hf : ∀ (B : A.toScheme.Opens)
      (hxB : (⟨⟨x, hxU⟩, hxA⟩ : A.toScheme) ∈ B)
      (m : Γ((Modules.restrictFunctor A.ι).obj ((Modules.overEquiv U).functor.obj F), B)),
      ((Modules.overEquiv U).functor.obj N).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
          ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ (Modules.Hom.app f B m) =
        q (((Modules.overEquiv U).functor.obj F).presheaf.germ (A.ι ''ᵁ B) ⟨x, hxU⟩
          ⟨⟨⟨x, hxU⟩, hxA⟩, hxB, rfl⟩ m)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U),
      let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hVU)
      let S := openModuleStalkFunctor X V ⟨x, hxV⟩
      ∃ (a : R ⋙ S ≅ openModuleStalkFunctor X U ⟨x, hxU⟩)
        (k : R.obj F ⟶ R.obj N),
        S.map k = a.hom.app F ≫
          (ModuleCat.restrictScalars (U.ι.stalkMap ⟨x, hxU⟩).hom).map q ≫
            a.inv.app N := by sorry

end
end AlgebraicGeometry.Scheme
