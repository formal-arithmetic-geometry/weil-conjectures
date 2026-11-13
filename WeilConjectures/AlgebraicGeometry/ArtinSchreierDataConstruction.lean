/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHom
public import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.AlgebraicGeometry.EtaleStructureSectionsEquiv

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false

/-- The lifted étale structure-module sheaf has natural additive section identifications
(Stacks, Tags 03DR, 03DU, 0096 and 01CA). -/
theorem artinSchreier_construction (C : Scheme.{u}) :
    ∃ (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : G ≅ (sheafCompose C.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (Scheme.Modules.etaleTensorSectionsSheaf (Scheme.Modules.unitObj C)))
      (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤)),
      ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
        a V (G.obj.map g x) = g.unop.left.appTop (a U x) := by
  refine ⟨_, Iso.refl _, etaleStructureSectionsEquiv C, ?_⟩
  intro U V g x
  exact etaleStructureSectionsEquiv_naturality C U V g x

end AlgebraicGeometry
