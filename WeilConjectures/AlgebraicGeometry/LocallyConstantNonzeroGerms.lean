/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.NonzeroGermWitness
import WeilConjectures.AlgebraicGeometry.RefineNonzeroGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # A nonzero morphism into a locally constant sheaf has locally nonzero germs
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A nonzero morphism into an abelian sheaf whose underlying set sheaf is locally
constant has a section on a nonempty etale neighbourhood whose image has nonzero
geometric germs everywhere on that neighbourhood. -/
theorem exists_section_everywhere_nonzero_germ (X : Scheme.{u})
    (N F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyConstantEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F))
    (ψ : N ⟶ F) (hψ : ψ ≠ 0) :
    ∃ (U : X.Etale) (_ : Nonempty U.left) (s : N.obj.obj (op U)),
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
        (v : (pointSmallEtale t).fiber.obj U),
        (pointSmallEtale t).toPresheafFiber U v F.obj (ψ.hom.app (op U) s) ≠ 0 := by
  obtain ⟨U, _, s, Ω, hΩ, hcl, t, v, hs⟩ :=
    exists_section_nonzero_at_some_germ X N F ψ hψ
  obtain ⟨V, r, hV, hr⟩ :=
    refine_section_nonzero_germs X F hF U (ψ.hom.app (op U) s) Ω t v hs
  refine ⟨V, hV, N.obj.map r.op s, ?_⟩
  intro Ω' hΩ' hcl' t' v'
  have hn := congrArg (fun f ↦ f s) (ψ.hom.naturality r.op)
  change ψ.hom.app (op V) (N.obj.map r.op s) =
    F.obj.map r.op (ψ.hom.app (op U) s) at hn
  rw [hn]
  exact hr Ω' t' v'

end AlgebraicGeometry.Scheme
