/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy

/-!
# Compatibility of the monodromy of lisse sheaves with pullback

The monodromy of lisse `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.LisseMonodromy`) records the
compatibility of `cor-galois-lisse-representations` with pullback only along endomorphisms
(`AlgebraicGeometry.ProEtale.LisseMonodromy.mono_upperStar`). This file states the compatibility
with base change along an arbitrary morphism `f : X ⟶ Y` of connected regular locally Noetherian
schemes: a path `τ : F_y ≅ F_z` of `X` and the induced path `F_{y ≫ f} ≅ F_{z ≫ f}` of `Y` act
compatibly on `G_{y ≫ f} = (f^* G)_y` for a lisse sheaf `G` on `Y`.

## Main statements

- `AlgebraicGeometry.ProEtale.exists_lisseMonodromy_pullback`: the base change compatibility
  of `cor-galois-lisse-representations`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme.FiniteEtale

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω]

/-- **Lisse `ℚ̄_ℓ`-sheaves and continuous representations: compatibility with base change**
(blueprint: `cor-galois-lisse-representations`, the compatibility with base change, and
`def-wf-fundamental-representation`). On a connected regular locally Noetherian scheme `Y` there
is a monodromy of lisse sheaves which is an equivalence at every base point
(`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`) and which is compatible with pullback along
every morphism `f : X ⟶ Y` from a connected regular locally Noetherian scheme: for some
monodromy on `X`, again an equivalence at every base point, the transport along the path
`F_{y ≫ f} ≅ F_{z ≫ f}` induced by a path `τ : F_y ≅ F_z` of `X` acts on
`Γ(Spec Ω̄, (y ≫ f)^* G) = Γ(Spec Ω̄, y^* f^* G)` as the transport along `τ` acts on the stalks of
`f^* G`. This extends `AlgebraicGeometry.ProEtale.LisseMonodromy.mono_upperStar`, which records
the case of an endomorphism `f` of `Y`.

Like `AlgebraicGeometry.ProEtale.exists_lisseMonodromy`, this is the case `Λ = ℚ̄_ℓ` of the
dictionary between lisse sheaves and representations of the fundamental group, which needs the
comparison of the Bhatt–Scholze lisse sheaves with adic systems of finite locally constant étale
sheaves. -/
theorem exists_lisseMonodromy_pullback [IsLocallyNoetherian Y] [IsRegular Y] [ConnectedSpace Y] :
    ∃ M : LisseMonodromy l Y Ω, (∀ t, M.IsEquivalenceAt t) ∧
      ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsRegular X] [ConnectedSpace X] (f : X ⟶ Y),
        ∃ M' : LisseMonodromy l X Ω, (∀ t, M'.IsEquivalenceAt t) ∧
          ∀ {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ X} (τ : fiber y ≅ fiber z)
            (G : LisseSheaf l Y),
            (M.mono (pullbackPathIso f τ)).hom.app G ≫ (upperStarStalkIso l f z G.obj.X).hom =
              (upperStarStalkIso l f y G.obj.X).hom ≫ (M'.mono τ).hom.app (G.upperStar l f) := by
  sorry

end AlgebraicGeometry.ProEtale
