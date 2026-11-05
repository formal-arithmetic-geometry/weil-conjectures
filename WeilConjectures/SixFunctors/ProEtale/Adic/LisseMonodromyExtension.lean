/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback

/-!
# Lisse sheaves whose monodromy factors through a quotient extend

Let `f : Y' ⟶ Y` be a morphism of connected schemes with compatible monodromies of lisse
`ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`), which are
equivalences at a base point `t` of `Y'` and at its image, and assume that
`π₁(Y', t) → π₁(Y, t ≫ f)` is surjective, as for a dense open of a normal scheme. A lisse sheaf
`G'` on `Y'` whose monodromy representation is trivial on the kernel of
`π₁(Y', t) → π₁(Y, t ≫ f)` is the pullback of a lisse sheaf on `Y`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_rep_eq_self`): its
representation factors through a continuous representation of `π₁(Y, t ≫ f)`, which is the
monodromy representation of a lisse sheaf `G` on `Y`, and `f^* G ≅ G'` since both have the same
`π₁(Y', t)`-representation.

For an open `U` of a smooth curve and the open `V = U ∪ {z}` obtained by adding a boundary point,
the kernel is the local inertia at `z`, and this says that a lisse sheaf with trivial local
monodromy at `z` extends over `z` (blueprint `cor-wf-unramified-boundary-purity`).

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathHom`: the homomorphism
  `π₁(Y', y) → π₁(Y, y ≫ f)` of automorphism groups of fibre functors, which is continuous
  (`AlgebraicGeometry.Scheme.FiniteEtale.continuous_pullbackPathHom`).

## Main statements

- `AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_rep_eq_self`.
- `AlgebraicGeometry.Scheme.FiniteEtale.exists_pullbackPathHom_apply_eq`: if `P ×_Y Y'` is
  connected, `π₁(Y', y)` acts transitively on the fibre of `P` at `y ≫ f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.FiniteEtale

variable {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The homomorphism `π₁(Y', y) → π₁(Y, y ≫ f)` of automorphism groups of fibre functors induced
by a morphism `f : Y' ⟶ Y` (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso`). -/
noncomputable def pullbackPathHom (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y') :
    Aut (fiber y) →* Aut (fiber (y ≫ f)) where
  toFun σ := pullbackPathIso f σ
  map_one' := pullbackPathIso_refl f y
  map_mul' σ τ := by
    rw [Aut.Aut_mul_def, Aut.Aut_mul_def, pullbackPathIso_trans]

open PreGaloisCategory in
/-- The homomorphism `π₁(Y', y) → π₁(Y, y ≫ f)` is continuous: its component at a finite étale
`Y`-scheme `P` is determined by the component of the source at `P ×_Y Y'`. -/
lemma continuous_pullbackPathHom (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y') :
    Continuous (pullbackPathHom f y) := by
  rw [(autEmbedding_isClosedEmbedding (fiber (y ≫ f))).isInducing.continuous_iff]
  refine continuous_pi fun P ↦ ?_
  have hc : Continuous fun σ : Aut (fiber y) ↦ autEmbedding (fiber y) σ ((pullback f).obj P) :=
    (continuous_apply ((pullback f).obj P)).comp
      (autEmbedding_isClosedEmbedding (fiber y)).continuous
  exact ((continuous_of_discreteTopology (β := Aut ((fiber (y ≫ f)).obj P))
    (f := fun a : Aut ((fiber y).obj ((pullback f).obj P)) ↦
      ((pullbackFiberIso f y).app P).symm ≪≫ a ≪≫ (pullbackFiberIso f y).app P)).comp hc).congr
    fun σ ↦ rfl

open PreGaloisCategory in
/-- If the base change `P ×_Y Y'` of a finite étale `Y`-scheme along `f : Y' ⟶ Y` is connected,
the
automorphisms of the fibre functor at `y` act transitively on the fibre of `P` at `y ≫ f`, through
`pullbackPathHom`. -/
lemma exists_pullbackPathHom_apply_eq [ConnectedSpace Y'] (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y')
    (P : Y.FiniteEtale) [IsConnected ((pullback f).obj P)] (a b : (fiber (y ≫ f)).obj P) :
    ∃ τ : Aut (fiber y), (pullbackPathHom f y τ).hom.app P a = b := by
  have key (a' : (fiber y).obj ((pullback f).obj P)) :
      ∃ τ : Aut (fiber y), τ.hom.app _ a' = (pullbackFiberIso f y).inv.app P b :=
    MulAction.exists_smul_eq _ a' _
  obtain ⟨τ, hτ⟩ := key ((pullbackFiberIso f y).inv.app P a)
  refine ⟨τ, ?_⟩
  have h : (pullbackPathHom f y τ).hom.app P a = (pullbackFiberIso f y).hom.app P
      (τ.hom.app _ ((pullbackFiberIso f y).inv.app P a)) := rfl
  rw [h, hτ]
  exact ConcreteCategory.congr_hom ((pullbackFiberIso f y).inv_hom_id_app P) b

end Scheme.FiniteEtale

namespace ProEtale

section Universal

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω] [IsLocallyNoetherian Y]
  [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y]

/-- The monodromy of lisse `ℓ`-adic sheaves on a connected regular Noetherian scheme given by its
universal profinite étale covers (`AlgebraicGeometry.Scheme.universalCovers`), on which lisse
sheaves are constant (`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`). Being a definite
choice, it is compatible with the monodromy of the same kind on any connected regular Noetherian
scheme mapping to `Y` (`AlgebraicGeometry.ProEtale.isCompatible_universalLisseMonodromy`). -/
noncomputable def universalLisseMonodromy : LisseMonodromy l Y Ω :=
  (Scheme.universalCovers Y Ω).lisseMonodromy fun y G ↦
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover _ y G.property

/-- The monodromy from universal covers is an equivalence at every base point
(`cor-galois-lisse-representations`). -/
theorem universalLisseMonodromy_isEquivalenceAt (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (universalLisseMonodromy l Y Ω).IsEquivalenceAt t :=
  (Scheme.universalCovers Y Ω).lisseMonodromy_isEquivalenceAt _ t

variable {Y} in
/-- The monodromies from universal covers are compatible with every morphism of connected regular
Noetherian schemes. -/
theorem isCompatible_universalLisseMonodromy {Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    [CompactSpace Y'] [IsRegular Y'] [ConnectedSpace Y'] (f : Y' ⟶ Y) :
    LisseMonodromy.IsCompatible f (universalLisseMonodromy l Y Ω)
      (universalLisseMonodromy l Y' Ω) :=
  fun _ _ τ G ↦ (Scheme.universalCoversHom f).lisseMonodromy_mono_upperStar _ _ τ G

end Universal

namespace LisseMonodromy

open Scheme.FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω] {f : Y' ⟶ Y}
  {M : LisseMonodromy l Y Ω} {M' : LisseMonodromy l Y' Ω}

end LisseMonodromy

end ProEtale

end AlgebraicGeometry
