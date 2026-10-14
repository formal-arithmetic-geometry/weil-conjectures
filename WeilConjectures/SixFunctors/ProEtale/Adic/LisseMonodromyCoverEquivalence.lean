/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCover
public import WeilConjectures.WeilSheaf.LisseDuality

/-!
# The monodromy from universal covers is an equivalence

Let `Y` be a connected regular Noetherian scheme with universal profinite étale covers `Ỹ_y`
on which lisse sheaves are free, and let `M` be the monodromy of lisse sheaves obtained from them
(`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`). At every base point `t`, the stalk
functor identifies lisse sheaves with continuous finite-dimensional representations of
`π₁(Y, t)` (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_isEquivalenceAt`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  {U : Scheme.UniversalCovers Y Ω}
  (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
    Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))
  [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y]

include hU in
/-- **The monodromy representations are continuous.** -/
theorem lisseMonodromy_continuous_rep (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (G : LisseSheaf l Y)
    (φ : Module.Dual (PadicAlgCl l) (LisseMonodromy.StalkSpace t G))
    (v : LisseMonodromy.StalkSpace t G) :
    Continuous fun g : Aut (fiber t) ↦ φ ((U.lisseMonodromy hU).rep t G g v) := by
  sorry

/-- An element of the stalk of `M` killed by `φ : M ⟶ N` comes from the stalk of the kernel of
`φ`: the stalk functor is left exact. -/
lemma exists_stalkFunctor_map_kernel_ι_eq {K : Type u} [Field K] {Z : Scheme.{u}}
    (t : Spec (.of K) ⟶ Z) {M N : AdicSheaf l Z} (φ : M ⟶ N) (x : (stalkFunctor l t).obj M.X)
    (hx : ((stalkFunctor l t).map φ.hom).hom x = 0) :
    ∃ y, ((stalkFunctor l t).map (kernel.ι φ).hom).hom y = x := by
  let F := AdicSheaf.forget Z ⋙ stalkFunctor l t
  refine ⟨((PreservesKernel.iso F φ).inv).hom ((ModuleCat.kernelIsoKer (F.map φ)).inv.hom ⟨x, hx⟩), ?_⟩
  change ((PreservesKernel.iso F φ).inv ≫ F.map (kernel.ι φ)).hom _ = x
  rw [PreservesKernel.iso_inv_ι, ← ModuleCat.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

omit [CompactSpace Y] in
/-- **The stalk functor is faithful** on lisse sheaves on a connected regular Noetherian
scheme. -/
theorem lisseStalk_faithful (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G H : LisseSheaf l Y}
    (f g : G ⟶ H) (h : (lisseStalk l t).map f = (lisseStalk l t).map g) : f = g := by
  have := IsRegular.irreducibleSpace Y
  let φ : G.obj ⟶ H.obj := f.hom - g.hom
  have hφ : (stalkFunctor l t).map φ.hom = 0 := by
    have e : (stalkFunctor l t).map φ.hom =
        (AdicSheaf.forget Y ⋙ stalkFunctor l t).map f.hom -
          (AdicSheaf.forget Y ⋙ stalkFunctor l t).map g.hom :=
      (AdicSheaf.forget Y ⋙ stalkFunctor l t).map_sub
    rw [e, sub_eq_zero]
    exact h
  have hK := (isAdicLisseSheaf_kernel_cokernel_of_irreducibleSpace G.property H.property φ).1
  have : Epi (kernel.ι φ) := hK.epi_of_surjective_stalkFunctor_map G.property _ t fun x ↦
    exists_stalkFunctor_map_kernel_ι_eq t φ x (by rw [hφ]; rfl)
  have h0 : φ = 0 := by
    rw [← cancel_epi (kernel.ι φ), kernel.condition, comp_zero]
  exact ObjectProperty.hom_ext _ (sub_eq_zero.1 h0)

include hU in
/-- **The stalk functor is full onto equivariant maps.** -/
theorem lisseMonodromy_full (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G H : LisseSheaf l Y}
    (φ : LisseMonodromy.StalkSpace t G →ₗ[PadicAlgCl l] LisseMonodromy.StalkSpace t H)
    (hφ : ∀ g v, φ ((U.lisseMonodromy hU).rep t G g v) = (U.lisseMonodromy hU).rep t H g (φ v)) :
    ∃ f : G ⟶ H, ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom = φ := by
  sorry

include hU in
/-- **Every continuous finite-dimensional representation is a monodromy representation.** -/
theorem lisseMonodromy_essSurj (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (V : Type (u + 1)) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) (Aut (fiber t)) V)
    (hρ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ (G : LisseSheaf l Y) (e : LisseMonodromy.StalkSpace t G ≃ₗ[PadicAlgCl l] V),
      ∀ g v, e ((U.lisseMonodromy hU).rep t G g v) = ρ g (e v) := by
  sorry

/-- **The monodromy from universal covers is an equivalence at every base point** (blueprint:
`cor-galois-lisse-representations`, the case `Λ = ℚ̄_ℓ`). -/
theorem lisseMonodromy_isEquivalenceAt (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (U.lisseMonodromy hU).IsEquivalenceAt t where
  continuous_rep := lisseMonodromy_continuous_rep hU t
  faithful := lisseStalk_faithful t
  full := lisseMonodromy_full hU t
  essSurj := lisseMonodromy_essSurj hU t

end AlgebraicGeometry.Scheme.UniversalCovers
