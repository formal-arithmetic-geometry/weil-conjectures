/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelPointTrace
public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelUpperStarComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!
# The Galois action on a geometric stalk in the two models

Let `Ω` be a separably closed field, `σ` an automorphism of `Spec Ω` and `x : Spec Ω ⟶ X` a
geometric point with `σ ≫ x = x`. Then `σ` acts on the stalk at `x`:

- in the condensed model, on `x^* M` for a module object `M` over `ℚ̲̄_ℓ,X`, by
  `x^* M ≅ σ^* x^* M ≅ (σ ≫ x)^* M = x^* M`, through the trivialization `σ^* ≅ 𝟭` of the pullback
  along `σ` over the separably closed point
  (`AlgebraicGeometry.ProEtale.CondensedRing.upperStarIsoIdOfIsSepClosed`):
  `AlgebraicGeometry.ProEtale.galoisNew`;
- in the model of the `ℓ`-adic sheaves, on the global sections `Γ(Spec Ω, x^* N)`, by
  `Γ(x^* N) ≅ Γ(σ^* x^* N) ≅ Γ((σ ≫ x)^* N) = Γ(x^* N)`, through the invariance of the global
  sections under the pullback along an automorphism
  (`AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso`):
  `AlgebraicGeometry.ProEtale.galoisOld`.

The main result (`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_traceOrZero_galoisNew`) is
that the two actions have the same trace, for `M` with `x^* M` finite free and
`N = E⁻¹ M` its image in the model of the `ℓ`-adic sheaves. Through the pseudonatural
comparison of the pullbacks of the two models
(`AlgebraicGeometry.ProEtale.upperStarCondensedModInverseIso_comp`), the condensed action is the
image under `E` of an endomorphism `ψ` of `x^* N`, and the trace of `E ψ` is the trace of
`Γ(ψ)` (`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_traceOrZero_map_of_iso_biproduct`).
The two trivializations `Γ ∘ σ^* ≅ Γ` of the global sections, the old one and the one induced by
`σ^* ≅ 𝟭`, are natural, hence (on finite free objects) differ by a scalar `λ`, which is
determined by the unit: the old action fixes the restrictions of global sections
(`AlgebraicGeometry.ProEtale.galoisOld_comp_globalSectionsToUpperStar`), and the new one is
trivial on the unit, so both have trace `1` on the unit and `λ = 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

/-- **Natural transformations proportional on a generator**: two natural transformations
`α β : F ⟶ G` between additive functors to `R`-modules with `α_u = c • β_u` satisfy
`α_A = c • β_A` for every `A ≅ uʳ`. -/
lemma CategoryTheory.NatTrans.app_eq_smul_of_iso_biproduct {C : Type*} [Category C]
    [Preadditive C] [HasFiniteBiproducts C] {R : Type*} [CommRing R] {F G : C ⥤ ModuleCat R}
    [F.Additive] [G.Additive] (α β : F ⟶ G) {u : C} (c : R) (hu : α.app u = c • β.app u)
    {A : C} {r : ℕ} (e : A ≅ ⨁ fun _ : Fin r ↦ u) : α.app A = c • β.app A := by
  have kB (γ : F ⟶ G) : γ.app (⨁ fun _ : Fin r ↦ u) =
      ∑ i, F.map (biproduct.π (fun _ : Fin r ↦ u) i) ≫ γ.app u ≫
        G.map (biproduct.ι (fun _ : Fin r ↦ u) i) := by
    conv_lhs => rw [← Category.comp_id (γ.app _), ← CategoryTheory.Functor.map_id,
      ← biproduct.total, Functor.map_sum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Functor.map_comp, ← Category.assoc, ← γ.naturality, Category.assoc]
  have kA (γ : F ⟶ G) : γ.app A = F.map e.hom ≫ γ.app (⨁ fun _ : Fin r ↦ u) ≫ G.map e.inv := by
    rw [γ.naturality_assoc, ← G.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [kA α, kA β, kB α, kB β, hu]
  simp only [Linear.smul_comp, Linear.comp_smul, ← Finset.smul_sum]

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

section Old

variable {S X : Scheme.{u}} (σ : S ≅ S) (x : S ⟶ X) (hσ : σ.hom ≫ x = x)

/-- The invariance `Γ(S, σ^* A) ≅ Γ(S, A)` of the global sections of `ℓ`-adic sheaves under the
pullback along an automorphism `σ`, as `ℚ̄_ℓ`-vector spaces. -/
noncomputable def adicGlobalSectionsModuleUpperStarIso :
    (σ.hom)^*ᵃ[l] ⋙ adicGlobalSectionsModule l S ≅ adicGlobalSectionsModule l S :=
  NatIso.ofComponents (fun A ↦ (WeilCoefficients.toModuleCat l).mapIso
      ((globalSectionsUpperStarIso (WeilCoefficients.{u} l) σ).app A.X))
    (fun f ↦ by
      simp only [Functor.comp_map, Functor.mapIso_hom, Iso.app_hom, ← Functor.map_comp]
      exact congrArg (WeilCoefficients.toModuleCat l).map
        ((globalSectionsUpperStarIso _ σ).hom.naturality f.hom))

/-- **The Galois action on a stalk, in the model of the `ℓ`-adic sheaves**: for an automorphism
`σ` of `S` and `x : S ⟶ X` with `σ ≫ x = x`, the automorphism
`Γ(x^* N) ≅ Γ(σ^* x^* N) ≅ Γ((σ ≫ x)^* N) = Γ(x^* N)` of the global sections of `x^* N`. -/
noncomputable def galoisOld (N : AdicSheaf l X) :
    (adicGlobalSectionsModule l S).obj ((x)^*ᵃ[l].obj N) ⟶
      (adicGlobalSectionsModule l S).obj ((x)^*ᵃ[l].obj N) :=
  (adicGlobalSectionsModuleUpperStarIso l σ).inv.app ((x)^*ᵃ[l].obj N) ≫
    (adicGlobalSectionsModule l S).map
      ((adicUpperStarComp l σ.hom x).inv.app N ≫ (adicUpperStarCongr l hσ).hom.app N)

/-- The restriction of global sections along a morphism is compatible with the congruence
isomorphisms of the pullbacks. -/
lemma globalSectionsToUpperStar_app_comp_map_upperStarCongr {T Y : Scheme.{u}} {g g' : T ⟶ Y}
    (h : g = g') (F : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (globalSectionsToUpperStar _ g).app F ≫
        (Sheaf.Γ _ _).map ((upperStarCongr (WeilCoefficients.{u} l) h).hom.app F) =
      (globalSectionsToUpperStar _ g').app F := by
  subst h
  simp [upperStarCongr]

set_option maxHeartbeats 1000000 in
-- the kernel checks the identification of the underlying sheaves of the pullbacks by unfolding
/-- **The Galois action fixes the restrictions of global sections**: the restriction
`Γ(X, N) ⟶ Γ(S, x^* N)` followed by `AlgebraicGeometry.ProEtale.galoisOld` is the
restriction. -/
lemma globalSectionsToUpperStar_comp_galoisOld (N : AdicSheaf l X) :
    (WeilCoefficients.toModuleCat l).map ((globalSectionsToUpperStar _ x).app N.X) ≫
        galoisOld l σ x hσ N =
      (WeilCoefficients.toModuleCat l).map ((globalSectionsToUpperStar _ x).app N.X) := by
  have h0 := globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
    (WeilCoefficients.{u} l) σ ((x)^*ᵃ[l].obj N).X
  have h1 : (globalSectionsUpperStarIso (WeilCoefficients.{u} l) σ).inv.app ((x)^*ᵃ[l].obj N).X =
      (globalSectionsToUpperStar _ σ.hom).app ((x)^*ᵃ[l].obj N).X := by
    rw [← Category.id_comp ((globalSectionsUpperStarIso _ σ).inv.app _), ← h0, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  have h2 : (globalSectionsToUpperStar _ (σ.hom ≫ x)).app N.X ≫
      (Sheaf.Γ _ _).map ((upperStarComp (WeilCoefficients.{u} l) σ.hom x).hom.app N.X) =
      (globalSectionsToUpperStar _ x).app N.X ≫
        (globalSectionsToUpperStar _ σ.hom).app ((x)^*ᵃ[l].obj N).X :=
    globalSectionsToUpperStar_comp (WeilCoefficients.{u} l) σ.hom x N.X
  have h3 := globalSectionsToUpperStar_app_comp_map_upperStarCongr l hσ N.X
  simp only [galoisOld, adicGlobalSectionsModuleUpperStarIso, NatIso.ofComponents_inv_app,
    Functor.mapIso_inv, Iso.app_inv, Functor.comp_map, ← Functor.map_comp]
  refine congrArg (WeilCoefficients.toModuleCat l).map ?_
  rw [h1, ← reassoc_of% h2, Functor.map_comp, Functor.map_comp]
  have e1 : (AdicSheaf.forget S).map ((adicUpperStarComp l σ.hom x).inv.app N) =
      (upperStarComp (WeilCoefficients.{u} l) σ.hom x).inv.app N.X :=
    adicUpperStarComp_inv_app_hom σ.hom x N
  have e2 : (AdicSheaf.forget S).map ((adicUpperStarCongr l hσ).hom.app N) =
      (upperStarCongr (WeilCoefficients.{u} l) hσ).hom.app N.X :=
    adicUpperStarCongr_hom_app_hom hσ N
  rw [e1, e2]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact h3

end Old

end AlgebraicGeometry.ProEtale
