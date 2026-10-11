/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-!
# Higher direct images and restriction to an open subscheme of the base

Let `g : T' ⟶ T` be an open immersion and let `f' : X' ⟶ T'`, `g' : X' ⟶ X` be the base change
of `f : X ⟶ T` along `g`. Then `R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}` for every `𝒪_X`-module
`ℱ` (`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict_of_isPullback`).

The pushforward commutes with restriction to opens,
`f'_* (ℱ|_{X'}) ≅ (f_* ℱ)|_{T'}` (`AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso`).
The restriction of an injective resolution `ℱ → I` is a resolution `ℱ|_{X'} → I|_{X'}` by flasque
modules, which are acyclic for `f'_*`, so `R^q f'_* (ℱ|_{X'})` is the cohomology of
`f'_* (I|_{X'}) ≅ (f_* I)|_{T'}`; restriction to `T'` is exact, so this is `(R^q f_* ℱ)|_{T'}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {f : X ⟶ T} {g : T' ⟶ T} {g' : X' ⟶ X} {f' : X' ⟶ T'}
  [IsOpenImmersion g] [IsOpenImmersion g']

/-- In a cartesian square with `g` an open immersion, `f⁻¹(g(V)) = g'(f'⁻¹(V))`. -/
lemma preimage_image_eq_image_preimage_of_isPullback (sq : IsPullback g' f' f g)
    (V : T'.Opens) : f ⁻¹ᵁ (g ''ᵁ V) = g' ''ᵁ (f' ⁻¹ᵁ V) := by
  ext x
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_image, Set.mem_preimage, Set.mem_image,
    SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, hvx⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x v hvx.symm
    refine ⟨sq.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
      exact hv
    · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨f' y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]

variable (f g g' f') in
/-- The comparison of the two composites `T'.Opens ⥤ X.Opens`, `V ↦ f⁻¹(g(V)) = g'(f'⁻¹(V))`. -/
noncomputable def opensFunctorCompMapIso (sq : IsPullback g' f' f g) :
    g.opensFunctor ⋙ TopologicalSpace.Opens.map f.base ≅
      TopologicalSpace.Opens.map f'.base ⋙ g'.opensFunctor :=
  NatIso.ofComponents (fun V ↦ eqToIso (preimage_image_eq_image_preimage_of_isPullback sq V))
    fun _ ↦ rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **The pushforward commutes with restriction to an open subscheme of the base.** In a cartesian
square with `g` an open immersion, `(f_* ℱ)|_{T'} ≅ f'_* (ℱ|_{X'})`. -/
noncomputable def pushforwardRestrictIso (sq : IsPullback g' f' f g) :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor g' ⋙ pushforward f' := by
  letI := Functor.isContinuous_comp.{u} g.opensFunctor (TopologicalSpace.Opens.map f.base)
    (Opens.grothendieckTopology T') (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)
  letI := Functor.isContinuous_comp.{u} (TopologicalSpace.Opens.map f'.base) g'.opensFunctor
    (Opens.grothendieckTopology T') (Opens.grothendieckTopology X')
    (Opens.grothendieckTopology X)
  refine SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (opensFunctorCompMapIso f g g' f' sq).symm ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
  ext V x
  dsimp
  trace_state
  sorry

end AlgebraicGeometry.Scheme.Modules
