/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.RingTheory.Etale.IntegrallyClosed

/-!
# Irreducible components of Noetherian schemes, flat open maps, normal étale schemes

Three elementary facts used by the Noetherian theory of constructible étale sheaves:

- `AlgebraicGeometry.Scheme.finite_irreducibleComponents` (blueprint
  `lem-weil-pbc-noetherian-finite-components`): a Noetherian scheme has finitely many
  irreducible components.
- `AlgebraicGeometry.universallyOpen_of_flat_of_locallyOfFinitePresentation` (blueprint
  `lem-weil-pbc-flat-lfp-open`): a flat morphism locally of finite presentation is universally
  open, in particular open (`AlgebraicGeometry.Scheme.Hom.isOpenMap`).
- `AlgebraicGeometry.Scheme.exists_isClopen_isIntegral_of_etale` (blueprint
  `lem-fin-etale-normal-components`): a Noetherian scheme étale over a normal integral scheme is
  a finite disjoint union of open and closed normal integral subschemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-weil-pbc-noetherian-finite-components`: Finitely many irreducible components.

A Noetherian scheme has finitely many irreducible components. -/
theorem Scheme.finite_irreducibleComponents (X : Scheme.{u}) [IsNoetherian X] :
    (irreducibleComponents X).Finite :=
  TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- Blueprint `lem-weil-pbc-flat-lfp-open`: Flat finite-presentation morphisms are open.

A flat morphism locally of finite presentation is universally open: it is open, and so is every
base change of it. This is Mathlib's `AlgebraicGeometry.UniversallyOpen.of_flat`. -/
theorem universallyOpen_of_flat_of_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] : UniversallyOpen f :=
  UniversallyOpen.of_flat f

/-- The local rings of a scheme étale over an integral scheme with integrally closed local rings
are integrally closed domains (the étale case of Stacks 033C). -/
theorem Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale {W Y : Scheme.{u}} (f : W ⟶ Y)
    [Etale f] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (x : W) :
    IsDomain (W.presheaf.stalk x) ∧ IsIntegrallyClosed (W.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := W)
    (show x ∈ (f ⁻¹ᵁ U : W.Opens) from hxU)
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  -- `Γ(Y, U)` is an integrally closed domain
  have : IsIntegrallyClosed Γ(Y, U) := IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦ by
    let y : PrimeSpectrum Γ(Y, U) := ⟨P, inferInstance⟩
    have hy : hU.fromSpec y ∈ U := by
      have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
      rwa [hU.range_fromSpec] at this
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨_, hy⟩
    have := hU.isLocalization_stalk' y hy
    have := hY (hU.fromSpec y)
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk (hU.fromSpec y))
        (Localization.AtPrime P)).toRingEquiv
  -- the étale algebra `Γ(Y, U) ⟶ Γ(W, V)`
  let := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.Etale Γ(Y, U) Γ(W, V) := by
    rw [← RingHom.etale_algebraMap]
    exact HasRingHomProperty.appLE @Etale f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ _
  let := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hxV⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (W.presheaf.stalk x)

/-- Blueprint `lem-fin-etale-normal-components`: Normal components after étale pullback.

Let `f : W ⟶ Y` be étale with `W` Noetherian and `Y` normal integral (an integral scheme all
of whose local rings are integrally closed). Then `W` is a finite disjoint union of open and
closed subschemes `W_a` which are normal integral. -/
theorem Scheme.exists_isClopen_isIntegral_of_etale {W Y : Scheme.{u}} (f : W ⟶ Y) [Etale f]
    [IsNoetherian W] [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ (n : ℕ) (U : Fin n → W.Opens), (∀ a, IsClopen (U a : Set W)) ∧
      Pairwise (fun a b ↦ Disjoint (U a) (U b)) ∧ ⨆ a, U a = ⊤ ∧
      ∀ a, IsIntegral (U a).toScheme ∧
        ∀ w : (U a).toScheme, IsIntegrallyClosed ((U a).toScheme.presheaf.stalk w) := by
  have hW := Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale f hY
  let e := (Finite.equivFin (ConnectedComponents W)).symm
  let U (a : Fin (Nat.card (ConnectedComponents W))) : W.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {e a},
      ((isClopen_discrete {e a}).preimage ConnectedComponents.continuous_coe).isOpen⟩
  have hU (a : Fin (Nat.card (ConnectedComponents W))) : IsClopen (U a : Set W) :=
    (isClopen_discrete {e a}).preimage ConnectedComponents.continuous_coe
  refine ⟨Nat.card (ConnectedComponents W), U, hU, fun a b hab ↦ ?_, ?_, fun a ↦ ?_⟩
  · dsimp only
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact (Set.disjoint_singleton.2 (e.injective.ne hab)).preimage _
  · rw [← TopologicalSpace.Opens.coe_eq_univ, TopologicalSpace.Opens.coe_iSup,
      Set.eq_univ_iff_forall]
    intro x
    exact Set.mem_iUnion.2 ⟨e.symm x, by simp [U]⟩
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e a)
  have hUx : (U a : Set W) = connectedComponent x := by
    simp [U, ← hx, connectedComponents_preimage_singleton]
  have : ConnectedSpace (U a) :=
    isConnected_iff_connectedSpace.1 (hUx ▸ isConnected_connectedComponent)
  have hst (w : (U a).toScheme) :=
    (asIso ((U a).ι.stalkMap w)).commRingCatIsoToRingEquiv
  have hdom (w : (U a).toScheme) : IsDomain ((U a).toScheme.presheaf.stalk w) :=
    have := (hW ((U a).ι w)).1
    (hst w).symm.injective.isDomain (hst w).symm.toRingHom
  have : IrreducibleSpace (U a).toScheme := irreducibleSpace_of_isDomain_stalk _ hdom
  have : IsReduced (U a).toScheme := isReduced_of_isReduced_stalk _
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, fun w ↦ ?_⟩
  have := (hW ((U a).ι w)).2
  exact .of_equiv (hst w)

end AlgebraicGeometry
