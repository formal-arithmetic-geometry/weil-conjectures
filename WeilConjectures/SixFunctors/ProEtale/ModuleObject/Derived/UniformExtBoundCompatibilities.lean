/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Compatibilities from other sections used by the uniform `Ext` bounds

The uniform `Ext` bounds for the `ℓ`-adic coefficient rings (blueprints
`sk-lem-uniform-constructible-ext` and `sk-lem-int-ext` (2)) rest on three results of other
blueprint nodes. They are stated here separately, in exactly the form in which the bounds use
them, and are the corresponding statements of those nodes on the integration branch:

* `ProEtale.DerivedCategory.uniformExtBoundCompat_constructibleFiniteTor`: the vanishing step of
  blueprint `det-ctf-finite-compact-proetale` for finite coefficients, which rests on Deligne's
  generic finiteness (blueprint `lem-asd-smooth-generic-direct-image`, for
  `thm-fin-deligne-generic-open`; `AlgebraicGeometry.Etale.smoothGenericDirectImage`);
* `ProEtale.uniformExtBoundCompat_integralModel`: integral models of bounded constructible
  `E`-complexes (blueprint `sk-thm-sfb-rationalization-comparison`,
  `ProEtale.isLocalization_boundedConstructibleExtendScalars`);
* `ProEtale.uniformExtBoundCompat_essSurjObj` and `ProEtale.uniformExtBoundCompat_homSurj`: the
  descent of objects and morphisms of `Dᵇc(X, ℚ̄_ℓ)` to a finite subextension (blueprint
  `sk-thm-sfb-qlbar-two-colimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl _root_.DerivedCategory.TStructure

namespace DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
  [HasInvertibleExponent Λ X]

include hk aX in
/-- Compatibility from blueprint `det-ctf-finite-compact-proetale` (vanishing step), resting on
`lem-asd-smooth-generic-direct-image` / `thm-fin-deligne-generic-open`: for `C` in
`Dctf(X, Λ)` there is `N` with `Hom(C, L) = 0` for every pro-étale complex `L` with cohomology
sheaves of étale origin in degrees `≤ N`. -/
lemma uniformExtBoundCompat_constructibleFiniteTor
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) :
    ∃ N : ℤ, ∀ L, etaleOriginHomology Λ X L → L.IsLE N → ∀ f : C ⟶ L, f = 0 :=
  exists_forall_eq_zero_of_constructibleFiniteTor hk aX hC

end DerivedCategory

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] [TopologicalSpace.NoetherianSpace X]

/-- Compatibility from blueprint `sk-thm-sfb-rationalization-comparison`: every bounded
constructible `E`-complex is the extension of scalars of a bounded constructible
`𝒪_E`-complex. -/
lemma uniformExtBoundCompat_integralModel (E : FiniteIntermediateField ℓ)
    (K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) :
    ∃ K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X),
      Nonempty ((boundedConstructibleExtendScalars X ℓ E).obj K₀ ≅ K) :=
  exists_boundedConstructibleExtendScalars_obj_iso X ℓ E K

/-- Compatibility from blueprint `sk-thm-sfb-qlbar-two-colimit` (objects): every bounded
constructible `ℚ̄_ℓ`-complex is the extension of scalars of a bounded constructible
`E`-complex for some finite subextension `E`. -/
lemma uniformExtBoundCompat_essSurjObj : (constructibleCocone X ℓ).EssSurjObj :=
  constructibleCocone_essSurjObj X ℓ

/-- Compatibility from blueprint `sk-thm-sfb-qlbar-two-colimit` (morphisms): every morphism
between extensions of scalars to `ℚ̄_ℓ` comes from some finite subextension. -/
lemma uniformExtBoundCompat_homSurj : (constructibleCocone X ℓ).HomSurj :=
  constructibleCocone_homSurj X ℓ

end AlgebraicGeometry.ProEtale
