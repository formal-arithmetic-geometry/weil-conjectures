/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.AlgebraicGeometry.LocallyNoetherianDomainStalkComponents

/-!
# Normality and components of an étale source

Source: Stacks Project, Tags 033C and 033N; blueprint
`part-six-operations/sec-reduction-finite-coefficients/sec-lattices/`
`sk-lem-wrp-normal-geometric-cover`, proof, second paragraph, first sentence
(blueprint: lem-wrp-etale-normal-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An étale source over a normal finite-type scheme is locally Noetherian and normal,
and its connected components are clopen integral schemes.

Source: Stacks Project, Tags 033C and 033N; blueprint
`part-six-operations/sec-reduction-finite-coefficients/sec-lattices/`
`sk-lem-wrp-normal-geometric-cover`, proof, second paragraph, first sentence
(blueprint: lem-wrp-etale-normal-components).

Proof:
1. A field is Noetherian, so `Spec k` is locally Noetherian; the structure morphism of `X`
   is locally of finite type, so `X` is locally Noetherian (Tag 01T6). The étale `p` is
   locally of finite presentation, hence locally of finite type, so `Y` is locally
   Noetherian by Tag 01T6 again.
2. Cover `Y` by affine opens `Spec B` mapping into affine opens `Spec A` of `X` with
   `A → B` étale. The localizations of `A` are stalks of `X`, normal domains, so `A` is a
   normal ring; étale ascent of normality (Tag 033C) makes `B` normal, so every stalk of
   `Y` is a normal domain.
3. `Y` is locally Noetherian with domain stalks, so by
   `locally_noetherian_domain_stalk_components` (blueprint:
   lem-wrp-locnoeth-domain-stalk-components; Tag 033N) every connected component
   `connectedComponent y` is open and closed and, with its open subscheme structure,
   integral. If `Y` is empty the assertions are vacuous.
-/
theorem etale_normal_components
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (hX : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Y ⟶ X) [Etale p] :
    IsLocallyNoetherian Y ∧
      (∀ y : Y,
        IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      (∀ y : Y,
        IsClopen (connectedComponent y) ∧
          ∃ U : Y.Opens, (U : Set Y) = connectedComponent y ∧ IsIntegral U.toScheme) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hY (y : Y) :
      IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
    obtain ⟨U, hU, hyU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show p y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
      (show y ∈ (p ⁻¹ᵁ U : Y.Opens) from hyU)
    have hA (P : Ideal Γ(X, U)) [P.IsPrime] :
        IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
      let x : PrimeSpectrum Γ(X, U) := ⟨P, inferInstance⟩
      have hx : hU.fromSpec x ∈ U := by
        have : hU.fromSpec x ∈ Set.range hU.fromSpec := ⟨x, rfl⟩
        rwa [hU.range_fromSpec] at this
      let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hx⟩
      have := hU.isLocalization_stalk' x hx
      have := (hX (hU.fromSpec x)).1
      have := (hX (hU.fromSpec x)).2
      let e := (IsLocalization.algEquiv P.primeCompl
        (X.presheaf.stalk (hU.fromSpec x)) (Localization.AtPrime P)).toRingEquiv
      exact ⟨e.symm.injective.isDomain e.symm.toRingHom, .of_equiv e⟩
    have hp : (p.appLE U V hVU).hom.Etale :=
      HasRingHomProperty.appLE @Etale p inferInstance ⟨U, hU⟩ ⟨V, hV⟩ _
    obtain ⟨hd, hc⟩ := hp.isNormalRing hA (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
    have := hd
    have := hc
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyV⟩ : V)
    have := hV.isLocalization_stalk ⟨y, hyV⟩
    let e := (IsLocalization.algEquiv (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨y, hyV⟩).asIdeal)
      (Y.presheaf.stalk y)).toRingEquiv
    exact ⟨e.symm.injective.isDomain e.symm.toRingHom, .of_equiv e⟩
  exact ⟨inferInstance, hY,
    locally_noetherian_domain_stalk_components Y (fun y ↦ (hY y).1)⟩

end AlgebraicGeometry
