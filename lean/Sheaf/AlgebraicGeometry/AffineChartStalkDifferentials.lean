/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import WeilConjectures.AlgebraicGeometry.TangentBundle
import Mathlib.RingTheory.Localization.Module

/-!
# Affine chart comparison for stalk maps and relative differentials

Source: Stacks Project, Morphisms, Tags 01TP, 01V9, 01US and 01UT;
Schemes, Tags 01I1 and 01HV(6)-(7)
(blueprint: lem-trf-affine-chart-stalk-differentials).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

private theorem spanning_family_transport
    {R T M N : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module T N]
    (h : R ≃+* T) (e : M ≃+ N) (he : ∀ r m, e (r • m) = h r • e m) (n : ℕ) :
    (∃ v : Fin n → M, Submodule.span R (Set.range v) = ⊤) ↔
      ∃ v : Fin n → N, Submodule.span T (Set.range v) = ⊤ := by
  have : RingHomInvPair h.toRingHom h.symm.toRingHom := RingHomInvPair.of_ringEquiv h
  have : RingHomInvPair h.symm.toRingHom h.toRingHom := RingHomInvPair.of_ringEquiv_symm h
  let E : LinearEquiv (R := R) (S := T) h.toRingHom
      (σ' := h.symm.toRingHom) M N := { e with map_smul' := he }
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨E ∘ v, ?_⟩
    rw [Set.range_comp, Submodule.span_image_linearEquiv E, hv]
    simp
  · rintro ⟨v, hv⟩
    refine ⟨E.symm ∘ v, ?_⟩
    rw [Set.range_comp, Submodule.span_image_linearEquiv E.symm, hv]
    simp

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finitely presented morphism admits affine neighbourhoods whose coordinate
map is finitely presented and whose localized rings and differentials identify with the
ambient stalks. The equations on germs specify the canonical ring identifications and
send the germ of `da` to `da/1`. The additive differential equivalence respects
scalar multiplication via `h`, expressing linearity over the identified ring `A_q`.
The canonical map
`Localization.localRingHom` sends `r/t` to `phi(r)/phi(t)`.

Source: Stacks Project, Morphisms, Tags 01TP, 01V9, 01US and 01UT;
Schemes, Tags 01I1 and 01HV(6)-(7)
(blueprint: lem-trf-affine-chart-stalk-differentials).

Proof:
1. Choose affine neighbourhoods `W` of `x` and `V` of `f x` with `W` contained in
   `f`'s inverse image of `V`, by `def-sbc-locally-finite-presentation`. Their
   coordinate map `phi = f.appLE V W hWV` is finitely presented.
2. The affine chart square identifies the contracted prime. Affine-open stalk
   localization and `IsLocalization.algEquiv` construct the germ-preserving ring
   equivalences. Localization uniqueness reduces the stalk-map square to coordinate
   sections, where `germ_stalkMap_apply`, restriction of germs, and
   `Localization.localRingHom_to_map` give the same image.
3. Apply `lem-sc-relative-differentials-affine-sections` and
   `lem-sbc-affine-module-germ-localization` to the quasi-coherent differential
   sheaf. The composite of the section equivalence and the germ map is a localization
   of `Omega A/R`. Its localization equivalence gives `theta`, and its formula on
   numerators sends the germ of `da` to `da/1`. Give the target the stalk-ring action
   through `h`; the ring germ equation identifies its coordinate-ring action.
   `LinearEquiv.extendScalarsOfIsLocalization` then proves the required semilinearity.
4. Flatness is invariant under these compatible ring isomorphisms, using
   `def-weil-pbc-flat-ring-map`: transport modules along `e`, and on tensor
   products use `n tensor b` mapped to `n tensor h(b)`. The stalk-map square
   makes this balanced; the inverse uses `h.symm`. These bijections commute
   with module maps, so injectivity after tensoring is equivalent on both sides.
   The semilinear equivalence sends a spanning family of `r` vectors to a
   spanning family of `r` vectors, and its inverse gives the converse.
   For `r = 0` this says that one module is zero exactly when the other is. -/
theorem exists_affineChart_stalk_differentials
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    ∃ (W : X.Opens) (V : S.Opens) (hW : IsAffineOpen W) (hV : IsAffineOpen V)
      (hx : x ∈ W) (hWV : W ≤ f ⁻¹ᵁ V) (q : PrimeSpectrum Γ(X, W)),
      q = hW.primeIdealOf ⟨x, hx⟩ ∧
      (f.appLE V W hWV).hom.FinitePresentation ∧
      q.comap (f.appLE V W hWV).hom = hV.primeIdealOf ⟨f x, hWV hx⟩ ∧
      ∃ (e : S.presheaf.stalk (f x) ≃+*
          Localization.AtPrime (q.comap (f.appLE V W hWV).hom).asIdeal)
        (h : X.presheaf.stalk x ≃+* Localization.AtPrime q.asIdeal)
        (theta : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            f.relativeDifferentials ≃+
          LocalizedModule q.asIdeal.primeCompl
            (CommRingCat.KaehlerDifferential (f.appLE V W hWV))),
        (∀ r : Γ(S, V),
          e (S.presheaf.germ V (f x) (hWV hx) r) = algebraMap _ _ r) ∧
        (∀ a : Γ(X, W), h (X.presheaf.germ W x hx a) = algebraMap _ _ a) ∧
        (∀ b : S.presheaf.stalk (f x),
          h (f.stalkMap x b) =
            Localization.localRingHom (q.comap (f.appLE V W hWV).hom).asIdeal
              q.asIdeal (f.appLE V W hWV).hom rfl (e b)) ∧
        (∀ (b : X.presheaf.stalk x)
          (m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            f.relativeDifferentials), theta (b • m) = h b • theta m) ∧
        (∀ a : Γ(X, W),
          theta (f.relativeDifferentials.presheaf.germ W x hx
            (f.relativeDifferentialsDerivation.d a)) =
          LocalizedModule.mk (CommRingCat.KaehlerDifferential.d
            (f := f.appLE V W hWV) a) 1) ∧
        ((f.stalkMap x).hom.Flat ↔
          (Localization.localRingHom (q.comap (f.appLE V W hWV).hom).asIdeal
            q.asIdeal (f.appLE V W hWV).hom rfl).Flat) ∧
        (∀ r : ℕ,
          (∃ v : Fin r → (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
              f.relativeDifferentials,
            Submodule.span (X.presheaf.stalk x) (Set.range v) = ⊤) ↔
          ∃ v : Fin r → LocalizedModule q.asIdeal.primeCompl
              (CommRingCat.KaehlerDifferential (f.appLE V W hWV)),
            Submodule.span (Localization.AtPrime q.asIdeal) (Set.range v) = ⊤) := by
  obtain ⟨V, hV, hs, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := f x) (U := ⊤) (by trivial)
  obtain ⟨W, hW, hx, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := f ⁻¹ᵁ V) hs
  let q := hW.primeIdealOf ⟨x, hx⟩
  let phi := f.appLE V W hWV
  have hp : q.comap phi.hom = hV.primeIdealOf ⟨f x, hWV hx⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hx
  let AS := S.presheaf.algebra_section_stalk (U := V) ⟨f x, hWV hx⟩
  let AX := X.presheaf.algebra_section_stalk (U := W) ⟨x, hx⟩
  have : IsLocalization.AtPrime (S.presheaf.stalk (f x)) (q.comap phi.hom).asIdeal := by
    rw [hp]
    exact hV.isLocalization_stalk ⟨f x, hWV hx⟩
  have := hW.isLocalization_stalk ⟨x, hx⟩
  let e := (IsLocalization.algEquiv (q.comap phi.hom).asIdeal.primeCompl
    (S.presheaf.stalk (f x)) (Localization.AtPrime (q.comap phi.hom).asIdeal)).toRingEquiv
  let h := (IsLocalization.algEquiv q.asIdeal.primeCompl
    (X.presheaf.stalk x) (Localization.AtPrime q.asIdeal)).toRingEquiv
  have he (r : Γ(S, V)) :
      e (S.presheaf.germ V (f x) (hWV hx) r) = algebraMap _ _ r :=
    (IsLocalization.algEquiv (q.comap phi.hom).asIdeal.primeCompl
      (S.presheaf.stalk (f x)) (Localization.AtPrime (q.comap phi.hom).asIdeal)).commutes r
  have hh (a : Γ(X, W)) : h (X.presheaf.germ W x hx a) = algebraMap _ _ a :=
    (IsLocalization.algEquiv q.asIdeal.primeCompl
      (X.presheaf.stalk x) (Localization.AtPrime q.asIdeal)).commutes a
  let ell := Localization.localRingHom (q.comap phi.hom).asIdeal
    q.asIdeal phi.hom rfl
  have square : h.toRingHom.comp (f.stalkMap x).hom = ell.comp e.toRingHom := by
    apply IsLocalization.ringHom_ext (q.comap phi.hom).asIdeal.primeCompl
    ext r
    change h (f.stalkMap x (S.presheaf.germ V (f x) (hWV hx) r)) =
      ell (e (S.presheaf.germ V (f x) (hWV hx) r))
    rw [he, Localization.localRingHom_to_map, f.germ_stalkMap_apply]
    rw [← X.presheaf.germ_res_apply (CategoryTheory.homOfLE hWV) x hx (f.app V r)]
    exact hh _
  have hflat : (f.stalkMap x).hom.Flat ↔ ell.Flat := by
    exact (RingHom.Flat.comp_iff_of_bijective_left
      (f := (f.stalkMap x).hom) (g := h.toRingHom) h.bijective).symm.trans
      ((congrArg RingHom.Flat square).to_iff.trans
        (RingHom.Flat.comp_iff_of_bijective_right
          (f := ell) (g := e.toRingHom) e.bijective))
  let A := Γ(X, W)
  let B := X.presheaf.stalk x
  let M := CommRingCat.KaehlerDifferential phi
  let F := f.relativeDifferentials
  let N := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F
  let L := LocalizedModule q.asIdeal.primeCompl M
  let : Module A N := Module.compHom N (X.presheaf.germ W x hx).hom
  have : IsScalarTower A B N := .of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨g, hg, hloc⟩ := Scheme.isLocalizedModule_affine_germ F
    (inferInstanceAs F.IsQuasicoherent) W hW ⟨x, hx⟩
  have := hloc
  obtain ⟨c, hc⟩ := relativeDifferentials_affine_sections f ⟨W, hW⟩ ⟨V, hV⟩ hWV
  let l : M →ₗ[A] N := g ∘ₗ c.toLinearMap
  have : IsLocalizedModule q.asIdeal.primeCompl l :=
    IsLocalizedModule.of_linearEquiv_right (R := A) (M' := N) q.asIdeal.primeCompl g c
  let E : N ≃ₗ[A] L := (IsLocalizedModule.iso q.asIdeal.primeCompl l).symm
  have hE (m : M) : E (l m) = LocalizedModule.mk m 1 :=
    IsLocalizedModule.iso_symm_apply q.asIdeal.primeCompl l m
  let : Module B L := Module.compHom L h.toRingHom
  have : IsScalarTower A B L := .of_algebraMap_smul fun a m ↦ by
    change h (X.presheaf.germ W x hx a) • m = a • m
    rw [hh]
    exact IsScalarTower.algebraMap_smul (Localization.AtPrime q.asIdeal) a m
  have hscalar (b : B) (m : N) : E (b • m) = h b • E m :=
    (E.extendScalarsOfIsLocalization q.asIdeal.primeCompl B).map_smul b m
  have hd (a : A) :
      E (F.presheaf.germ W x hx (f.relativeDifferentialsDerivation.d a)) =
        LocalizedModule.mk (CommRingCat.KaehlerDifferential.d (f := phi) a) 1 := by
    rw [← hc a, ← hg]
    exact hE _
  refine ⟨W, V, hW, hV, hx, hWV, q, rfl, f.finitePresentation_appLE hV hW hWV,
    hp, e, h, E.toAddEquiv, he, hh, ?_, hscalar, hd, hflat, ?_⟩
  · intro b
    exact DFunLike.congr_fun square b
  · exact spanning_family_transport h E.toAddEquiv hscalar

end AlgebraicGeometry.Scheme.Hom
