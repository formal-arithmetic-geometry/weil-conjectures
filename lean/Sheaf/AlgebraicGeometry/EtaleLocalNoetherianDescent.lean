/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.DirectSum.Module

/-!
# Descent of local Noetherianity along an etale covering

Source: Stacks Project, Descent, Tag 034C (descent direction), specialized to etale
coverings using Topologies, Tag 021N
(blueprint: lem-trf-etale-local-noetherian-descent).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Local Noetherianity descends along a jointly surjective family of etale morphisms.
Source: Stacks Project, Descent, Tag 034C; Topologies, Tags 021N and 0218
(blueprint: lem-trf-etale-local-noetherian-descent).

Proof plan:
1. For each affine open `W` of `T`, base change the covering to `W`
   (lem-weil-pbc-etale-covering-base-change). Identify each base change with the open
   preimage of `W` (lem-weil-pbc-open-preimage-fibre-product), and refine to finitely
   many affine opens `U_j` of the covering schemes
   (lem-weil-pbc-etale-covering-affine-refinement). Their rings `A_j` are Noetherian
   by pqf-lem-affine-open-locnoeth.
2. Write `R` for the sections of `W`. Etaleness implies flatness
   (def-weil-etale-morphism); the affine flatness criterion
   (lem-weil-pbc-flat-morphism-affine-criterion) and finite-product flatness
   (lem-weil-pbc-finite-product-flat-modules) make `R` to the product of the `A_j`
   flat. Joint surjectivity and the projections of that product give a surjection
   on prime spectra (def-weil-affine-spectrum). Thus this map is faithfully flat
   (lem-weil-pbc-flat-surjective-spectrum-faithfully-flat). The finite product is
   Noetherian by the componentwise ideal argument, so faithfully flat descent
   (lem-weil-pbc-faithfully-flat-descent-noetherian) makes `R` Noetherian.
3. Apply the affine-open-cover characterization of local Noetherianity
   (pqf-def-locnoeth) to conclude that `T` is locally Noetherian. -/
theorem isLocallyNoetherian_of_etale_cover
    {T : Scheme.{u}} {A : Type v} (Tₐ : A → Scheme.{u}) (t : ∀ a, Tₐ a ⟶ T)
    [∀ a, Etale (t a)] [∀ a, IsLocallyNoetherian (Tₐ a)]
    (hcover : ∀ x : T, ∃ a : A, ∃ y : Tₐ a, t a y = x) :
    IsLocallyNoetherian T := by
  classical
  let 𝒰 := Scheme.Cover.mkOfCovers (P := @Etale) A Tₐ t hcover
  apply (isLocallyNoetherian_iff_openCover T.affineCover).mpr
  intro k
  let W := T.affineCover.X k
  let 𝒰' := 𝒰.pullback₁ (T.affineCover.f k)
  have (a : 𝒰'.I₀) : Etale (𝒰'.f a) := Scheme.Cover.map_prop 𝒰' a
  have : QuasiCompactCover 𝒰'.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun a ↦ (𝒰'.f a).isOpenMap)
  have (a : 𝒰'.I₀) : IsLocallyNoetherian (𝒰'.X a) := by
    change IsLocallyNoetherian (Limits.pullback (T.affineCover.f k) (t a))
    exact isLocallyNoetherian_of_isOpenImmersion (Limits.pullback.snd _ _)
  obtain ⟨𝒱, e, hfin, he⟩ := QuasiCompactCover.exists_hom (𝒰 := 𝒰')
  let := hfin
  let := Fintype.ofFinite 𝒱.I₀
  have (i : 𝒱.I₀) : IsLocallyNoetherian (Spec (𝒱.X i)) := by
    let := he i
    exact isLocallyNoetherian_of_isOpenImmersion (e.h₀ i)
  let R : Type u := Γ(W, ⊤)
  let B (i : 𝒱.I₀) : Type u := Γ(Spec (𝒱.X i), ⊤)
  let (i : 𝒱.I₀) : Algebra R (B i) := (𝒱.f i).appTop.hom.toAlgebra
  have (i : 𝒱.I₀) : Module.Flat R (B i) := by
    have : Etale (𝒱.f i) := 𝒱.map_prop i
    exact (𝒱.f i).flat_appTop
  have (i : 𝒱.I₀) : IsNoetherianRing (B i) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : Module.Flat R (∀ i, B i) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R 𝒱.I₀ B).symm
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R (∀ i, B i))) := by
    intro p
    obtain ⟨x, hx⟩ := W.isoSpec.hom.surjective p
    let i := 𝒱.idx x
    obtain ⟨y, hy⟩ := 𝒱.covers x
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom B i)
      ((Spec (𝒱.X i)).isoSpec.hom y), ?_⟩
    change (Spec.map (𝒱.f i).appTop) ((Spec (𝒱.X i)).isoSpec.hom y) = p
    rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality,
      Scheme.Hom.comp_apply, hy, hx]
  let := Module.FaithfullyFlat.of_comap_surjective hsurj
  have hR : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := R) (M := R) (A := ∀ i, B i)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R (∀ i, B i) _).symm.toLinearEquiv)
  exact isLocallyNoetherian_of_isOpenImmersion W.isoSpec.hom

end AlgebraicGeometry
