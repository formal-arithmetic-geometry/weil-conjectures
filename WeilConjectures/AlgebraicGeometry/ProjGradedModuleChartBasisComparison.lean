/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleChartBasisComparisonFixed

/-!
# Principal-open section comparison for a graded-module chart

## References

* Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations. -/
local instance localizedModuleHomogeneousScalarsBasisComparison (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false
set_option linter.unusedVariables false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "ModX" => (Proj 𝒜).Modules

/-- The fraction-chart descriptions give compatible linear equivalences on the principal
open basis of a fixed affine chart. This asserts only the sectionwise comparison;
extending these maps to a morphism of sheaves is a separate step
(Stacks, Constructions, Lemmas 01MB, 01M4 and 01M7). -/
theorem gradedModuleChart_basisComparison
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (U : ∀ (f g : Fidx), R[f])
    (hU : ∀ (f g : Fidx), (U f g).val = Localization.mk (g.val.1 ^ f.val.2)
      (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1))
    (theta : ∀ (f g : Fidx), D[g] ≤ D[f] →
      LocalizedModule.Away (U f g) (Z f) ≃+ Z g)
    (thetaS : ∀ (f g : Fidx), D[g] ≤ D[f] → Localization.Away (U f g) ≃+* R[g])
    (htheta : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      (∀ r : R[f], thetaS f g i (algebraMap R[f] (Localization.Away (U f g)) r) =
        rhoS f g i r) ∧
      (∀ q : Z f, theta f g i (mk q 1) = rho f g i q) ∧
      (∀ (r : Localization.Away (U f g)) (q : LocalizedModule.Away (U f g) (Z f)),
        theta f g i (r • q) = thetaS f g i r • theta f g i q))
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val)
    (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hscalar : ∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
      alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s)
    (hrestriction : ∀ (f g : Fidx) (i : D[g] ≤ D[f])
      (s : F.val.obj (op D[f])),
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)) :
    ∀ f : Fidx,
      let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
      let E := Scheme.Modules.restrict F D[f].ι
      let G := Scheme.Modules.restrict (tilde (ModuleCat.of R[f] (Z f))) e.hom
      let B := Set.range (fun r : R[f] ↦ e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r)
      ∃ l : ∀ U : B, E.val.obj (op U.val) ≃ₗ[
          D[f].toScheme.ringCatSheaf.obj.obj (op U.val)]
          G.val.obj (op U.val),
        ∀ (U V : B) (i : V.val ≤ U.val) (s : E.val.obj (op U.val)),
          l V (E.val.map (homOfLE i).op s) = G.val.map (homOfLE i).op (l U s) := by
  intro f
  exact gradedModuleChart_basisComparison_fixed 𝒜 Z rhoS rho U hU theta thetaS htheta
    hcanonical F alpha hscalar hrestriction f

end AlgebraicGeometry.Proj
