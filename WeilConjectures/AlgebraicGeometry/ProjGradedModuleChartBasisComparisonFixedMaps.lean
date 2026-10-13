/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Principal-open section comparison for a graded-module chart

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core) -/
local instance localizedModuleHomogeneousScalarsBasisComparisonFixedCore (T : Submonoid S) :
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

/-- On each principal open of a fixed chart, there is a bijective linear comparison
extending the same additive comparison on whole-chart sections.

Source: Stacks Project, Constructions, Lemmas 01M4, 01M7 and 01MB, last paragraph.
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-core)

Proof:
Use alpha f and the inverse of the tilde global-section equivalence to define the
whole-chart comparison a, transporting through the two open-immersion restriction
identifications. For a principal open D(r), represent r as b/f^n with b homogeneous
of degree n*deg(f), and set g=f*b of positive degree (n+1)*deg(f). The chart
intersection formula identifies its inverse image in D_+(f) with D_+(g), since
U f g=r^deg(f) and D(r^deg(f))=D(r). The hypothesis hcanonical identifies the
ring restriction with the canonical localization map; htheta and hrestriction
identify module restriction with the localization map of Z f. Thus sections of
E on this open are the localization of Z f at r, by theta and alpha g. Sections
of G are the same localization, by tilde.toOpen and the chart isomorphism.
The unique comparison extending the identity on Z f is linear over the localized
section ring and bijective by these two localization descriptions. It agrees with
a on restrictions of whole-chart sections by htheta and hrestriction. This
construction works independently for each open in B; no compatibility for nested
proper opens is asserted here. For r=0, localization and the section modules on
the empty open are zero, so the assertion still holds. -/
theorem gradedModuleChart_basisComparison_fixed_core
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
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s))
    (f : Fidx) :
      let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
      let E := Scheme.Modules.restrict F D[f].ι
      let G := Scheme.Modules.restrict (tilde (ModuleCat.of R[f] (Z f))) e.hom
      let B := Set.range (fun r : R[f] ↦ e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r)
      ∃ a : E.val.obj (op ⊤) →+ G.val.obj (op ⊤),
        ∀ V : B, ∃ l : E.val.obj (op V.val) →ₗ[
          D[f].toScheme.ringCatSheaf.obj.obj (op V.val)] G.val.obj (op V.val),
          Function.Bijective l ∧ ∀ s : E.val.obj (op ⊤),
            l (E.val.map V.val.leTop.op s) =
              G.val.map V.val.leTop.op (a s) := by sorry

end AlgebraicGeometry.Proj
