/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.Algebra.Module.GradedModuleAwayRestriction
import Sheaf.Topology.SheafOfModulesFromBasis
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherence from graded-module charts

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-quasicoherent)
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
(blueprint: lem-weil-pbc-proj-graded-module-chart-quasicoherent) -/
local instance localizedModuleHomogeneousScalarsChartQuasicoherent (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "ModX" => SheafOfModules (moduleRings (Proj 𝒜).toRingedSpace)

/-- A sheaf with the degree-zero localization charts is quasi-coherent.
Source: Stacks Project, Constructions, Lemmas 01M4, 01M7 (2) and 01MB;
Schemes, Lemma 01IA.
(blueprint: lem-weil-pbc-proj-graded-module-chart-quasicoherent)

Proof:
1. Fix f. Identify its affine standard open with Spec R[f] using basicOpenIsoSpec.
   Given r in R[f], write r=a/f^n with a homogeneous of degree n*deg(f). The homogeneous
   element h=f*a has positive degree, even when a=0, and D[h] inside D[f] corresponds
   to the principal open D(r), by awayι_preimage_basicOpen. Its principal generator is
   r^deg(f). Localizing at r or this positive power gives the same module.
2. The comparisons in gradedModuleAwayRestriction identify Z[h] with Z[f] localized
   at this generator, hence at r. The given rho agrees with the canonical maps by its
   fraction formula: represent every section by y/f^m and compare the prescribed image
   for a homogeneous relation h^e=b*f. The ring map agrees by ambient localization
   uniqueness and injectivity of the homogeneous inclusion.
3. Use hscalar and hrestriction to identify the sections of F on these principal opens
   with those of the tilde sheaf of the R[f]-module Z[f]. For nested opens the comparison
   composition law identifies both restrictions with the same localization map.
   The basis-extension uniqueness theorem therefore gives an isomorphism on D[f].
4. Mathlib's tilde sheaf is quasi-coherent. Quasi-coherence is local, and the positive
   homogeneous standard opens cover Proj, so F is quasi-coherent. On an empty chart its
   denominator is nilpotent and both the ring and module localizations vanish; the tilde
   comparison remains valid. If Proj is empty, the local criterion is vacuous. -/
theorem gradedModuleChart_quasicoherent
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (hZ : (∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)))
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (hlaws : (∀ (f g : Fidx) (i : D[g] ≤ D[f]),
        (∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) ∧
        (∀ (r : R[f]) (q : Z f), rho f g i (r • q) = rhoS f g i r • rho f g i q) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g.val.1 ^ e = a * f.val.1 →
          ∀ (m : ℕ) (y : M) (q : Z f),
            (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
            (rho f g i q : N[g]) = mk (a ^ m • y)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1))) ∧
      (∀ (f : Fidx) (i : D[f] ≤ D[f]) (q : Z f), rho f f i q = q) ∧
      (∀ (f g h : Fidx) (i : D[g] ≤ D[f]) (j : D[h] ≤ D[g]) (q : Z f),
        rho g h j (rho f g i q) = rho f h (j.trans i) q) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]), D[f] = D[g] →
        Function.Bijective (rho f g i)))
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
    F.IsQuasicoherent := by sorry

end AlgebraicGeometry.Proj
