/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Sheaf.Algebra.Module.GradedModuleAwayRestriction
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties
import Sheaf.RingTheory.CoverModuleExact

/-!
# Finite gluing of graded-module charts

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-gluing)
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
(blueprint: lem-weil-pbc-proj-graded-module-chart-gluing) -/
local instance localizedModuleHomogeneousScalarsChartGluing (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1

/-- Finite unique gluing for a graded-module chart system, including the empty cover.
Source: Stacks Project, Constructions, Lemma 01M4 (1)(c)--(h) and the construction
before Definition 01M6; Algebra, Lemma 00EK.
(blueprint: lem-weil-pbc-proj-graded-module-chart-gluing)

Proof:
1. Use standardOpenProperties to obtain the unit-ideal generators
   u_i = g_i^deg(f)/f^deg(g_i) in R[f] for the displayed cover.
2. Apply gradedModuleAwayRestriction. Its submodule has the same carrier as Z, so
   Submodule.ext identifies them. The given rho agrees with its restriction: represent
   each element by an ordinary localized fraction and use the stated fraction formula.
   The ambient ring maps agree by the uniqueness of maps out of S_f that commute with S;
   injectivity of homogeneous-localization inclusion gives equality of rhoS.
3. Transport the principal localization comparisons to Z. The comparison to each chart
   sends t/1 to rho(t). The generator for the product chart is u_i*u_j: this follows by
   multiplying the two fractions. The comparison composition law identifies the two
   overlap maps with the canonical localization maps in coverModuleExact.
4. Transport q_i back along these comparisons. The overlap assumption is exactly the
   compatibility hypothesis of coverModuleExact. That theorem gives a unique t in Z f,
   and its localization equations give the asserted restriction equations. Conversely
   any solution localizes to this glued t and hence equals it. For n=0 the unit-ideal
   hypothesis forces R[f] to be the zero ring and Z f the zero module, so the same
   existence and uniqueness proof applies without a maximum over an empty set. -/
theorem gradedModuleChart_gluing
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
        ∀ r : R[f], (rhoS f g i r).val = l r.val) :
    let fg := fun f g : Fidx ↦
      (⟨(f.val.1 * g.val.1, f.val.2 + g.val.2),
        Nat.add_pos_left f.property.1 g.val.2,
        SetLike.mul_mem_graded f.property.2 g.property.2⟩ : Fidx)
    ∀ (f : Fidx) (n : ℕ) (g : Fin n → Fidx)
      (hg : ∀ i, D[g i] ≤ D[f]),
      (⨆ i, D[g i]) = D[f] → ∀ q : ∀ i, Z (g i),
      (∀ i j,
        rho (g i) (fg (g i) (g j))
          (by simpa only [fg, basicOpen_mul] using
            (inf_le_left : D[g i] ⊓ D[g j] ≤ D[g i])) (q i) =
        rho (g j) (fg (g i) (g j))
          (by simpa only [fg, basicOpen_mul] using
            (inf_le_right : D[g i] ⊓ D[g j] ≤ D[g j])) (q j)) →
      ∃! t : Z f, ∀ i, rho f (g i) (hg i) t = q i := by sorry

end AlgebraicGeometry.Proj
