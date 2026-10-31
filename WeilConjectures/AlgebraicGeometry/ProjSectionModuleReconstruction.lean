/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandardProjTwistTensor
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Adjoin.Basic
import WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Reconstruction from all twisted sections on standard Proj

Source: Stacks Project, properties.tex, Tag 0AG5 (lemma-proj-quasi-coherent),
and constructions.tex, Tag 0B5I (lemma-comparison-proj-quasi-coherent).
(blueprint: lem-sfb-proj-section-module-reconstruction).

The associated sheaves of the shifted section module are presented by the existing
`IsStandardProjShiftSheaf` interface. The fraction equation multiplies by the
free generator f^a, so it specifies division by that generator without choosing
an inverse or a second tensor product.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open AlgebraicGeometry.Scheme.Modules
open scoped DirectSum

namespace AlgebraicGeometry.Proj

variable {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- The actual additive direct sum of all integer twisted global sections.
Source: Stacks 0AG5 and 0B5I (blueprint: lem-sfb-proj-section-module-reconstruction). -/
abbrev projTwistedSections (F : (Proj 𝒜).Modules) :=
  ⨁ n : ℤ, Γ(F ⊗ twist 𝒜 n, ⊤)

/-- The grading on the twisted-section direct sum is its summand-image grading.
Source: Stacks 0AG5 and 0B5I (blueprint: lem-sfb-proj-section-module-reconstruction). -/
noncomputable def projTwistedSectionsGrading (F : (Proj 𝒜).Modules) :
    ℤ → AddSubgroup (projTwistedSections 𝒜 F) :=
  fun n ↦ (DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) n).range

/-- The associated sheaves of the shifts exist, and their zeroth shift admits a
unique isomorphism to F satisfying the counit's chart formula.
The chart predicate includes injectivity, exact fraction range, scalar compatibility
and localization restrictions; thus G is the associated sheaf, not an arbitrary sheaf.
Source: Stacks 0B5I and 0AG5 (blueprint: lem-sfb-proj-section-module-reconstruction). -/
def IsProjSectionReconstruction (F : (Proj 𝒜).Modules)
    [Module S (projTwistedSections 𝒜 F)] : Prop :=
  ∃ (G : ℤ → (Proj 𝒜).Modules)
    (chart : ∀ (n : ℤ) (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      Γ(G n, basicOpen 𝒜 f) →+ LocalizedModule.Away f (projTwistedSections 𝒜 F)),
    IsStandardProjShiftSheaf 𝒜 (projTwistedSectionsGrading 𝒜 F) G chart ∧
    ∃! ε : G 0 ⟶ F, IsIso ε ∧
      ∀ (f : S) (hf : f ∈ 𝒜 1) (a : ℕ)
        (t : Γ(F ⊗ twist 𝒜 (a : ℤ), ⊤)) (q : Γ(G 0, basicOpen 𝒜 f)),
        chart 0 f 1 (by decide) hf q =
          mk (DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) (a : ℤ) t)
            (⟨f ^ a, ⟨a, rfl⟩⟩ : Submonoid.powers f) →
        tmulSection (ε.app (basicOpen 𝒜 f) q) (twistPowSection (a : ℤ) hf) =
          (F ⊗ twist 𝒜 (a : ℤ)).presheaf.map
            (homOfLE (le_top : basicOpen 𝒜 f ≤ ⊤)).op t

/-- The all-integer twisted-section sum has its canonical graded S-module action,
and its associated sheaf is canonically isomorphic to the original quasi-coherent
module, with the prescribed fraction evaluation on every degree-one standard open.
No Noetherian or finite-type hypothesis on F is imposed.

Source: Stacks Project, properties.tex, Tag 0AG5, and constructions.tex, Tag 0B5I.
(blueprint: lem-sfb-proj-section-module-reconstruction).

Proof:
1. Choose the finite degree-one algebra generators. Their standard opens cover by
   prop-nagata-proj-standard-open, since their ideal contains the irrelevant ideal.
   The standard-open intersections are affine by
   lem-weil-pbc-proj-standard-open-inclusion. The affine compactness and affine-cover
   criterion of lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-quasi-separated-affine-cover-criterion make X qcqs. With no generators,
   X is empty and the empty cover gives the same conclusion.
2. Construct the action by summing homogeneous multiplication on the direct sum.
   The unit, associativity and naturality equations of
   lem-sfb-standard-proj-twist-tensor prove its module laws and grading compatibility.
   Apply lem-sfb-proj-section-tensor-localization-comparison with L = O(1) at each
   generator. It identifies the local fraction module and evaluation with those of
   lem-sc-p1-invertible-section-localization. The latter is an isomorphism since
   X is qcqs and F is quasi-coherent.
3. By lem-sfb-proj-section-fraction-naturality the fraction evaluations commute with
   every standard-open restriction. The chart presentation of
   lem-weil-pbc-proj-graded-module-sheaf-exists and the standard-open basis therefore
   glue them to the unique O_X-linear counit. Its fraction formula holds on every
   degree-one chart. Both sheaves are quasi-coherent; local bijectivity from step 2
   and lem-weil-pbc-quasi-coherent-iso-on-affine-cover make it an isomorphism.
   The free generator twistPowSection turns division into the displayed equation.
   Zero sheaves, zero/nilpotent denominators and empty Proj are included.
-/
theorem projSectionModuleReconstruction
    (hgen : ∃ (r : ℕ) (f : Fin r → S),
      (∀ i : Fin r, f i ∈ 𝒜 1) ∧ Algebra.adjoin (𝒜 0) (Set.range f) = ⊤)
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] :
    ∃ m : Module S (projTwistedSections 𝒜 F),
      (∀ (e : ℕ) (n : ℤ) (s : S) (hs : s ∈ 𝒜 e)
        (t : Γ(F ⊗ twist 𝒜 n, ⊤)),
        @SMul.smul S (projTwistedSections 𝒜 F) m.toSMul s
            (DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) n t) =
          DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) (n + e)
            ((F ◁ twistMul n hs).app ⊤ t)) ∧
      @IsProjSectionReconstruction S _ 𝒜 _ F m := by
  sorry

end AlgebraicGeometry.Proj
