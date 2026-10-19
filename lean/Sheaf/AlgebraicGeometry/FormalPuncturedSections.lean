/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Algebra.Homology.LocalCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.CompleteLocalSubideal
import WeilConjectures.RingTheory.Depth
import Sheaf.RingTheory.SerreCriterionReduced
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Homology.LocalCohomologyGeneratorBound
import Sheaf.Paper.PuncturedDerivedCompletionSections

/-!
# Formal sections on a reduced punctured complete local spectrum

Source: Stacks Project, Tags 0DXR and 0ECR, first half of the proof.
(blueprint: lem-per-formal-punctured-idempotent-algebraization)

The comparison is specified on every neighborhood and every quotient level. These equations
characterize the canonical map, including its restriction and reduction coordinates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace FormalPuncturedSections

/-- The reduced ring in Stacks 0ECR, namely `A / sqrt(0)`.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
abbrev Reduction (A : Type u) [CommRing A] := A ⧸ (⊥ : Ideal A).radical

/-- The quotient morphism from the reduced spectrum; Stacks 0ECR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def reductionMap (A : Type u) [CommRing A] :
    Spec (.of (Reduction A)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A).radical))

/-- The extended ideal `IB` in the reduced ring; Stacks 0DXR and 0ECR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def reducedIdeal {A : Type u} [CommRing A] (I : Ideal A) : Ideal (Reduction A) :=
  I.map (Ideal.Quotient.mk (⊥ : Ideal A).radical)

/-- Opens between `U ∩ V(I)` and `U`, with their inclusion order; Stacks 0DXR.
Taking the opposite category gives the reverse inclusion order used for restriction.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
abbrev Neighborhoods {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (.of A)).Opens) :=
  {V : (Spec (.of A)).Opens // V ≤ U ∧
    (U : Set (Spec (.of A))) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆ V}

/-- The inclusion of the neighborhood poset in the opens of the spectrum; Stacks 0DXR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def neighborhoodInclusion {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (.of A)).Opens) : Neighborhoods I U ⥤ (Spec (.of A)).Opens :=
  (show Monotone (fun V : Neighborhoods I U ↦ V.val) from fun _ _ h ↦ h).functor

/-- The diagram `V ↦ Γ(π⁻¹(V), O)` with restriction maps; Stacks 0DXR, reduced as in 0ECR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def neighborhoodSections {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (.of A)).Opens) : (Neighborhoods I U)ᵒᵖ ⥤ CommRingCat.{u} :=
  (neighborhoodInclusion I U ⋙
    TopologicalSpace.Opens.map (reductionMap A).base).op ⋙
      (Spec (.of (Reduction A))).presheaf

/-- The quotient map of spectra at positive level `n + 1`; Stacks 0DXR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def quotientMap {B : Type u} [CommRing B] (J : Ideal B) (n : ℕ) :
    Spec (.of (B ⧸ J ^ (n + 1))) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))

/-- The open of the positive quotient level lying over `W`; Stacks 0DXR.
For `B = A/sqrt(0)`, `J = IB`, and `W = π⁻¹(U)`, this is `T_(n+1)`.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def thickeningOpen {B : Type u} [CommRing B] (J : Ideal B)
    (W : (Spec (.of B)).Opens) (n : ℕ) : (Spec (.of (B ⧸ J ^ (n + 1)))).Opens :=
  quotientMap J n ⁻¹ᵁ W

/-- Inclusion of consecutive open thickenings, induced by quotient reduction; Stacks 0DXR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def thickeningTransition {B : Type u} [CommRing B] (J : Ideal B)
    (W : (Spec (.of B)).Opens) (n : ℕ) :
    (thickeningOpen J W n).toScheme ⟶ (thickeningOpen J W (n + 1)).toScheme :=
  (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))).resLE
      (thickeningOpen J W (n + 1)) (thickeningOpen J W n) (by
        simp only [thickeningOpen, ← Scheme.Hom.comp_preimage, quotientMap,
          ← Spec.map_comp]
        exact le_rfl)

/-- The inverse diagram of rings `Γ(T_(n+1), O)`, with quotient reduction maps; Stacks 0DXR.
(blueprint: lem-per-formal-punctured-idempotent-algebraization) -/
def formalSectionsDiagram {B : Type u} [CommRing B] (J : Ideal B)
    (W : (Spec (.of B)).Opens) : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.ofSequence (thickeningTransition J W)).op ⋙ Scheme.Γ

end FormalPuncturedSections

namespace Scheme

open FormalPuncturedSections

/-- Formal sections comparison for the reduced structure sheaf of a complete local ring.
Source: Stacks Project, Tag 0DXR (lemma-application-theorem), specialized as in the first half
of the proof of Tag 0ECR (lemma-punctured-still-connected).
(blueprint: lem-per-formal-punctured-idempotent-algebraization)

The displayed equations say that the isomorphism takes a section on a neighborhood to its
restrictions on every infinitesimal thickening. On a thickening, the inverse image of every
neighborhood equals the inverse image of `U`: all its points lie over `V(I)`. Thus the
restriction after each limit projection is invertible, and these equations characterize
the canonical comparison, rather than an unspecified ring isomorphism.

Proof: (1) The local-cohomology generator bound makes `cd(A,I)` finite and nonnegative.
Completeness for the maximal ideal implies completeness for `I`, by
[lem-sbc-complete-local-subideal]. (2) Put `B = A/sqrt(0)`. At minimal primes the component
dimension hypothesis gives the dimension alternative of
[lem-per-local-support-completion-comparison]. At other primes reducedness gives depth at
least one by Serre's reducedness criterion; lifting a regular element along the local
surjection from `A_p` gives the same depth bound for the localized `A`-module `B`.
(3) Apply that support comparison to obtain `J₀` with `V(J₀) ∩ V(I) = {m}` and degree-zero
and degree-one comparison isomorphisms for all sufficiently small defining ideals.
(4) For a neighborhood `V` inside the complement of `V(J₀)`, choose a defining ideal `J'`
for its complement and use `J = J'J₀`. The two exact localization rows of
[lem-per-completed-affine-localization-diagram] compare sections on `V` to completed
punctured sections. (5) The identity on `B` and the degree-zero and degree-one support
isomorphisms give bijectivity of the section comparison by the exact-sequence diagram chase.
(6) [lem-per-punctured-derived-completion-sections] identifies degree zero with the limit of
quotient sections, naturally on every open neighborhood. The quotient pushforward formula
identifies these sections with those of `T_n`, respecting restriction and ring operations.
Thus the bijection has exactly the reduction coordinates in the displayed equations.
(7) Neighborhoods inside the chosen one are cofinal, by intersection. Surjectivity follows
from a representative there; equality of images forces equality on a common smaller
neighborhood by injectivity there. Hence the colimit comparison is bijective, and its ring
structure makes it the required isomorphism. -/
theorem formal_punctured_sections_comparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hfinite : topologicalKrullDim (Spec (.of A)) < ⊤)
    (I : Ideal A) (hI : I ≠ ⊤)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    (d : WithBot ℕ∞)
    (hd : IsLeast {e : WithBot ℕ∞ | ∃ Z ∈ irreducibleComponents (Spec (.of A)),
      topologicalKrullDim Z = e} d)
    (hbound : ModuleCat.localCohomologicalDimension I + 1 < d) :
    ∃ e : colimit (neighborhoodSections I U) ≅
        limit (formalSectionsDiagram (reducedIdeal I) (reductionMap A ⁻¹ᵁ U)),
      ∀ (V : Neighborhoods I U) (n : ℕ),
        colimit.ι (neighborhoodSections I U) (op V) ≫ e.hom ≫
          limit.π (formalSectionsDiagram (reducedIdeal I) (reductionMap A ⁻¹ᵁ U)) (op n) ≫
          (thickeningOpen (reducedIdeal I) (reductionMap A ⁻¹ᵁ U) n).topIso.hom ≫
          (Spec (.of (Reduction A ⧸ reducedIdeal I ^ (n + 1)))).presheaf.map
            (homOfLE ((TopologicalSpace.Opens.map
              (quotientMap (reducedIdeal I) n).base).map
                ((TopologicalSpace.Opens.map (reductionMap A).base).map
                  (homOfLE V.property.1))).le).op =
          (quotientMap (reducedIdeal I) n).app (reductionMap A ⁻¹ᵁ V.val) := by
  sorry

end Scheme

end AlgebraicGeometry

end
