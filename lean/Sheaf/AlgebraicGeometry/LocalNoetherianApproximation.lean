/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Algebra.Category.Ring.Constructions
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Sheaf.RingTheory.ColimitFlatRingMap
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.RadicialPreparationFibreComparison
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus
import Sheaf.TraceFormula.GeometricallyIrreducibleFibreLocus

/-!
# Noetherian approximation with geometrically integral fibres

Source: Stacks Project, Algebra, Tag 05FT, first proof paragraph; More on Morphisms,
Tags 05FE, 05FG, 05FH and 05FL (blueprint: lem-trf-local-noetherian-approximation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finitely presented flat algebra with geometrically integral fibres descends to a
finite type flat algebra with geometrically integral fibres over a finite type integer ring.
The pushout square includes compatibility with the original algebra map and canonically
identifies `S` with `S₀ ⊗[R₀] R` (Stacks Project, Algebra, Tag 05FT, first proof paragraph;
More on Morphisms, Tags 05FE, 05FG, 05FH and 05FL).
(blueprint: lem-trf-local-noetherian-approximation)

Proof:
1. Express `R` as the filtered colimit of its finitely generated integer subalgebras
   (lemma-nagata-ring-finite-type-subalgebras). Descend the finite presentation to a stage
   `Rᵢ → Bᵢ` (lem-kun-fp-algebra-descent), and set `Bⱼ = Bᵢ ⊗[Rᵢ] Rⱼ` for `j ≥ i`.
   The stages containing `Rᵢ` remain directed with union `R`, since a finite set of elements
   together with generators of `Rᵢ` is contained in a finitely generated subalgebra.
2. Every stage map is finitely presented by
   lem-weil-pbc-finite-presentation-base-change-composition. Apply
   lem-weil-pbc-colimit-flat-ring-map to the initial algebra map `Rᵢ → Bᵢ` and its base
   changes: its limit is the given flat map. Obtain a stage `j_f` beyond which every
   stage map is flat. This uses finite presentation as an algebra, not as a module.
3. Over `A = Rⱼ_f`, `B = Bⱼ_f`, the geometrically reduced and irreducible fibre loci
   are constructible (lem-trf-geometrically-reduced-fibre-locus and
   lem-trf-geometrically-irreducible-fibre-locus). Identify affine base changes and fibres
   using lem-weil-pbc-fibre-product-affine-spectra. The reduced-locus base-change equality
   and lem-sbc-radicial-preparation-fibre-comparison with the identity universal
   homeomorphism show that the image of `Spec R → Spec A` lies in both loci: integral
   fibres are reduced and irreducible after every field extension
   (def-pc-integral-scheme and def-pc-geometrically-irreducible).
4. By lem-weil-pbc-limit-affine-transition, the affine inverse system has limit `Spec R`.
   Its stages are quasi-compact and quasi-separated, and its transitions are affine.
   Apply lem-weil-pbc-limit-contained-in-constructible to each locus at `j_f`, and take a
   common upper bound `j₀` of the resulting indices. The whole image of `Spec Rⱼ₀ → Spec A`
   lies in both loci. No projection from the limit needs to be surjective.
5. The reduced-locus base-change equality and the same fibre-comparison lemma, together
   with the affine fibre-product identification, give geometrically reduced and
   geometrically irreducible fibres for `Rⱼ₀ → Bⱼ₀`. After every field extension these
   fibres are nonempty, reduced and irreducible, hence integral (def-pc-integral-scheme).
   Thus the fibres are geometrically integral (def-pc-geometrically-irreducible);
   empty fibres are excluded by irreducibility.
6. Set `R₀ = Rⱼ₀`, `S₀ = Bⱼ₀`. The first is of finite type over the integers by its
   construction. The second is flat by step 2 and of finite type because its finite
   presentation supplies finitely many algebra generators
   (def-weil-pbc-finitely-presented-algebra). Step 5 supplies the fibre condition.
   Tensor associativity identifies `(Bᵢ ⊗[Rᵢ] R₀) ⊗[R₀] R` with `Bᵢ ⊗[Rᵢ] R ≅ S`:
   `(b ⊗ a) ⊗ r` maps to `b ⊗ ar`, with inverse `b ⊗ r ↦ (b ⊗ 1) ⊗ r`.
   The identities and algebra compatibility follow on pure tensors. Tensor products
   are coproducts of commutative algebras, giving the stated pushout; the universal
   map sends `b₀ ⊗ r` to the product of the two compatible images and is unique. -/
theorem exists_local_noetherian_approximation
    (R S : CommRingCat.{u}) [Algebra R S] [Algebra.FinitePresentation R S]
    (hflat : (algebraMap R S).Flat)
    (hfibres : ∀ p : PrimeSpectrum R,
      GeometricallyIntegral (Spec.map (CommRingCat.ofHom
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))))) :
    ∃ (R₀ S₀ : CommRingCat.{u}) (_ : Algebra R₀ S₀)
      (a : R₀ →+* R) (b : S₀ →+* S),
      RingHom.FiniteType (Int.castRingHom R₀) ∧
      RingHom.FiniteType (algebraMap R₀ S₀) ∧
      (algebraMap R₀ S₀).Flat ∧
      (∀ p₀ : PrimeSpectrum R₀,
        GeometricallyIntegral (Spec.map (CommRingCat.ofHom
          (algebraMap p₀.asIdeal.ResidueField (p₀.asIdeal.Fiber S₀))))) ∧
      IsPushout (CommRingCat.ofHom (algebraMap R₀ S₀)) (CommRingCat.ofHom a)
        (CommRingCat.ofHom b) (CommRingCat.ofHom (algebraMap R S)) := by
  sorry

end AlgebraicGeometry
