/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.FieldTheory.BertiniFieldExtension
import Sheaf.AlgebraicGeometry.BertiniIndependentFunctions
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Sheaf.AlgebraicGeometry.BertiniAffineIncidenceIrreducible
import Sheaf.AlgebraicGeometry.BertiniIncidenceElimination
import Sheaf.AlgebraicGeometry.BertiniAffineIncidenceChart
import Sheaf.AlgebraicGeometry.BertiniUniversalZeroSection
import WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Affine presentation of the universal Bertini incidence family

Source: Stacks Project, More on Morphisms, Tag 0G4F, middle and final proof paragraphs.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Affine function-field presentation of the universal Bertini incidence scheme.
This supplies the local codimension-two intersection and the arrow isomorphism obtained
by eliminating the first incidence variable. It makes no geometric-irreducibility claim
about the incidence function field.

Source: Stacks Project, More on Morphisms, Tag 0G4F, the reduction, incidence-irreducibility,
and function-field identification in its proof. (blueprint: lem-zl-bertini-generic-fibre-chart).

Proof: Reduce Y; its nilradical is nilpotent by Noetherianity, and reduction after any field
base change leaves section zero-scheme supports and residue fields unchanged.
The three supplied vectors are independent by evaluation at the generic point of W and
the principal ideal height bound.
Extend them to a basis. On each nonempty trivializing affine Spec B the first section is
nonzero and the base-locus condition gives height at least two for the coefficient ideal.
Use exists_bertiniAffineIncidenceChart to identify the incidence chart and its parameter
map with the polynomial quotient. Apply irreducibleSpace_bertiniAffineIncidence using the
coefficient height bound. The zero-parameter section supplies a point over every point of
the base. Thus the
incidence charts over intersecting base opens intersect, and their union is irreducible.
Choose an affine Spec A in the complement of the first zero locus meeting W. Trivialize by
the first section and let g be the other section ratios. Its first two functions vanish on a
component of dimension
dim A minus two by the finite-type domain chain-length formula. The generic-residue-field
criterion applied to Y gives geometric irreducibility of Frac A over k. The independent
functions lemma implies independence of the variables and sum g_i x_i, hence dominance of
the incidence projection. The proved incidence elimination theorem solves for the first
variable, identifying the generic residue field of H with Frac(Frac(A)[x_2,...,x_r]).
The parameter residue field maps isomorphically onto
k(x_2,...,x_r,sum g_i x_i); the minus sign is absorbed by a coordinate automorphism.
These identifications yield the asserted arrow isomorphism. The original basis is related
to the adapted basis by an invertible linear coordinate change, and the ULift indexing by
a variable-renaming isomorphism; transport the presentation through both. -/
theorem exists_bertiniIncidenceChart
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [GeometricallyIrreducible (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ ψ : V →ₗ[k] Γ(L, ⊤),
      (∃ (v₁ v₂ v₃ : V) (W : TopologicalSpace.IrreducibleCloseds Y),
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support ∩
            (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support) W ∧
        ¬ (W : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₁)).zeroLocus.support ∧
        Order.coheight W = 2) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ ⋂ w : V,
            ((Scheme.Modules.homOfGlobalSection L (ψ w)).zeroLocus.support : Set Y)) B →
        2 ≤ Order.coheight B) →
      ∀ (r : ℕ) (b : Module.Basis (Fin r) k V),
        let H := (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L
          (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))).subscheme
        let q := bertiniUniversalProjection (Y ↘ Spec (.of k)) L
          (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))
        ∃ (A : CommRingCat.{u}) (a : Algebra k A),
          letI := a
          ∃ (hft : Algebra.FiniteType k A) (hdom : IsDomain A),
            letI := hft
            letI := hdom
            ∃ (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A),
              (∃ W : Set (PrimeSpectrum.zeroLocus
                  ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
                W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
                  ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
                topologicalKrullDim W + 2 = ringKrullDim A) ∧
              GeometricallyIrreducible
                (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing A)))) ∧
              ∃ hI : IrreducibleSpace H,
                letI := hI
                IsDominant q ∧ Nonempty (Arrow.mk
                  (Spec.map (q.residueFieldMap (genericPoint H))) ≅
                  Arrow.mk (Spec.map (CommRingCat.ofHom
                    (algebraMap
                      (FieldTheory.bertiniBaseField k (FractionRing A) n
                        (fun i ↦ algebraMap A (FractionRing A) (g i)))
                      (FieldTheory.bertiniOmega (FractionRing A) n))))) := by
  sorry

end AlgebraicGeometry
