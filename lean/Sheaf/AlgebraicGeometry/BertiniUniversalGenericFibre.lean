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
import Sheaf.AlgebraicGeometry.BertiniGenericFibreChart
import Sheaf.AlgebraicGeometry.IrreducibleDominantGenericFibre
import Sheaf.AlgebraicGeometry.FibreResidueArrow
import Sheaf.AlgebraicGeometry.BertiniAffineFunctionField
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility

/-!
# The generic fibre of the universal Bertini incidence family

Source: Stacks Project, More on Morphisms, Tag 0G4F, middle and final proof paragraphs.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The universal incidence family has geometrically irreducible generic fibre under
Bertini's two codimension hypotheses.

Source: Stacks Project, More on Morphisms, Tag 0G4F, middle and final proof paragraphs.
(blueprint: lem-zl-bertini-universal-generic-fibre).

Proof: The incidence chart theorem supplies the finite type affine domain, the local
codimension-two intersection, geometric irreducibility of its fraction field, irreducibility
of the incidence scheme, dominance of the projection, and its generic residue-field arrow.
Dominance sends the incidence generic point to the coefficient generic point. The generic
fibre is irreducible: any two nonempty open subsets contain this point viewed in the fibre.
The fibre inclusion is an embedding, so this point is generic in the fibre. Its residue
field map is identified with the original incidence residue-field map by the fibre
residue-arrow isomorphism. The affine algebraic Bertini theorem gives geometric
irreducibility of the corresponding field extension. Transport through these arrow
isomorphisms and apply the generic-residue-field criterion to the irreducible generic
fibre. Finally transport along the equality of parameter generic points. -/
theorem geometricallyIrreducible_bertiniUniversal_genericFiber
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
        GeometricallyIrreducible
          ((bertiniUniversalProjection (Y ↘ Spec (.of k)) L
            (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))).fiberToSpecResidueField
            (genericPoint (Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k))))) := by
  classical
  intro ψ hcomp hbase r b
  let q := bertiniUniversalProjection (Y ↘ Spec (.of k)) L
    (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))
  let η := genericPoint (Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k)))
  obtain ⟨A, a, hft, hdom, n, hn, g, hdim, hgeom, hI, hD, ⟨e⟩⟩ :=
    exists_bertiniIncidenceChart k Y L V ψ hcomp hbase r b
  let := a
  let := hft
  let := hdom
  let := hI
  let := hD
  let H := (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L
    (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))).subscheme
  let ξ := genericPoint H
  have he : q ξ = η := by
    apply IsGenericPoint.eq _ (genericPoint_spec _)
    have hR : closure (q '' (Set.univ : Set H)) = Set.univ := by
      rw [Set.image_univ]
      exact q.denseRange.closure_range
    exact hR ▸ (genericPoint_spec H).image q.continuous
  have hgeneric : IsGenericPoint (q ξ)
      (Set.univ : Set (Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k)))) := by
    rw [he]
    exact genericPoint_spec _
  have hgoal : GeometricallyIrreducible (q.fiberToSpecResidueField (q ξ)) := by
    have := irreducibleSpace_fiber_of_isGenericPoint q (q ξ) hgeneric
    let F := (Spec (.of (MvPolynomial (ULift.{u} (Fin r)) k))).residueField (q ξ)
    let : (q.fiber (q ξ)).Over (Spec (.of F)) := ⟨q.fiberToSpecResidueField (q ξ)⟩
    have hx : IsGenericPoint (q.asFiber ξ) (Set.univ : Set (q.fiber (q ξ))) := by
      rw [isGenericPoint_iff_specializes]
      intro z
      simp only [Set.mem_univ, iff_true]
      apply (q.fiberι (q ξ)).isEmbedding.isInducing.specializes_iff.mp
      simpa only [Scheme.Hom.fiberι_asFiber] using
        (genericPoint_spec H).specializes (Set.mem_univ (q.fiberι (q ξ) z))
    have hξ : genericPoint (q.fiber (q ξ)) = q.asFiber ξ :=
      (genericPoint_spec _).eq hx
    obtain ⟨e₀⟩ := nonempty_fibreResidueArrow_iso q ξ
    change GeometricallyIrreducible ((q.fiber (q ξ)) ↘ Spec (.of F))
    apply (geometricallyIrreducible_iff_genericResidueField F (q.fiber (q ξ))
      (genericPoint (q.fiber (q ξ))) (genericPoint_spec _)).mpr
    rw [hξ]
    exact (MorphismProperty.arrow_mk_iso_iff @GeometricallyIrreducible (e₀ ≪≫ e)).mpr
      (FieldTheory.geometricallyIrreducible_bertiniAffineFunctionField k A n hn g hdim hgeom)
  change GeometricallyIrreducible (q.fiberToSpecResidueField η)
  exact he ▸ hgoal

end AlgebraicGeometry
