/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PicardDerivedModelSections
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf

/-! # Scalar cycles as derived test sections

Source: Stacks Project, Tag 0BF2, the degree-zero cycle calculation.
(blueprint: lem-sc-picard-scalar-derived-cycles)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The scalar-cycle calculation for an arbitrary derived object with a fixed connective
strictly perfect model. No direct image or family of line bundles occurs in this lemma.
Source: Stacks Project, Tag 0BF2, degree-zero cycle calculation; Tags 08C4 and 0D5S.
(blueprint: lem-sc-picard-scalar-derived-cycles)

Proof: On the affine U, the finite-projective terms of K are quasi-coherent. The affine
module equivalence sheafifies e0 and e1, and hd identifies the degree-zero differential
with the vector d. Strictly perfect complexes are K-flat. Termwise pullback therefore
computes derived pullback on every smaller open and on the residue spectrum. It remains
connective, so degree-zero hypercohomology is the global sections of the kernel of the
outgoing differential: the spectral sequence has only its (0,0) term in total degree zero.
This is also the group of derived morphisms from the degree-zero structure sheaf. On V,
every scalar cycle supplies such a morphism, with no boundaries in degree zero. On the
residue spectrum hdw kills the differential, and e0 identifies all such morphisms with
the residue field. Pullback of the representing morphism is evaluation of its scalar.
The canonical composition comparison is computed on these K-flat representatives, so
conjugating by it is precisely picardDerivedModelRestriction. Transport throughout by
hE gives the stated c and lifts. The fixed hE makes c independent of V. Rank m=0 has
zero outgoing differential and satisfies the same argument; w excludes empty V and U. -/
theorem picard_scalar_derived_cycles
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d)
    (hdw : ∀ i, W.evaluation U w hwU (d i) = 0) :
    ∃ c : picardDerivedModelSections E (W.fromSpecResidueField w) ≃+ W.residueField w,
      ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U) (a : Γ(W, V)),
        (a • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i)) = 0) →
        ∃ ξ : picardDerivedModelSections E V.ι,
          picardDerivedModelRestriction E (picardResidueLift W w V hwV) V.ι
              (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV) ξ =
            c.symm (W.evaluation V w hwV a) := by sorry

end AlgebraicGeometry.Scheme
