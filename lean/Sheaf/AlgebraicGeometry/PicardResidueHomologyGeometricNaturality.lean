/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison
import Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixed
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Geometric naturality after passing to residue homology

Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: lem-sc-picard-residue-homology-geometric-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 600000 in
-- The two auxiliary comparisons require additional elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The residue homology quotients of strictly perfect direct-image models identify
with geometric fibre cohomology, compatibly with the induced homology maps.
Source: Stacks Project, Tags 0B91, 0BF2 and 01XK; steps 1, 2 and 4 of
`lem-sc-picard-residue-cycles-geometric-naturality`.
(blueprint: lem-sc-picard-residue-homology-geometric-naturality)

Proof: Apply the coefficient pullback adjunction unit to ui, and derive the
resulting direct-image arrow. Restrict to U and conjugate by hE and hCi to
obtain a. Evaluate the strictly perfect models on the affine open. Their terms
are finite projective: the finite free retractions in strict perfectness remain
retractions after affine sections. The bounded complexes are consequently
K-flat, so termwise residue extension computes their derived pullbacks.
The explicit quotient affineResidueCycleHomology is their degree-one homology.
The equality hp and evaluation A -> kappa(w) identify kappa(p) with kappa(w);
since k is an
immersion, kappa(w) is canonically kappa(s). Apply arbitrary derived base change
for the relatively flat invertible coefficient and affine-base cohomology to
identify source and target homology with fibre coefficient cohomology. Use tau
on the source and its pullbacks along ui_s on the targets. These give additive
equivalences eK and eC with structure-sheaf cohomology.
For every chain representative phi of a, functoriality of derived residue
pullback identifies its induced homology map with that of a. The comparison
with termwise residue tensor is natural on K-flat complexes. Naturality of
base change, coefficient pullback, and affine cohomology then gives the equality
for every homology class z and every representative of a. No assertion that
all representatives are chain homotopic is needed. Nonzero source boundaries
are killed before this comparison;
when n=0 the target family and its equations are empty. No witness of mere
existence is used to define a coefficient or a complex. -/
theorem picard_residue_homology_geometric_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z) := by
  classical
  obtain ⟨eK, eC, _⟩ :=
    picard_residue_homology_geometric_comparison f Xi fi ui hui L W k w s hw τ U hwU hU p hp K
      hK hE C hC hCi
  obtain ⟨a, ha⟩ :=
    picard_residue_homology_geometric_naturality_fixed f Xi fi ui hui L W k w s hw τ U hwU hU p hp K
      hK hE C hC hCi eK eC
  exact ⟨eK, eC, a, ha⟩

end AlgebraicGeometry.Scheme
