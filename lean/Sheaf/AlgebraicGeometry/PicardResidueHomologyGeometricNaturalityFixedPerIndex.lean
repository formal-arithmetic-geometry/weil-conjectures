/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
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

import Sheaf.AlgebraicGeometry.AffineResidueModelNaturality
import Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality

/-! Per-index component of positive-family geometric naturality.

Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: new-picard-residue-homology-geometric-naturality-fixed-per-index)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/- The former arbitrary-equivalence statement was false. For an identity map of
an elliptic curve over C, choose the source comparison to be linear and compose
the target comparison with conjugation. A representative would then have to
induce conjugation, although every residue chain map is C-linear. The corrected
quantifiers choose one geometric source comparison, then compatible target
comparisons for all indices. See the change record for the full counterexample. -/
set_option maxHeartbeats 1600000 in
-- The model comparisons elaborate several derived and section functors.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedVariables false in
/-- Choose a common source comparison and construct the naturality data per index.
Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: new-picard-residue-homology-geometric-naturality-fixed-per-index)

Proof: Write E for the derived direct image of the pulled-back invertible L on
X_W, and Ei for the corresponding objects on Xi_W. The coefficient pullback
adjunction units and composition of derived direct images give arrows E -> Ei.
Restrict them to U and conjugate by the supplied model isomorphisms hE and hCi.
This constructs the derived arrows a. Terminal sections of a strictly perfect
complex form a bounded complex of finite projective Gamma(W,U)-modules: sections
preserve the finite-free retractions and zero terms. These complexes are K-flat,
so their termwise residue tensors compute derived residue pullback. Their
first homology is the explicit quotient affineResidueCycleHomology. The equation
hp identifies the prime's residue field with kappa(w); the immersion k and hw
identify this field with kappa(s). The arbitrary base-change comparison of 0B91
and the affine-base cohomology comparison of 01XK identify the residue homology
with cohomology of the fibre coefficient. Apply tau on the source, and its
pullbacks on the targets, to obtain structure-sheaf cohomology. Use this SAME
source comparison for every index; the target comparisons come from the same
natural constructions. Naturality of the adjunction unit, base change and the
K-flat comparison gives the equation for the geometric derived arrow. Every
chain representative has this equation, because derived residue pullback
depends only on its image under Q. This argument includes nonzero boundaries,
nonfree finite projective terms and zero complexes. No arbitrary additive
comparison is prescribed. The empty family is handled by the caller. -/
theorem picard_residue_homology_geometric_naturality_fixed_positive_per_index
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
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (hn : 0 < n) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1),
      ∀ i : Fin n,
        ∃ (eCi : affineResidueCycleHomology W U p (C i) ≃+
            Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
          (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ (φ : K ⟶ C i), DerivedCategory.Q.map φ = a →
        ∀ z : affineResidueCycleHomology W U p K,
          eCi (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z) := by
  classical
  obtain ⟨eg, hg⟩ := picard_derived_fibre_naturality f Xi fi ui hui L W k w s hw τ
  obtain ⟨m⟩ := hE
  obtain ⟨er, hr⟩ := affine_residue_model_naturality W w U hwU hU p hp _ K hK m
  refine ⟨er.trans eg, ?_⟩
  intro i
  obtain ⟨egi, hb⟩ := hg i
  obtain ⟨mi⟩ := hCi i
  obtain ⟨eri, hi⟩ := hr _
    (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) (C i) (hC i) mi
  refine ⟨eri.trans egi,
    m.inv ≫ (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.map
        (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ mi.hom, ?_⟩
  intro φ hφ z
  exact (congrArg egi (hi φ hφ z)).trans (hb (er z))

end AlgebraicGeometry.Scheme
