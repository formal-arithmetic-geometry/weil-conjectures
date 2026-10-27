/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing
public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.RegularSequenceConormal
import Sheaf.AlgebraicGeometry.ProperFlatDualizingPolynomialModel
import Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison
import Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.NodalClosedPointsReduced
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType

/-! # Comparing the nodal dualizing and adjunction lines

Source: Stacks Project, duality.tex, Tags 0E2T--0E2Z and 0B6V;
moduli-curves.tex, Tag 0E6R. The comparison of the two normalized systems is
agent-formulated in the DAG (blueprint: lem-sfb-nodal-dualizing-adjunction-line-comparison).

The supplied systems retain their actual module pullbacks and base-change comparisons.
A cartesian change with an isomorphism on the total space and identity on the base
also represents an isomorphism of families, so one naturality equation covers both clauses.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- On a Noetherian nodal family the relative dualizing line and the normalized
adjunction line are isomorphic, compatibly with their specified comparisons.
The original family is indexed by `FlatLCIBaseChange.identity f`. Quantifying over
all cartesian models includes the chosen fibre product and every isomorphic family.
Only the new bases are required to be Noetherian; their maps need not be flat.
The comparison family has no presentation or chosen cover as an argument.

Source: Stacks Project, duality.tex, Tags 0E2T, 0E2W, 0E2X, 0E2Y, 0E2Z and 0B6V;
moduli-curves.tex, Tag 0E6R
(blueprint: lem-sfb-nodal-dualizing-adjunction-line-comparison).

Proof, following the six DAG steps:
1. On a regular presentation put c=n-1. RegularSequenceKoszulRegular and
   RegularSequenceConormal identify the conormal basis, including c=0.
   The nodal relative-dualizing theorem identifies f^! O with omega[1].
2. The proper-flat polynomial model identifies this object locally with
   RHom_P(B, Omega^n)[n], retaining the quotient action and ordered refinements.
   The inverse normalized top-Ext map of lem-trf-lci-adjunction-top-ext gives
   omega restricted to U isomorphic to the dual conormal wedge tensor the volume wedge.
3. The signed Koszul determinant comparison and adjunction-cotangent normalization
   give precisely the transitions of K. Glue the module maps and their inverses by
   glue_sheaves_of_modules. Refining or replacing presentations gives the same maps.
4. Properness, flatness and finite presentation survive base change. Fibre-dimension
   invariance, the nonzero field-extension argument and the nodal reducedness theorem
   preserve the fibre assumptions. Base-changed LCI equations are regular at the closed
   source; over a Noetherian base the principal-neighbourhood theorem supplies the
   required regular presentations. Thus every Noetherian base change is admissible.
5. The relative-duality polynomial base-change comparison is computed on the finite
   free Koszul resolution. KoszulBaseChangeIso carries each ordered wedge to its
   pulled-back wedge. On Hom the tensor map sends h tensor r to the functional
   z tensor s maps to rs(h(z) tensor 1). Its top-degree map has the same sign and
   dual-wedge normalization as both the local theta and the adjunction comparison.
   Hence the displayed square commutes locally on generators and therefore globally.
   Flatness of the original family suffices, including for nonflat base changes.
6. For an isomorphism of families, compose each presentation with that isomorphism.
   Polynomial-duality naturality and the presentation comparison for adjunction use
   the same transported equations and volume forms. The normalized top-Ext map is
   unchanged on these bases, giving clause (2). Together with steps 3 and 5 this
   proves presentation independence and both requested comparison compatibilities.
-/
theorem exists_nodalDualizingAdjunctionLineComparison
    {X T : Scheme.{u}} (f : X ⟶ T) [IsNoetherian T]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      Nonempty ↥(pullback f t) ∧ IsReduced (pullback f t) ∧
        (pullback f t).IsPureDimension 1 ∧
        ∀ x : ↥(pullback f t), IsClosed ({x} : Set ↥(pullback f t)) →
          x ∉ (pullback.snd f t).smoothLocus →
          Nonempty
            (AdicCompletion
              (IsLocalRing.maximalIdeal ((pullback f t).presheaf.stalk x))
              ((pullback f t).presheaf.stalk x) ≃+*
                (MvPowerSeries (Fin 2) Ω ⧸
                  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    (hlci : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (FlatLCIPresentation f 1 U))
    (W : NodalRelativeDualizingSystem.{u, w} f)
    (K : FlatLCIAdjunctionSystem f 1) (hK : K.IsNormalized) :
    ∃ θ : ∀ (B : FlatLCIBaseChange f), IsNoetherian B.S' → (W.omega B ≅ K.line B),
      ∀ (B D : FlatLCIBaseChange f) (hB : IsNoetherian B.S') (hD : IsNoetherian D.S')
        (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
        (hc : IsPullback g D.p' B.p' b) (hg : g ≫ B.g = D.g) (hb : b ≫ B.b = D.b),
        (Scheme.Modules.tensorPullback g).map (θ B hB).hom ≫
            (K.baseChange B D g b hc hg hb).hom =
          (W.baseChange B D g b hc hg hb).hom ≫ (θ D hD).hom := by
  sorry

end AlgebraicGeometry
