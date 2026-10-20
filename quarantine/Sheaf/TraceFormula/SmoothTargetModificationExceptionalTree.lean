/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.TraceFormula.Modification
public import Sheaf.TraceFormula.ProjectiveLineTree
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.TraceFormula.GenusZeroSmoothProperLine
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
import Sheaf.RingTheory.ProjectiveOverLocalFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.NodalContractionEulerDefect
import Sheaf.AlgebraicGeometry.ProperNormalGeometricConnectedness
import Sheaf.TraceFormula.ValuationModificationProperCompletion

/-! # Exceptional fibres of modifications over smooth points

Source: Temkin, *Stable modification of relative curves*, Lemma 4.4.2,
printed pp. 30–31, and Appendix B, pp. 57–58
(blueprint: lem-trf-smooth-target-modification-exceptional-tree).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A positive-dimensional modification fibre over a smooth point of a relative curve
is a projective-line tree, whose boundary in the original geometric source fibre
has at most two points. The reduced fibre is the actual nilradical subscheme, and
`pullback.mapDesc` puts it in the fibre over the composite geometric base point.
The hypotheses allow empty or disconnected other fibres, arbitrary characteristic,
and nonseparated curves over the valuation base.

Source: Temkin, Lemma 4.4.2 and Appendix B, printed pp. 30–31 and 57–58
(blueprint: lem-trf-smooth-target-modification-exceptional-tree).

Proof plan, following all eight steps of the node:
1. Flatness makes sections of the structure line torsion-free over the valuation
   domain (lem-sc-flat-invertible-sections-torsion-free). They inject into their
   generic localization, which is reduced by smoothness. Thus Z is reduced.
   Apply lem-trf-valuation-modification-proper-completion near x. It provides
   proper flat finitely presented integral auxiliary curves over a localization
   of V, a normal target, identified geometrically integral generic fibres, and
   the unchanged exceptional fibre and ambient neighbourhood.
2. Apply lem-trf-proper-normal-geometric-connectedness to the auxiliary modification:
   its generic fibre is a point with the target function field, so the exceptional
   fibre is nonempty and connected. The localized valuation ring is integrally
   closed. Apply the same lemma to the proper source curve, using
   lem-pc-h0-proper-variety for its generic global functions. The auxiliary geometric
   source D and its surjective image C are connected.
3. Finite type over the geometric field gives Noetherianity. The closed exceptional
   fibre B is a finite union of whole curve components and possibly isolated points;
   connectedness excludes the latter. It is pure one-dimensional, nodal by the local
   branch model, and proper as a closed subcurve of D. Write v for its components,
   e for its internal nodes, and r for its boundary points. The complement is nonempty;
   connectedness of D implies r is at least one.
4. Apply lem-pc-rf-perfect-base-change to the structure sheaves of both proper flat
   auxiliary curves. The perfect complexes are represented over the local base by
   bounded finite projective modules, free by lem-trf-projective-over-local-free.
   After any field base change the Euler characteristic is the alternating sum of
   their integer ranks. The identified generic fibres therefore give chi(D) = chi(C).
5. Apply lem-trf-nodal-contraction-euler-defect. If g_i are the nonnegative genera
   of the component normalizations, its equality becomes
   0 = (r - 1) + (e - v + 1) + sum_i g_i.
6. Connectedness of B makes its dual multigraph connected. Construct a spanning tree
   by adjoining edges to new vertices. It has v - 1 edges, so e - v + 1 is nonnegative.
   The equality forces r = 1, e = v - 1, and all g_i = 0. Every edge is in that tree,
   excluding self-loops and multiple-edge cycles.
7. Lem-trf-genus-zero-smooth-proper-line identifies every normalized component with P1.
   Lem-trf-nodal-normalization-adjunction, applied in the original source fibre,
   says component singularities are self-nodes. The tree has none, so the component
   normalization is an isomorphism: the components themselves are P1 over the field.
8. The boundary is detected locally by one branch in B and one outside B at a node.
   The preserved ambient neighbourhood identifies these points with the r = 1
   auxiliary boundary points. Hence its cardinality is at most two. Together with
   the previous steps this gives every projective-line-tree clause asserted here.
-/
theorem smoothTargetModificationExceptionalTree
    (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    {Z W : Scheme.{u}} (w : W ⟶ Spec (.of V))
    [Flat w] [LocallyOfFinitePresentation w] [QuasiCompact w] [QuasiSeparated w]
    (hWdim : ∀ t : Spec (.of V), (w.fiber t).IsPureDimension 1)
    [Smooth (pullback.snd w (Spec.map (CommRingCat.ofHom V.subtype)))]
    (f : Z ⟶ W)
    (hf : EtaModification (Spec.map (CommRingCat.ofHom V.subtype)) f w)
    [Flat (f ≫ w)] [LocallyOfFinitePresentation (f ≫ w)]
    [QuasiCompact (f ≫ w)] [QuasiSeparated (f ≫ w)]
    (hZdim : ∀ t : Spec (.of V), ((f ≫ w).fiber t).IsPureDimension 1)
    (hnodal : ∀ (Ξ : Type u) [Field Ξ] [IsAlgClosed Ξ]
      (s : Spec (.of Ξ) ⟶ Spec (.of V)),
      ∀ z : (pullback (C := Scheme.{u}) (f ≫ w) s),
        (∃ U : (pullback (f ≫ w) s).Opens,
          z ∈ U ∧ Smooth (U.ι ≫ pullback.snd (f ≫ w) s)) ∨
        Orgogozo.IsOrdinaryDoublePoint (pullback.snd (f ≫ w) s) z)
    (x : W) (hx : ∃ U : W.Opens, x ∈ U ∧ Smooth (U.ι ≫ w))
    (hpositive : 0 < topologicalKrullDim (f.fiber x))
    (Ω : Type u) [Field Ω] [Algebra (W.residueField x) Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic (W.residueField x) Ω] :
    IsProjectiveLineTree
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫
          W.fromSpecResidueField x)).nilradical.subschemeι ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫
          W.fromSpecResidueField x)) ∧
    (Set.range
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫
            W.fromSpecResidueField x)).nilradical.subschemeι ≫
          pullback.mapDesc f
            (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫
              W.fromSpecResidueField x) w) ∩
      closure ((Set.range
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫
            W.fromSpecResidueField x)).nilradical.subschemeι ≫
          pullback.mapDesc f
            (Spec.map (CommRingCat.ofHom (algebraMap (W.residueField x) Ω)) ≫
              W.fromSpecResidueField x) w))ᶜ)).encard ≤ 2 := by
  sorry

end AlgebraicGeometry
