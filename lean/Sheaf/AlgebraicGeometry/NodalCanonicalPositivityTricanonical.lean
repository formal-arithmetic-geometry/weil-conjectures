/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry

/-! # Canonical positivity and the tricanonical embedding of a nodal curve

Source: Stacks Project, curves.tex, Tag 0E8X (lemma-tricanonical), and moduli-curves.tex,
Tag 0E74 (lemma-stable); component interpretation in curves.tex, Tags 0E63, 0E64 and 0E3P
(blueprint: lem-sfb-nodal-canonical-positivity-tricanonical).

A basis of the entire space of sections identifies the quotient projective bundle
P(H^0(C, omega^3)) with coordinate projective space. The morphism in the conclusion is
explicitly the morphism of those generating sections, not an arbitrary closed immersion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The dualizing line is ample exactly when rational normalized components have at least
three ambient nodal branches and genus-one normalized components have at least one.
Under these conditions its third tensor power has vanishing H^1 and embeds the curve by
its complete linear system, with the indicated pullback of the tautological quotient line.

Source: Stacks Project, curves.tex, Tags 0E8X, 0E63, 0E64 and 0E3P; moduli-curves.tex,
Tag 0E74 (blueprint: lem-sfb-nodal-canonical-positivity-tricanonical).

Proof plan, following the three steps of the node:
1. Properness gives separatedness and finite type (def-weil-proper-morphism).
   Finite type over the Noetherian field gives finite presentation, by
   lem-weil-pbc-finite-type-noetherian-finite-presentation; every field module is flat.
   Apply lem-sfb-gorenstein-curve-relative-dualizing to obtain its Serre-duality line.
   The supplied natural representing bijections identify omega with this line by Yoneda:
   the maps corresponding to the two identity maps are mutually inverse by naturality.
   Lem-sfb-proper-nodal-dualizing-base-change identifies its pullback to each normalized
   component V with the canonical line of V twisted by the ambient nodal branches.
   Thus deg(nu^*omega) = 2g(V)-2+b(V), counting both branches of each self-node.
2. Lem-trf-fibre-degree-ample-criterion applies to this proper reduced pure curve.
   Ampleness is equivalent to positivity of every normalized component degree.
   Substitution gives b>=3 in genus zero and b>=1 in genus one; in genus at least two
   positivity is automatic. This proves both directions of the equivalence.
3. Apply lem-sfb-stable-pointed-field-linear-series with no markings, D=0 and m=3.
   Its component positivity is exactly step 2. It gives H^1(omega^3)=0, global generation,
   and the complete-linear-system closed immersion. A basis of all global sections
   identifies its target with coordinate projective space. By
   lem-trf-projective-bundle-quotient-geometry this is the evaluation quotient morphism,
   and the tautological quotient line pulls back to omega^3.
-/
theorem nodal_canonical_positivity_tricanonical
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (C : Scheme.{u}) [C.Over (Spec (.of Ω))]
    [IsProper (C ↘ Spec (.of Ω))] [ConnectedSpace C] [IsReduced C]
    (hpure : C.IsPureDimension 1)
    (hnodal : ∀ x : C, x ∉ (C ↘ Spec (.of Ω)).smoothLocus →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    (hgenus : 2 ≤ Module.finrank Ω
      (Scheme.Modules.scalarCohomology (C ↘ Spec (.of Ω))
        (SheafOfModules.unit C.ringCatSheaf) 1))
    (omega : C.Modules) [omega.IsInvertible]
    (duality : ∀ (F : C.Modules), F.IsQuasicoherent →
      (F ⟶ omega) ≃
        (Scheme.Modules.scalarCohomology (C ↘ Spec (.of Ω)) F 1 ⟶ ModuleCat.of Ω Ω))
    (hnatural : ∀ (F G : C.Modules) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent)
      (a : F ⟶ G) (t : G ⟶ omega)
      (z : Scheme.Modules.scalarCohomology (C ↘ Spec (.of Ω)) F 1),
      duality F hF (a ≫ t) z = duality G hG t
        (((RingedSpace.moduleCohomology C.toRingedSpace 1).map a) z)) :
    (Scheme.Modules.IsAmple C omega ↔
      ∀ Z : irreducibleComponents C,
        (Module.finrank Ω
          (Scheme.Modules.scalarCohomology (C.normalizedComponentMap Z ≫ C ↘ Spec (.of Ω))
            (SheafOfModules.unit (C.reducedNormalizationComponent Z).normalization.ringCatSheaf)
            1) = 0 →
          3 ≤ (C.normalizedComponentMap Z ⁻¹'
            {x | x ∉ (C ↘ Spec (.of Ω)).smoothLocus}).encard) ∧
        (Module.finrank Ω
          (Scheme.Modules.scalarCohomology (C.normalizedComponentMap Z ≫ C ↘ Spec (.of Ω))
            (SheafOfModules.unit (C.reducedNormalizationComponent Z).normalization.ringCatSheaf)
            1) = 1 →
          1 ≤ (C.normalizedComponentMap Z ⁻¹'
            {x | x ∉ (C ↘ Spec (.of Ω)).smoothLocus}).encard)) ∧
    (Scheme.Modules.IsAmple C omega →
      Subsingleton (Scheme.Modules.scalarCohomology (C ↘ Spec (.of Ω))
        (omega.tensorPow 3) 1) ∧
      ∃ (I : Type u) (_ : Finite I)
        (b : Module.Basis I Ω ((ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom Ω (X := C))).obj
            ((omega.tensorPow 3).val.obj (Opposite.op ⊤))))
        (s : I → (omega.tensorPow 3).sections),
        (∀ i : I, (s i).val (Opposite.op ⊤) = b i) ∧
        ∃ hs : Epi ((omega.tensorPow 3).freeHomEquiv.symm s),
          IsClosedImmersion (ProjectiveSpace.homOfGeneratingSections I
            (C ↘ Spec (.of Ω)) (omega.tensorPow 3) s hs) ∧
          Nonempty ((Scheme.Modules.tensorPullback
            (ProjectiveSpace.homOfGeneratingSections I (C ↘ Spec (.of Ω))
              (omega.tensorPow 3) s hs)).obj
                (ProjectiveSpace.twist I (Spec (.of Ω)) 1) ≅ omega.tensorPow 3)) := by
  sorry

end AlgebraicGeometry
