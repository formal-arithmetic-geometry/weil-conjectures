/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.TraceFormula.MultipointedCurve
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import Sheaf.TraceFormula.PureRelativeDimensionFiniteStage
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.TraceFormula.StableModificationConstructibility
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.TraceFormula.StableModificationStabilityFieldDescent

/-!
# Normal finite-type models of finite semistable modification diagrams

Source: Temkin, *Stable modification of relative curves*, §3.1, Remark 3.1.1(ii),
Lemma 5.1(ii), and the first paragraph of the proof of Theorem 1.2 (printed p. 35),
with the normal finite-type refinement from Proposition 3.5.2
(blueprint: lem-trf-stable-curve-diagram-noetherian-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite diagram of semistable marked modifications admits a normal affine
finite-type model over the integers.
Source: Temkin, *Stable modification of relative curves*, §3.1, Remark 3.1.1(ii),
Lemma 5.1(ii), and the first paragraph of the proof of Theorem 1.2, with the
normal refinement of Proposition 3.5.2
(blueprint: lem-trf-stable-curve-diagram-noetherian-model).

Proof plan, following all nine steps of the DAG node:
1. Write S = Spec A. Approximate A by its finitely generated integer subalgebras,
   using lemma-nagata-noetherian-inverse-system-affine. They are domains, so every
   stage is integral and each projection preserves the generic point. The stages
   are Noetherian by lem-weil-pbc-finite-type-over-noetherian.
2. Apply thm-pd-spreading-out and lem-weil-pbc-finite-diagram-lift-of-models to
   descend all curve and marking objects, their structure and inclusion maps,
   all pair maps and all compatibility equations at one common stage.
3. Enlarge the stage by lem-weil-pbc-descend-flat-finite-presentation,
   lem-weil-pbc-descend-closed-immersion, lem-weil-pbc-eventually-proper, and
   lem-trf-pure-relative-dimension-finite-stage. The structure maps become flat
   and finitely presented with the stated pure dimensions, the marking maps
   closed immersions, and the pair maps proper. The cited permanence lemmas
   retain these properties at subsequent stages.
4. The fraction fields of the subalgebras have union Frac A. Descend the generic
   inverses and their inverse equations by thm-pd-spreading-out. Descend generic
   smoothness and etaleness along the faithfully flat field extension, using
   lem-trf-smooth-fpqc-base-descent and lem-galois-fpqc-descend-etale.
5. Approximate the stage fraction field by principal localizations. Descend all
   generic inverses and their equations once more, obtaining one principal open
   on which all pair maps are isomorphisms. Flatness over a domain makes the
   restriction maps on affine charts injective: a section killed by localization
   is killed by a power of a nonzero base element and is zero by
   lem-sc-flat-invertible-sections-torsion-free. Hence the opens on both parts
   are schematically dense, giving eta-modifications.
6. Use lem-trf-stable-modification-constructibility to form the finite intersection
   of the constructible semistable loci and the selected stable loci. Field
   descent of stability puts the image of S in this intersection, and
   lem-weil-pbc-limit-contained-in-constructible makes an entire later stage lie
   in it. Preserve these properties by lem-trf-semistable-marked-base-change.
7. Apply lem-sbc-normal-finite-stage-universal. The normal integral finite
   replacement of this affine stage is affine and finite type over the integers.
   Both dominant maps preserve generic points. Pull back the complete diagram
   and the principal open, retaining the multipointed structures, generic
   smoothness and etaleness, semistability, selected stability, and properness.
8. Every generic curve is smooth and every generic marking etale, hence reduced
   by sbc-lem-smooth-geometrically-reduced and
   lem-weil-pbc-etale-smooth-zero-dimensional-fibres. On each flat affine chart
   a nilpotent vanishes generically, so a nonzero base scalar kills it. The
   torsion-free sections lemma makes it zero. Thus all total spaces are reduced.
9. The defining base element of the common principal open stays nonzero under
   the dominant normal refinement. The same flat-localization argument gives
   schematic density on both parts. The proper pair maps are eta-modifications,
   and the common open is dense. Fibre-product associativity gives all diagram
   comparison isomorphisms and their compatibility equations. -/
theorem exists_normal_affine_finite_type_model_of_stable_curve_diagram
    (S : Scheme.{u}) [IsIntegral S] [IsAffine S]
    (hnormal : ∀ x : S,
      IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))
    (C : MultipointedCurve S)
    (hCη : Smooth (C.x.fiberToSpecResidueField (genericPoint S)))
    (hDη : Etale (C.d.fiberToSpecResidueField (genericPoint S)))
    (J : Type u) [Finite J]
    (Cj : J → MultipointedCurve S)
    (f : ∀ j : J, (Cj j).Hom C)
    (hf : ∀ j : J, (f j).IsEtaModification (S.fromSpecResidueField (genericPoint S)))
    (hsemi : ∀ j : J, (Cj j).IsSemistable)
    (Jst : Set J)
    (hstable : ∀ j : J, j ∈ Jst → (f j).IsStable (S.fromSpecResidueField (genericPoint S))) :
    ∃ (S₀ : Scheme.{u}) (η₀ : S₀),
      IsIntegral S₀ ∧ IsAffine S₀ ∧
      (∀ x : S₀, IsDomain (S₀.presheaf.stalk x) ∧
        IsIntegrallyClosed (S₀.presheaf.stalk x)) ∧
      IsGenericPoint η₀ (Set.univ : Set S₀) ∧
      ∃ (t₀ : S₀ ⟶ Spec (.of (ULift.{u} ℤ))),
        LocallyOfFiniteType t₀ ∧ QuasiCompact t₀ ∧
        ∃ (s : S ⟶ S₀),
          IsDominant s ∧ s (genericPoint S) = η₀ ∧
          ∃ (C₀ : MultipointedCurve S₀),
            Smooth (C₀.x.fiberToSpecResidueField η₀) ∧
            Etale (C₀.d.fiberToSpecResidueField η₀) ∧
            ∃ (Cj₀ : J → MultipointedCurve S₀),
              ∃ (f₀ : ∀ j : J, (Cj₀ j).Hom C₀),
              (∀ j : J, (f₀ j).IsEtaModification (S₀.fromSpecResidueField η₀)) ∧
              (∀ j : J, (Cj₀ j).IsSemistable) ∧
              (∀ j : J, j ∈ Jst → (f₀ j).IsStable (S₀.fromSpecResidueField η₀)) ∧
              ∃ (eC : C.X ≅ pullback C₀.x s)
                (eD : C.D ≅ pullback C₀.d s),
                eC.hom ≫ pullback.snd C₀.x s = C.x ∧
                eD.hom ≫ pullback.snd C₀.d s = C.d ∧
                eD.hom ≫ pullback.fst C₀.d s ≫ C₀.i =
                  C.i ≫ eC.hom ≫ pullback.fst C₀.x s ∧
                (∀ j : J,
                  ∃ (eCj : (Cj j).X ≅ pullback (Cj₀ j).x s)
                    (eDj : (Cj j).D ≅ pullback (Cj₀ j).d s),
                    eCj.hom ≫ pullback.snd (Cj₀ j).x s = (Cj j).x ∧
                    eDj.hom ≫ pullback.snd (Cj₀ j).d s = (Cj j).d ∧
                    eDj.hom ≫ pullback.fst (Cj₀ j).d s ≫ (Cj₀ j).i =
                      (Cj j).i ≫ eCj.hom ≫ pullback.fst (Cj₀ j).x s ∧
                    eCj.hom ≫ (f₀ j).curveBaseChange s =
                      (f j).curve ≫ eC.hom ∧
                    eDj.hom ≫ (f₀ j).markingBaseChange s =
                      (f j).marking ≫ eD.hom) ∧
                ∃ U₀ : S₀.Opens,
                  Dense (U₀ : Set S₀) ∧
                  (∀ j : J,
                    IsIso (pullback.snd (f₀ j).curve (C₀.x ⁻¹ᵁ U₀).ι) ∧
                    IsIso (pullback.snd (f₀ j).marking (C₀.d ⁻¹ᵁ U₀).ι)) ∧
                  IsReduced C₀.X ∧ IsReduced C₀.D ∧
                  (∀ j : J, IsReduced (Cj₀ j).X ∧ IsReduced (Cj₀ j).D) := by
  sorry

end AlgebraicGeometry
