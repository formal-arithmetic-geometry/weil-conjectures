/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmpleCurveTwoSectionPencil
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.AlgebraicGeometry.NonzeroDifferentialGenericallyEtale
import WeilConjectures.AlgebraicGeometry.Curve.UniformizerDifferentialBasis
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.Mathlib.GroupTheory.CosetCover
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.SectionBoundaryExact
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms
import WeilConjectures.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing
import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.GroupTheory.CosetCover
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # A nonempty open of separating pairs of norm sections

Source: de Jong, Families of curves and alterations (1997), §3.4(c), p.606,
norm-section replacement on the original smooth curve; Stacks, Tags 02O1 and 0C1C.
(blueprint: lem-sfb-separating-pair-open)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry
open Scheme.Modules

/-- Canonical base change of the already defined translated tensor. Its factors are
identified by the commuting action squares and the section-normalized pullback comparisons.
Source: de Jong §3.4(c), norm-section parameter space; Stacks, Tag 01CD.
(blueprint: lem-sfb-separating-pair-open) -/
noncomputable def normPencilTranslateBaseChangeIso {X Y : Scheme.{u}} {G : Type v}
    (f : Y ⟶ X) (α : G → Aut X) (β : G → Aut Y)
    (w : ∀ g : G, (β g).hom ≫ f = f ≫ (α g).hom) (L : X.Modules) :
    ∀ l : List G, (tensorPullback f).obj (pencilTranslateTensor α L l) ≅
      pencilTranslateTensor β ((tensorPullback f).obj L) l
  | [] => (boundaryPullbackComparison f).app _ ≪≫ pullbackObjUnitIso f
  | g :: l =>
      boundaryPullbackTensorIso f ((tensorPullback (α g).hom).obj L)
        (pencilTranslateTensor α L l) ≪≫
      ((((tensorPullbackSectionComp f (α g).hom).app L).symm ≪≫
        eqToIso (congrArg (fun q ↦ (tensorPullback q).obj L) (w g).symm) ≪≫
        (tensorPullbackSectionComp (β g).hom f).app L) ⊗ᵢ
          normPencilTranslateBaseChangeIso f α β w L l)

/-- Specialize a pair of section-coordinate vectors at a field-valued parameter point.
The pullback-power comparison takes the resulting section to `L_E` raised to power `n`.
Source: de Jong §3.4(c), norm-section parameter space; Stacks, Tag 02KH.
(blueprint: lem-sfb-separating-pair-open) -/
noncomputable def normPencilCoordinateSection
    {F E : Type u} [Field F] [Field E] {C Y : Scheme.{u}}
    (π : Y ⟶ C) (p : Y ⟶ Spec (.of E)) (L : C.Modules) (n : ℕ)
    {I : Type u} [Fintype I] (b : I → Γ(L.tensorPow n, ⊤))
    (z : Spec (.of E) ⟶ 𝔸(I × ULift.{u} (Fin 2); Spec (.of F)))
    (j : ULift.{u} (Fin 2)) : Γ(((Scheme.Modules.tensorPullback π).obj L).tensorPow n, ⊤) :=
  (boundaryPullbackPowIso π L n).hom.app ⊤
    (∑ i : I, p.appTop (z.appTop (AffineSpace.coord (Spec (.of F)) (i, j))) •
      (((tensorPullback π).obj (L.tensorPow n)).presheaf.map
        (homOfLE (Scheme.Hom.preimage_top π).ge).op
        (((tensorPullbackSectionAdjunction π).unit.app (L.tensorPow n)).app ⊤ (b i))))

/-- The base-changed pair of norm sections, in the tensor power of the pullback of
`B = ⊗ g^*L`. The norm is formed with the base-changed action, then transported through
the canonical base-change comparison, not through an arbitrary module isomorphism.
Source: de Jong §3.4(c), norm-section replacement; Stacks, Tags 01CD, 01CT.
(blueprint: lem-sfb-separating-pair-open) -/
noncomputable def normPencilSections
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F))
    {G : Type v} [Group G] [Fintype G] (ρ : G →* Aut (Over.mk f))
    (L : C.Modules) (n : ℕ) {I : Type u} [Fintype I]
    (b : I → Γ(L.tensorPow n, ⊤))
    (z : Spec (.of E) ⟶ 𝔸(I × ULift.{u} (Fin 2); Spec (.of F))) :
    ULift.{u} (Fin 2) →
      (((Scheme.Modules.tensorPullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F E))))).obj
          (pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L)).tensorPow n).sections :=
  fun j ↦
    SheafOfModules.sectionsMap
      ((boundaryTensorPowIso (normPencilTranslateBaseChangeIso
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F E))))
        (fun g ↦ (Over.forget _).mapIso (ρ g))
        (fun g ↦ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⋙
          Over.forget _).mapIso (ρ g))
        (fun g ↦ (baseChange_morphism_projections (ρ g).hom
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))))).1)
        L (pencilGroupElements G)).symm n).hom)
      (pencilNormSection
        (fun g ↦ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⋙
          Over.forget _).mapIso (ρ g))
        ((tensorPullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F E))))).obj L) n
        (SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
          (normPencilCoordinateSection
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F E))))
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F E)))) L n b z j))))

/-- For all sufficiently large powers of an ample invertible module, a nonempty Zariski
open of pairs of sections gives finite surjective invariant pencils that are etale on
nonempty opens, over every extension field. Nonempty refers to the parameter scheme.
Source: de Jong §3.4(c), p.606, norm-section replacement; Stacks, Tags 02O1 and 0C1C.
(blueprint: lem-sfb-separating-pair-open).

Proof:
1. Pass to an algebraic closure. Projectivity gives properness, finite type gives
Noetherianity, and ampleness survives base change (lem-pc-projective-proper,
lem-trf-scheme-relative-ample-base-change, lem-weil-pbc-finite-type-over-noetherian).
2. Faithfulness survives field extension: field extension is faithfully flat, so equality
of morphisms descends by the affine-chart tensor-injectivity argument.
3. Use the faithful function-field action to find a free geometric orbit, and choose a
rational point in its nonempty affine open by the Nullstellensatz
(lem-sfb-proper-curve-function-field-morphisms, lem-wf-affine-nullstellensatz-vanishing).
4. Fix the union of the first infinitesimal neighbourhoods of this orbit. Serre vanishing
and eventual global generation give one bound n0 for its ideal and all subsequent n
(lem-sc-smooth-connected-curve-local-rings, lem-weil-pbc-coherent-serre-vanishing,
lem-weil-pbc-coherent-twist-global-generation).
5. The section boundary sequence lifts jets: choose a section a with one simple zero on
the orbit and value one at all other orbit points (lem-sc-module-section-boundary-exact).
6. Its orbit zero set S is finite, by the integral-curve dimension bound and Noetherianity.
Finite-dimensional sections and global generation make evaluation kernels proper
(lem-pc-zero-scheme-properties, lem-sc-zero-dim-noetherian-closed-finite,
lem-pc-coherent-hi, lem-wf-affine-nullstellensatz-vanishing).
7. Finite linear avoidance gives b nonzero on S. The norms have disjoint zeros and generate
(lem-pc-finite-linear-avoidance, lem-weil-pbc-invertible-generating-sections-fibre).
8. Only one factor of the first norm has a simple zero at the chosen orbit point; the
second norm is a unit there. The ratio has nonzero differential, with no division by |G|
(lem-a1-uniformizer-differential-basis).
9. Proper coherent cohomology and flat base change give finite-dimensional section spaces
and their field-extension identifications. Tensoring universal coordinate sections makes
the universal norms polynomial (lem-pc-coherent-hi, lem-sc-flat-base-change-coherent).
10. Remove the proper image of the common zero locus. This is the open generating locus,
including at nonclosed parameter points (lem-weil-pbc-proper-base-change,
pqf-lem-proper-closed-map, lem-weil-pbc-invertible-generating-sections-fibre).
11. In local frames the expression (beta d alpha - alpha d beta)e^2 is frame independent.
It gives a polynomial map to the finite-dimensional space of sections of omega tensor M^2
(lem-sc-smooth-omega-finite-locally-free, lem-pc-coherent-hi).
12. Kahler and coherent-cohomology base change identify this differential section after
all extensions (lem-weil-pbc-kahler-differentials-base-change,
lem-sc-flat-base-change-coherent).
13. Intersect the generating locus with the complement of its polynomial zero locus.
The geometric pair constructed above witnesses nonemptiness over F.
14. The projective line is a smooth integral curve by its standard polynomial charts
(lem-pc-projective-space-canonical, sbc-lem-affine-space-smooth,
lem-weil-pbc-smooth-local-on-source, lemma-nagata-projective-space-base-change-proper).
15. On each generating chart the differential of the ratio is the alternating differential
divided by the square of the denominator. Its nonvanishing gives a nonempty etale open
(lem-a1-nonzero-differential-generically-etale).
16. Over an algebraic closure the ratio is nonconstant, hence its morphism to the
projective line is finite and surjective. Descend finiteness faithfully flatly and lift
points to descend surjectivity (lem-sc-rational-function-morphism,
lem-sc-morphism-from-function, lem-sbc-finite-morphism-fpqc-descent).
17. Translating permutes the tensor factors. Both norms transform by the same canonical
comparison, so the projective-space functor of points gives invariance
(def-weil-pbc-morphism-to-projective-space-by-sections).
-/
theorem exists_nonempty_separating_pair_open
    {F : Type u} [Field F] (C : Scheme.{u}) [C.Over (Spec (.of F))]
    [Smooth (C ↘ Spec (.of F))] [IsHProjective (C ↘ Spec (.of F))]
    [LocallyOfFiniteType (C ↘ Spec (.of F))] [QuasiCompact (C ↘ Spec (.of F))]
    [GeometricallyIntegral (C ↘ Spec (.of F))] [IsIntegral C]
    (hdim : topologicalKrullDim C = 1)
    (G : Type v) [Group G] [Fintype G]
    (ρ : G →* Aut (Over.mk (C ↘ Spec (.of F)))) (hρ : Function.Injective ρ)
    (L : C.Modules) [L.IsInvertible] (hL : IsAmple C L) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      FiniteDimensional F ((L.tensorPow n).H 0) ∧
      ∀ (I : Type u) [Fintype I] (b : Module.Basis I F ((L.tensorPow n).H 0)),
        ∃ W : (𝔸(I × ULift.{u} (Fin 2); Spec (.of F))).Opens,
          (W : Set (𝔸(I × ULift.{u} (Fin 2); Spec (.of F)))).Nonempty ∧
          ∀ (E : Type u) [Field E] [Algebra F E]
            (z : Spec (.of E) ⟶ 𝔸(I × ULift.{u} (Fin 2); Spec (.of F))),
            z ≫ 𝔸(I × ULift.{u} (Fin 2); Spec (.of F)) ↘ Spec (.of F) =
              Spec.map (CommRingCat.ofHom (algebraMap F E)) →
            Set.range z ⊆ W →
            ∃ hB : (((Scheme.Modules.tensorPullback
                (pullback.fst (C ↘ Spec (.of F))
                  (Spec.map (CommRingCat.ofHom (algebraMap F E))))).obj
                (pencilOrbitBundle (fun g ↦ (Over.forget _).mapIso (ρ g)) L)).tensorPow
                  n).IsInvertible,
            ∃ hs : Epi ((SheafOfModules.freeHomEquiv _).symm
              (normPencilSections (C ↘ Spec (.of F)) ρ L n
                (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z)),
            IsFinite (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
              (pullback.snd (C ↘ Spec (.of F))
                (Spec.map (CommRingCat.ofHom (algebraMap F E)))) _
              (normPencilSections (C ↘ Spec (.of F)) ρ L n
                (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z) hs) ∧
            Surjective (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
              (pullback.snd (C ↘ Spec (.of F))
                (Spec.map (CommRingCat.ofHom (algebraMap F E)))) _
              (normPencilSections (C ↘ Spec (.of F)) ρ L n
                (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z) hs) ∧
            (∀ g : G,
              ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).map
                (ρ g).hom).left ≫
                ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
                  (pullback.snd (C ↘ Spec (.of F))
                    (Spec.map (CommRingCat.ofHom (algebraMap F E)))) _
                  (normPencilSections (C ↘ Spec (.of F)) ρ L n
                    (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z) hs =
                ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
                  (pullback.snd (C ↘ Spec (.of F))
                    (Spec.map (CommRingCat.ofHom (algebraMap F E)))) _
                  (normPencilSections (C ↘ Spec (.of F)) ρ L n
                    (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z) hs) ∧
            ∃ U : (pullback (C ↘ Spec (.of F))
                (Spec.map (CommRingCat.ofHom (algebraMap F E)))).Opens,
              Nonempty U ∧
              Etale (U.ι ≫ ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin 2))
                (pullback.snd (C ↘ Spec (.of F))
                  (Spec.map (CommRingCat.ofHom (algebraMap F E)))) _
                (normPencilSections (C ↘ Spec (.of F)) ρ L n
                  (fun i ↦ H.zeroLinearEquiv (L.tensorPow n) (b i)) z) hs) := by
  sorry

end AlgebraicGeometry
