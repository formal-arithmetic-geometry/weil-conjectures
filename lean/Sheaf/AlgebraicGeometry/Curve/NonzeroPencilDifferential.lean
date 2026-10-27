module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.NonzeroDifferentialGenericallyEtale
import Sheaf.AlgebraicGeometry.Curve.SmoothCotangentGenericIsomorphism
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.Curve.ProperFunctionFieldMorphisms
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# A nonzero pencil differential

Source: Stacks Project, curves.tex, Tags 0C1C, 0BY1 and 0CCL;
constructions.tex, Tags 01NE and 01NG; descent.tex, Tag 02LA.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale)

The alternating section is specified by its formula in every local frame. Its unique
existence is part of the statement. The geometric map is likewise specified by the
universal property of projective-space base change, with no arbitrary chosen morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The local-frame characterization of the section `(t ds - s dt)` of `Ω ⊗ M ⊗ M`.
Source: the frame calculation in the node, and Stacks, Tag 01UM.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale) -/
def pencilDifferentialFrameFormula {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) (M : C.Modules)
    (s : ULift.{u} (Fin 2) → M.sections)
    (δ : Γ(f.relativeDifferentials ⊗ (M ⊗ M), ⊤)) : Prop :=
  ∀ (U : C.Opens) (e : Γ(M, U)), IsFreeGenerator e →
    ∀ a b : Γ(C, U), (s ⟨0⟩).val (op U) = a • e →
      (s ⟨1⟩).val (op U) = b • e →
      (f.relativeDifferentials ⊗ (M ⊗ M)).presheaf.map (homOfLE le_top).op δ =
        tmulSection (M := f.relativeDifferentials) (N := M ⊗ M)
          (b • f.relativeDifferentialsDerivation.d a -
          a • f.relativeDifferentialsDerivation.d b) (tmulSection (M := M) (N := M) e e)

/-- Both chart formulas, with the numerator and denominator indexed in either order.
Source: Stacks, Tags 01NE and 01NG, and the quotient-rule calculation in the node.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale) -/
def pencilDifferentialChartFormula {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) (M : C.Modules)
    (s : ULift.{u} (Fin 2) → M.sections) (h : C ⟶ ProjectiveLine (Spec (.of F))) : Prop :=
  (∀ i : ULift.{u} (Fin 2),
    (h ⁻¹ᵁ ProjectiveSpace.standardOpen _ _ i : Set C) =
      nonvanishingLocus M ((s i).val (op ⊤))) ∧
  ∀ (U : C.Opens) (e : Γ(M, U)), IsFreeGenerator e →
    ∀ (i j : ULift.{u} (Fin 2)), i ≠ j →
      ∀ (a : Γ(C, U)) (b : Γ(C, U)ˣ),
        (s j).val (op U) = a • e → (s i).val (op U) = (b : Γ(C, U)) • e →
        ∃ hU : U ≤ h ⁻¹ᵁ ProjectiveSpace.standardOpen _ _ i,
          h.appLE _ U hU (ProjectiveSpace.coordRatio _ _ i j) = a * (↑(b⁻¹) : Γ(C, U)) ∧
          f.relativeDifferentialsDerivation.d (a * (↑(b⁻¹) : Γ(C, U))) =
            ((↑(b⁻¹) : Γ(C, U)) ^ 2) •
              ((b : Γ(C, U)) • f.relativeDifferentialsDerivation.d a -
                a • f.relativeDifferentialsDerivation.d (b : Γ(C, U)))

/-- Pull back a compatible global section using the normalized tensor adjunction.
Source: Stacks, Tags 0095 and 01NE.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale) -/
noncomputable def pencilPullbackSection {C D : Scheme.{u}} (a : D ⟶ C)
    (M : C.Modules) (s : M.sections) : ((tensorPullback a).obj M).sections :=
  SheafOfModules.unitHomEquiv _ (homOfGlobalSection _
    (((tensorPullbackSectionAdjunction a).unit.app M).app ⊤ (s.val (op ⊤))))

/-- The germ of the pullback of the standard affine coordinate `T₀/T₁`.
Source: Stacks, Tags 01NG and 01RW.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale) -/
noncomputable def pencilAffineCoordinateGerm {K : Type u} [Field K]
    {D : Scheme.{u}} [IsIntegral D] (h : D ⟶ ProjectiveLine (Spec (.of K)))
    (hη : genericPoint D ∈ h ⁻¹ᵁ
      ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of K)) ⟨1⟩) :
    D.functionField :=
  (D.presheaf.germ
    (h ⁻¹ᵁ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of K)) ⟨1⟩)
    (genericPoint D) hη).hom
      (h.app (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of K)) ⟨1⟩)
        (ProjectiveSpace.coordRatio (ULift.{u} (Fin 2)) (Spec (.of K)) ⟨1⟩ ⟨0⟩))

/-- The geometric section and function-field clauses, for the actual geometric map.
Source: Stacks, Tags 0C1C, 0BY1, 0CCL and 01NG.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale) -/
def pencilGeometricMapConclusion {K : Type u} [Field K]
    {D : Scheme.{u}} [IsIntegral D] (b : D ⟶ Spec (.of K)) (M : D.Modules)
    (s : ULift.{u} (Fin 2) → M.sections)
    (h : D ⟶ ProjectiveLine (Spec (.of K))) : Prop :=
  (∃! δ : Γ(b.relativeDifferentials ⊗ (M ⊗ M), ⊤),
    pencilDifferentialFrameFormula b M s δ ∧ δ ≠ 0) ∧
  (∀ i : ULift.{u} (Fin 2), (s i).val (op ⊤) ≠ 0) ∧
  IsFinite h ∧ Surjective h ∧
  ∃ hη : genericPoint D ∈ h ⁻¹ᵁ
      ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of K)) ⟨1⟩,
    @KaehlerDifferential.D K D.functionField _ _ (((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫
        D.presheaf.germ ⊤ (genericPoint D) trivial).hom).toAlgebra
      (pencilAffineCoordinateGerm h hη) ≠ 0 ∧
    (∀ c : K, pencilAffineCoordinateGerm h hη ≠ ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫
        D.presheaf.germ ⊤ (genericPoint D) trivial).hom c) ∧
    ∀ (χ : D ⟶ ProjectiveLine (Spec (.of K)))
      (_wχ : χ ≫ ProjectiveLine (Spec (.of K)) ↘ Spec (.of K) = b)
      (hχη : genericPoint D ∈ χ ⁻¹ᵁ
        ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of K)) ⟨1⟩),
      pencilAffineCoordinateGerm χ hχη = pencilAffineCoordinateGerm h hη → χ = h

/-- The geometric conclusions for the unique base change of the given pencil.
This predicate expands the geometric clauses of this node's statement.
Source: Stacks, Tags 0C1C, 0BY1, 0CCL and 01NG.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale) -/
def pencilGeometricConclusion {F K : Type u} [Field F] [Field K] [Algebra F K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) [Smooth f] [GeometricallyIntegral f]
    (M : C.Modules) (s : ULift.{u} (Fin 2) → M.sections)
    (h : C ⟶ ProjectiveLine (Spec (.of F))) : Prop :=
  ∃! hK : pullback f (Spec.map (CommRingCat.ofHom (algebraMap F K))) ⟶
      ProjectiveLine (Spec (.of K)),
    hK ≫ ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom (algebraMap F K))) =
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F K))) ≫ h ∧
    hK ≫ ProjectiveLine (Spec (.of K)) ↘ Spec (.of K) =
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F K))) ∧
    pencilGeometricMapConclusion
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F K))))
      ((tensorPullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap F K))))).obj M)
      (fun i ↦ pencilPullbackSection (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap F K)))) M (s i)) hK

/-- A generating pencil with nonzero alternating differential is finite, surjective and
etale on a nonempty open, over every field, with the stated geometric identification.
Source: Stacks Project, Tags 0C1C, 0BY1, 0CCL, 01NG and 02LA.
(blueprint: lem-sfb-nonzero-pencil-differential-finite-etale)

Proof:
1. The two projective-line charts are affine lines, with integral coordinate rings and
   nonempty overlap. They prove smoothness, integrality and dimension one; projective
   properness gives separatedness (def-sc-p1-standard, sbc-lem-affine-space-smooth,
   lemma-nagata-projective-space-base-change-proper).
2. Replacing a frame e by ue replaces the alternating differential by u^(-2) times
   itself; the du terms cancel. Thus the local tensors glue uniquely. On the two
   generating charts the coordinates are s/t and t/s, and differentiating an inverse
   proves the two displayed quotient rules (lem-weil-pbc-projective-space-standard-charts).
   The coordinate differentials generate the target cotangent line, so dh is nonzero
   exactly when the glued section is nonzero (def-a1-relative-differentials-pullback-map).
3. Apply lem-a1-nonzero-differential-generically-etale to obtain a nonempty etale open.
4. Projectivity makes C proper by the closed-immersion factorization and proper
   composition (lem-weil-pbc-proper-fp-permanence).
5. After an algebraic closure, geometric integrality and smooth relative-dimension
   permanence give a smooth proper integral dimension-one curve
   (lem-a1-smooth-curve-cotangent-generic-isomorphism,
   lem-sbc-smooth-relative-dimension-permanence).
6. Tensor pullback preserves the generating pair and its classified map. Differential
   base change identifies the alternating section. A field-linear functional K to F
   taking 1 to 1 retracts the scalar-extension inclusion, so this section stays nonzero
   (lem-trf-relative-differential-sheaf-base-change,
   lem-weil-pbc-projective-space-functor-of-points).
7. Both geometric sections are nonzero, since otherwise their alternating differential
   vanishes. The t-chart contains the generic point. Its coordinate germ r has dr nonzero
   by localization of differentials and the generic cotangent criterion, so r is not a
   constant (lem-weil-pbc-kahler-differentials-localization).
8. The proper curve/function-field correspondence identifies the actual geometric map
   with the embedding z to r; embeddings of K(z) are determined by z. Its uniqueness
   gives precisely the final equality clause (lem-sfb-proper-curve-function-field-morphisms).
9. The map is proper with closed image containing the target generic point, hence
   surjective. It does not contract the sole dimension-one component; Tag 0CCL gives
   finiteness (lem-weil-pbc-proper-over-separated,
   lem-sfb-proper-dimension-one-noncontraction-finite).
10. Field-extension faithful flatness on the two affine charts makes the projective-line
    projection flat and surjective; affine quasi-compactness and base change make it
    quasi-compact (lem-weil-pbc-field-extension-base-change-faithfully-flat,
    lem-weil-pbc-flat-ring-map-iff-flat-affine,
    lem-weil-pbc-faithfully-flat-surjective-spectrum,
    lem-pc-field-extension-quasi-compact, lem-pc-quasi-compact-base-change).
11. Finiteness descends along this fpqc projection, and surjectivity descends by lifting
    points twice (lem-sbc-finite-morphism-fpqc-descent). No perfection or characteristic
    assumption occurred in any step. -/
theorem nonzero_pencil_differential_finite_etale
    {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) [Smooth f] [IsHProjective f]
    [GeometricallyIntegral f] [IsIntegral C] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hdim : topologicalKrullDim C = 1) (M : C.Modules) [M.IsInvertible]
    (s : ULift.{u} (Fin 2) → M.sections) (hs : Epi (M.freeHomEquiv.symm s))
    (h : C ⟶ ProjectiveLine (Spec (.of F)))
    (_hh : h = ProjectiveSpace.homOfGeneratingSections _ f M s hs) :
    Smooth (ProjectiveLine (Spec (.of F)) ↘ Spec (.of F)) ∧
    IsSeparated (ProjectiveLine (Spec (.of F)) ↘ Spec (.of F)) ∧
    IsIntegral (ProjectiveLine (Spec (.of F))) ∧
    topologicalKrullDim (ProjectiveLine (Spec (.of F))) = 1 ∧
    pencilDifferentialChartFormula f M s h ∧
    ∃! δ : Γ(f.relativeDifferentials ⊗ (M ⊗ M), ⊤),
      pencilDifferentialFrameFormula f M s δ ∧
      (Scheme.Hom.relativeDifferentialsPullbackMap
        (ProjectiveLine (Spec (.of F)) ↘ Spec (.of F)) h ≠ 0 ↔ δ ≠ 0) ∧
      (δ ≠ 0 → IsFinite h ∧ Surjective h ∧
        ∃ V : C.Opens, (V : Set C).Nonempty ∧ Etale (V.ι ≫ h)) ∧
      ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosure F K],
        Flat (ProjectiveSpace.map (ULift.{u} (Fin 2))
          (Spec.map (CommRingCat.ofHom (algebraMap F K)))) ∧
        Surjective (ProjectiveSpace.map (ULift.{u} (Fin 2))
          (Spec.map (CommRingCat.ofHom (algebraMap F K)))) ∧
        QuasiCompact (ProjectiveSpace.map (ULift.{u} (Fin 2))
          (Spec.map (CommRingCat.ofHom (algebraMap F K)))) ∧
        (δ ≠ 0 → pencilGeometricConclusion f M s h (K := K)) := by
  sorry

end AlgebraicGeometry
