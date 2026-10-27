/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Irreducible

/-! # Free geometric orbits of faithful finite actions on curves

Source: Stacks Project, Tags 0BY1, 02W0, 01KM, 056U, 0893 and 01XZ
(blueprint: lem-sfb-faithful-curve-free-geometric-orbit).

The three abbreviations only name the canonical scheme base change, its induced group
homomorphism and the tensor pullback of the given line bundle. They introduce no choices.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The canonical field base change, retaining its structure map to `Spec E`.
Source: Stacks Project, Tag 01JX; the base change in the geometric setup of Tag 0BY1
(blueprint: lem-sfb-faithful-curve-free-geometric-orbit). -/
noncomputable abbrev faithfulCurveFieldBaseChange {F : Type u} [Field F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) (E : Type u) [Field E] [Algebra F E] :
    Over (Spec (.of E)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).obj (Over.mk f)

/-- The original action base changed by the canonical pullback functor on schemes over `F`.
Source: Stacks Project, Tags 01JX and 02W0; geometric setup of Tag 0BY1
(blueprint: lem-sfb-faithful-curve-free-geometric-orbit). -/
noncomputable abbrev faithfulCurveFieldBaseChangeAction {F : Type u} [Field F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) {G : Type v} [Group G]
    (ρ : G →* Aut (Over.mk f)) (E : Type u) [Field E] [Algebra F E] :
    G →* Aut (faithfulCurveFieldBaseChange f E) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))).mapAut
    (Over.mk f)).comp ρ

/-- The given invertible module pulled back along the first projection of the field base change.
Source: Stacks Project, Tags 01JX and 0893
(blueprint: lem-sfb-faithful-curve-free-geometric-orbit). -/
noncomputable abbrev faithfulCurveFieldBaseChangeModule {F : Type u} [Field F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) (L : C.Modules)
    (E : Type u) [Field E] [Algebra F E] : (faithfulCurveFieldBaseChange f E).left.Modules :=
  (Scheme.Modules.tensorPullback
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F E))))).obj L

/-- Faithful finite curve actions have a nonempty open with no nonidentity geometric stabilizers
and an algebraically closed rational closed point with pairwise distinct underlying orbit points.
The arbitrary-field base-change clause also records the curve, ampleness and coherence facts.

Source: Stacks Project, Tags 0BY1, 02W0, 01KM, 056U, 0893 and 01XZ
(blueprint: lem-sfb-faithful-curve-free-geometric-orbit).

Proof:
1. Fix `E/F`. Projectivity implies properness (lem-kun-projective-implies-proper),
   which survives base change (lem-weil-pbc-proper-base-change). The relative dimension
   lemma lem-sc-curve-base-change-relative-dimension-one gives smooth relative dimension
   one. Iterated base change and geometric integrality imply that every further field
   extension gives an integral scheme. In particular the fibre over `E` is nonempty, so
   its dimension is one. Finite type over the Noetherian field spectrum gives Noetherianity
   (lem-weil-pbc-finite-type-over-noetherian).
2. Relative ampleness survives base change (lem-trf-scheme-relative-ample-base-change).
   Since both base spectra are affine, this gives absolute ampleness of the tensor
   pullback. Pull back local rank-one trivializations to obtain invertibility.
3. A finite locally free module is locally a finite free module, hence quasi-coherent
   of finite type. On a locally Noetherian scheme it is coherent by
   pqf-lem-coherent-ft-locnoeth. A coherent ideal tensored with a locally free module
   is locally a finite direct sum of that ideal, hence likewise quasi-coherent of finite
   type and coherent. Rank zero is included.
4. For an algebraic closure `Ω/F`, Spec Ω → Spec F is fpqc
   (lem-pc-field-extension-fpqc-cover). Descent of morphisms is injective on morphisms
   over the base (lem-galois-fpqc-morphisms-descend), so the base-changed action is faithful.
5. For each `g ≠ 1`, form the equalizer of its automorphism and the identity by pulling
   back the diagonal. It is closed since the curve is separated (01KM and
   lem-weil-pbc-closed-immersion-base-change). A test morphism factors through it exactly
   when the two composite morphisms agree; this detects residue-field maps as well.
6. Its closed image is proper: otherwise its dense image in the reduced curve would
   force the automorphism to be the identity by lem-sfb-relative-separated-dominant-ext.
   A finite union of proper closed subsets of a nonempty irreducible space is proper,
   inductively by irreducibility. Its complement is the required nonempty open. A fixed
   geometric point would factor through the excluded equalizer, a contradiction.
7. Density of smooth closed points with finite separable residue field
   (lem-pc-dense-separable-points) gives a closed point in the open. Over `Ω` its residue
   field is `Ω`, yielding the rational point. Equal underlying orbit points give equal
   Ω-rational point morphisms, since their residue-field maps over Ω are unique.
   Applying the inverse of one group element would then fix this geometric point, so
   the two elements agree. For the trivial group the excluded union is empty. No step
   divides by the group order or assumes any restriction on the characteristic. -/
theorem faithful_curve_free_geometric_orbit {F : Type u} [Field F]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of F)) [Smooth f] [IsHProjective f]
    [GeometricallyIntegral f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim C = 1) {G : Type v} [Group G] [Finite G]
    (ρ : G →* Aut (Over.mk f)) (hρ : Function.Injective ρ)
    (L : C.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple C L) :
    (∀ (E : Type u) [Field E] [Algebra F E],
      Smooth (faithfulCurveFieldBaseChange f E).hom ∧
      IsProper (faithfulCurveFieldBaseChange f E).hom ∧
      GeometricallyIntegral (faithfulCurveFieldBaseChange f E).hom ∧
      IsNoetherian (faithfulCurveFieldBaseChange f E).left ∧
      topologicalKrullDim (faithfulCurveFieldBaseChange f E).left = 1 ∧
      ∃ hInv : (faithfulCurveFieldBaseChangeModule f L E).IsInvertible,
        @Scheme.Modules.IsAmple (faithfulCurveFieldBaseChange f E).left
          (faithfulCurveFieldBaseChangeModule f L E) hInv ∧
        (∀ V : (faithfulCurveFieldBaseChange f E).left.Modules,
          V.IsFiniteLocallyFree →
          RingedSpace.IsCoherent (faithfulCurveFieldBaseChange f E).left.toRingedSpace V) ∧
        (∀ I : (faithfulCurveFieldBaseChange f E).left.IdealSheafData,
          RingedSpace.IsCoherent (faithfulCurveFieldBaseChange f E).left.toRingedSpace
            I.toModules →
          ∀ V : (faithfulCurveFieldBaseChange f E).left.Modules, V.IsFiniteLocallyFree →
            RingedSpace.IsCoherent (faithfulCurveFieldBaseChange f E).left.toRingedSpace
              (I.toModules ⊗ V : (faithfulCurveFieldBaseChange f E).left.Modules))) ∧
    (∀ (Ω : Type u) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
      Function.Injective (faithfulCurveFieldBaseChangeAction f ρ Ω) ∧
      ∃ U : (faithfulCurveFieldBaseChange f Ω).left.Opens,
        Set.Nonempty (U : Set (faithfulCurveFieldBaseChange f Ω).left) ∧
        (∀ (K : Type u) [Field K] [IsAlgClosed K]
          (y : Spec (.of K) ⟶ (faithfulCurveFieldBaseChange f Ω).left),
          (Scheme.SpecToEquivOfField K (faithfulCurveFieldBaseChange f Ω).left y).1 ∈ U →
          ∀ g : G, g ≠ 1 → y ≫ (faithfulCurveFieldBaseChangeAction f ρ Ω g).hom.left ≠ y) ∧
        ∃ x : Spec (.of Ω) ⟶ (faithfulCurveFieldBaseChange f Ω).left,
          x ≫ (faithfulCurveFieldBaseChange f Ω).hom = 𝟙 (Spec (.of Ω)) ∧
          (Scheme.SpecToEquivOfField Ω (faithfulCurveFieldBaseChange f Ω).left x).1 ∈ U ∧
          (Scheme.SpecToEquivOfField Ω (faithfulCurveFieldBaseChange f Ω).left x).1 ∈
            closedPoints (faithfulCurveFieldBaseChange f Ω).left ∧
          Function.Injective (fun g : G ↦
            (faithfulCurveFieldBaseChangeAction f ρ Ω g).hom.left
              ((Scheme.SpecToEquivOfField Ω (faithfulCurveFieldBaseChange f Ω).left x).1))) := by
  sorry

end AlgebraicGeometry
