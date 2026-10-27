/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.SmoothGenericRankReduction
import Sheaf.AlgebraicGeometry.SmoothFreeSequenceTransformFlatness
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
import Sheaf.TraceFormula.EtaleFlatteningDescent

/-!
# Flattening a smooth affine family from smaller-support cases

Source: Stacks Project, flat.tex, Tag 0815, theorem-flatten-module, third proof paragraph.
(blueprint: lem-trf-flattening-smooth-support-induction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The generic free subtraction step reduces smooth relative dimension n to modules
whose fibre support has dimension strictly below n.
Source: Stacks Project, Tag 0815, theorem-flatten-module, third proof paragraph.
(blueprint: lem-trf-flattening-smooth-support-induction).

Proof: Apply exists_admissibleBlowup_smooth_genericRankReduction. On each member of its
finite affine base cover, its universally exact free sequence has cokernel H with fibre
support dimension < n. It supplies quasi-coherence, finite type, finite presentation and
flatness over the compact preserved open for H. Apply hlower to H on that affine base;
the restricted IsFlatOver hypothesis gives the required stalk-flatness hypothesis.
The affine smooth source morphism is quasi-compact and locally of finite presentation.
Use smoothFreeSequence_transform_flatness to transfer flatness of the transformed H
to the transformed middle term on each cover member. Etale flattening descent glues
these open-cover blowups on the preliminary blowup base. The admissible-blowup calculus
composes this blowup with the preliminary one and identifies successive strict transforms;
flatness transfers across the resulting source and base isomorphisms. For n = 0 the
cokernel has empty fibre support, exactly the d = 0 case of hlower. Rank zero and empty
affine charts are allowed by both free-sequence and descent statements. -/
theorem exists_flat_moduleStrictTransform_smooth_of_lower_support
    (n : ℕ)
    (hlower : ∀ (S X : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (U : S.Opens), IsCompact (U : Set S) →
      (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation →
      (∀ x : X, f x ∈ U → Module.Flat (S.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F))) →
      (∀ s : S, topologicalKrullDim {x : f.fiber s |
      ¬ Subsingleton (((tensorPullback (f.fiberι s)).obj F).presheaf.stalk x)} <
        (n : WithBot ℕ∞)) →
      ∃ B : IsAdmissible S U,
      (@moduleStrictTransform _ _ f B.I
        (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFlatOver
          (pullback.snd f B.I.blowupMap))
    {S X : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsAffineHom f] [SmoothOfRelativeDimension n f]
    [GeometricallyIntegral f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation)
    (hflat : (F.restrict (f ⁻¹ᵁ U).ι).IsFlatOver (f ∣_ U)) :
    ∃ B : IsAdmissible S U,
      (@moduleStrictTransform _ _ f B.I
        (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFlatOver
          (pullback.snd f B.I.blowupMap) := by sorry

end AlgebraicGeometry.Scheme.Modules
