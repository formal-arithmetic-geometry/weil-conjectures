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
import Sheaf.TraceFormula.DevissageFlatteningTransfer
import Sheaf.TraceFormula.EtaleFlatteningDescent
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback

/-!
# Reducing bounded-support flattening to smooth affine families

Source: Stacks Project, flat.tex, Tag 0815, theorem-flatten-module, the first two
paragraphs of the proof, and Tag 0814, lemma-flatten-module-etale-localize.
(blueprint: lem-trf-flattening-smooth-affine-reduction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The etale-local devissage step of support-dimension induction for flattening.
Source: Stacks Project, Tag 0815, theorem-flatten-module, first two proof paragraphs;
Tag 0814, lemma-flatten-module-etale-localize.
(blueprint: lem-trf-flattening-smooth-affine-reduction).

Proof: At a point of nonzero fibre support, apply exists_devissage_flattening_transfer.
Its local support dimension n is at most the dimension of that fibre support, hence n < d.
The smooth affine pushforward module satisfies the presentation and flatness hypotheses
on the preserved open. Apply hsmooth and transfer the resulting strict-transform flatness
back through the finite and closed pushforwards using the equivalence in devissage transfer.
At a point outside support, finite-type support is closed, so use a zero restriction on an
open neighbourhood and the unit-ideal blowup. These etale source neighbourhoods cover X.
Quasi-compactness gives a finite subcover. Their affine etale bases are quasi-compact over
the quasi-separated base. Adjoin empty source diagrams over a finite affine cover of S
so the bases also cover S; zero modules on these diagrams are already flat. Apply finite
etale flattening descent to this family. When d = 0 every fibre support is empty and only
the zero-restriction diagrams are needed. No maximum of a nonempty support is assumed. -/
theorem exists_flat_moduleStrictTransform_of_smooth_affine
    (d : ℕ)
    (hsmooth : ∀ n : ℕ, n < d →
      ∀ (S X : Scheme.{u}) [IsAffine S]
      (f : X ⟶ S) [IsAffineHom f] [SmoothOfRelativeDimension n f]
      [GeometricallyIntegral f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (U : S.Opens), IsCompact (U : Set S) →
      (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation →
      (F.restrict (f ⁻¹ᵁ U).ι).IsFlatOver (f ∣_ U) →
      ∃ B : IsAdmissible S U,
      (@moduleStrictTransform _ _ f B.I
        (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFlatOver
          (pullback.snd f B.I.blowupMap))
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [QuasiCompact f] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation)
    (hflat : ∀ x : X, f x ∈ U → Module.Flat (S.presheaf.stalk (f x))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)))
    (hdim : ∀ s : S, topologicalKrullDim {x : f.fiber s |
      ¬ Subsingleton (((tensorPullback (f.fiberι s)).obj F).presheaf.stalk x)} <
        (d : WithBot ℕ∞)) :
    ∃ B : IsAdmissible S U,
      (@moduleStrictTransform _ _ f B.I
        (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).IsFlatOver
          (pullback.snd f B.I.blowupMap) := by sorry

end AlgebraicGeometry.Scheme.Modules
