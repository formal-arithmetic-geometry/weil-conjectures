/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.InvariantOpenEffectiveDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
import WeilConjectures.AlgebraicGeometry.TransportLeftNaturality
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Defs.Filter
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.SpectralGeneralizations
import Mathlib.Topology.Inseparable
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.AlgebraicGeometry.IntersectionSectionsFlatBaseChange
import WeilConjectures.AlgebraicGeometry.AffineFlatDescent
import WeilConjectures.AlgebraicGeometry.IntersectionStructureSections
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.Algebra.Category.Ring.Constructions
import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant
import WeilConjectures.AlgebraicGeometry.FpqcEffectivityAffineBaseGluing
import WeilConjectures.AlgebraicGeometry.FpqcSingletonAffineRefinement
import WeilConjectures.AlgebraicGeometry.FpqcCanonicalPullbackDatum
import WeilConjectures.AlgebraicGeometry.FpqcRefinementReflectsEffectivity

/-! # Effective descent for ind-quasi-affine schemes

Source: Stacks Project, More on Groupoids, Tag 0APK, lemma-ind-quasi-affine;
More on Morphisms, Tag 0AP6, definition-ind-quasi-affine
(blueprint: lem-sfb-ind-quasi-affine-effective-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- A descent datum on an ind-quasi-affine scheme along a flat, surjective,
quasi-compact morphism is effective. The morphism `t` need not be quasi-compact or
locally of finite presentation.

Source: Stacks Project, Tag 0APK, lemma-ind-quasi-affine; Tag 0AP6 defines the
ind-quasi-affine condition appearing in `hT`.
(blueprint: lem-sfb-ind-quasi-affine-effective-descent)

`D` is the recorded transport form of the overlap isomorphism and its cocycle.
`D.IsEffective` gives an X-scheme and a Cartesian square identifying T with its
pullback to V; invariance of transport is exactly compatibility with the canonical
descent datum, hence the displayed conjugation identity in the node.

Proof:
1. The flat, surjective, quasi-compact map p is a singleton fpqc covering.
2. For an affine open B in V, identify T times_V B with the inverse-image open
   t inverse B using pullbackRestrictIsoRestrict.
3. A quasi-compact open K in the pullback has quasi-compact open image under this
   isomorphism. The hypothesis makes that image quasi-affine, and hence K is
   quasi-affine. Since B is affine, the morphism K to B is quasi-compact and
   therefore quasi-affine.
4. Apply isEffective_of_indQuasiAffine_fpqc with this translated hypothesis.
   This is the same Stacks 0APK argument, already implemented in the library. -/
theorem isEffective_of_indQuasiAffine_flat_surjective_quasiCompact
    {V X T : Scheme.{u}} (p : V ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (t : T ⟶ V)
    (hT : ∀ (B : V.Opens), IsAffineOpen B →
      ∀ (U : (t ⁻¹ᵁ B).toScheme.Opens),
        IsCompact (U : Set (t ⁻¹ᵁ B).toScheme) → U.toScheme.IsQuasiAffine)
    (D : Over.DescentDatum p (Over.mk t)) : D.IsEffective := by
  apply isEffective_of_indQuasiAffine_fpqc p p.singleton_mem_fpqcPrecoverage ?_ D
  intro B hB K hK
  let e := pullbackRestrictIsoRestrict t B
  have : (e.hom ''ᵁ K).toScheme.IsQuasiAffine :=
    hT B hB (e.hom ''ᵁ K) (hK.image e.hom.continuous)
  have : K.toScheme.IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isIso (e.hom.isoImage K).hom
  have : IsAffine B.toScheme := hB
  infer_instance

end CategoryTheory.Over.DescentDatum
