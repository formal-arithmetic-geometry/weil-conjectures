/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Birational.Birational

import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability
import Sheaf.TraceFormula.ProjectiveBundleSeparated
import Sheaf.TraceFormula.LogRegularDivisorialStructure

/-!
# Gabber modification preserving relative logarithmic smoothness

Source: ILO, Exposé X Theorem 1.1 and its proof 1.3--1.8, pp.135--148;
VI Theorem 3.2, pp.73--75; XVI 3.7, pp.254--255
(blueprint: lem-per-gabber-log-smooth-equivariant-modification).

The trait log structure is identified, compatibly with its structural map, with
regular functions invertible over the generic point. Both equal and mixed
characteristic are included. No restriction confines the enlarged boundary to the
special fibre.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A tame generically free finite action on an integral fs log-regular log-smooth
model over a complete strictly henselian trait admits an equivariant projective
birational modification whose source and invariant-log quotient are log smooth
and log regular over the same trait.

Source: ILO X Theorem 1.1, pp.135--136; VI Theorem 3.2, pp.73--75;
XVI 3.7, pp.254--255
(blueprint: lem-per-gabber-log-smooth-equivariant-modification).

Proof, following the six DAG steps:
1. Complete local excellence and finite-type stability make the trait and source
   quasi-excellent and Noetherian. The canonical uniformizer chart is log regular.
   Projective-space separatedness gives separatedness of the quasi-projective source.
   Log-regular divisorial recognition identifies its boundary and makes the map one
   of log-regular pairs (lem-per-complete-local-excellence,
   lem-per-quasi-excellent-finite-type-stability, lem-trf-projective-bundle-separated,
   lem-trf-log-regular-divisorial-structure).
2. Apply lem-per-gabber-absolute-equivariant-modification for the absolute four-stage
   projective birational construction with very tame final action. Its log boundary
   includes the inverse image of the original boundary and the nonfree locus. This
   step alone gives no relative log-smoothness assertion.
3. The first two stages are saturated log blowup towers, hence log étale, and preserve
   log smoothness over the trait by composition
   (lem-per-log-smooth-composition-strict-base-change).
4. Use lem-per-gabber-fixed-locus-log-chart in each third-stage blowup. The z-chart
   lattice map is an automorphism. The y-chart map has free cokernel Z, so its
   cokernel extension splits and preserves the invertible torsion. Polynomial
   comparison maps are smooth. The chart criterion and strict-base-change locality
   preserve log smoothness through this finite stage.
5. In lem-per-gabber-abelian-stage-toric-chart, the invariant lattice quotient and
   retained-boundary lattice quotient embed in the original cokernel. Their torsion
   remains finite of invertible order. The retained chart comparison is affine space
   in the discarded boundary coordinates, hence smooth. The chart criterion proves
   relative log smoothness of the fourth-stage quotient.
6. Use lem-per-projective-finite-group-quotient for the categorical geometric scheme
   quotient and invariant affine charts. Apply lem-per-very-tame-log-quotient for
   exactly the invariant direct-image fs log structure, log regularity and the Kummer
   étale projection. Step 5 gives log smoothness of the quotient over the trait;
   composition gives log smoothness of the modified source. Equivariant birationality
   and relative quasi-projectivity come from the absolute construction. -/
theorem exists_gabber_logSmooth_equivariant_modification
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsStrictlyHenselianLocalRing R]
    (T : FineSaturatedLogScheme.{u}) (e : T.scheme ≅ Spec R)
    (hcanonical : ∃ c : T.logStructure.monoidSheaf.obj ≅
      divisorialLogPresheaf
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ e.inv),
      c.hom ≫ divisorialStructuralMap
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ e.inv) =
          T.logStructure.alpha)
    (V : FineSaturatedLogScheme.{u}) [IsIntegral V.scheme]
    (f : EtaleLogHom V T) (hregular : V.IsLogRegular) (hsmooth : f.IsLogSmooth)
    [LocallyOfFiniteType f.base] [QuasiCompact f.base]
    (hqp : ∃ (N : ℕ) (i : V.scheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); T.scheme)),
      IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); T.scheme) ↘ T.scheme = f.base)
    (H : Type v) [Group H] [Finite H] (a : FSLogGroupAction H V)
    (hover : ∀ g : H, (a.logMap g).CompEq f f)
    (htame : a.IsTame) (hfree : a.IsGenericallyFree) :
    ∃ (W : FineSaturatedLogScheme.{u}) (b : FSLogGroupAction H W)
      (h : EtaleLogHom W V) (s : EtaleLogHom W T)
      (Q : FineSaturatedLogScheme.{u}) (q : EtaleLogHom W Q) (t : EtaleLogHom Q T),
      IsIntegral W.scheme ∧ LocallyOfFiniteType s.base ∧ QuasiCompact s.base ∧
      (∃ (N : ℕ) (i : W.scheme ⟶ ℙ(ULift.{u} (Fin (N + 1)); T.scheme)),
        IsImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (N + 1)); T.scheme) ↘ T.scheme = s.base) ∧
      h.CompEq f s ∧ b.IsEquivariant a h ∧ IsHProjective h.base ∧
      (∃ d : W.scheme.PartialIso V.scheme,
        d.source.ι ≫ h.base = d.iso.hom ≫ d.target.ι) ∧
      W.IsLogRegular ∧ s.IsLogSmooth ∧ b.IsQuotient q ∧ q.CompEq t s ∧
      Q.IsLogRegular ∧ t.IsLogSmooth := by
  sorry

end AlgebraicGeometry
