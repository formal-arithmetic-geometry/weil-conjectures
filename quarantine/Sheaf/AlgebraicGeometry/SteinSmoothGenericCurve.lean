/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Sober
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.Paper.OrgogozoInductionData
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import Sheaf.AlgebraicGeometry.ProperGeometricallyReducedGlobalSectionsSeparable
import WeilConjectures.AlgebraicGeometry.FractionFieldSectionsBaseChange
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle

/-!
# Finite Stein base of a proper smooth generic curve

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, §1.3, printed p. 132;
Stacks Project, Tags 03H0, 0BUG, 0FD1, 0B3I and 07QU
(blueprint: lem-trf-stein-smooth-generic-curve).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The finite Stein base of a proper dominant morphism with smooth irreducible generic
curve is excellent, integral and Noetherian, and its generic curve is smooth and
geometrically integral. Projectivity uses the EGA projective-bundle convention.
Source: ILO, Exposé IX, §1.3, printed p. 132; Stacks 03H0, 0BUG, 0FD1, 0B3I and 07QU
(blueprint: lem-trf-stein-smooth-generic-curve).

The affine section isomorphism `g.app`, together with the affineness of the finite q,
specifies `S₀ = Spec_S(f_* O_C)`. The affine chart is `toSpecΓ` followed by Spec of
the inverse section isomorphism. In its target ring,
`g ⁻¹ᵁ (q ⁻¹ᵁ U) = f ⁻¹ᵁ U` by the factorization equality. The map `t` is the generic
restriction of `g`; its displayed compatibility characterizes it uniquely, since the
residue-field inclusion is a monomorphism. The isomorphism on global sections is the
canonical identification of the generic Stein residue field with `H⁰(C_η, O)`.
The residue extension uses `q.residueFieldMap`; the equality `q η₀ = η` identifies its
source with the stated generic field of S.

Proof plan:
1. Form the relative spectrum of the quasi-coherent algebra `f_* O_C`
   (def-weil-pbc-stein-factorization, lem-weil-pbc-affine-morphism-relative-spec).
   Proper coherent pushforward (lem-pc-coherent-hi) gives quasi-coherence and finite
   affine section algebras. The canonical affine charts glue the factorization.
2. These algebras are finite over the affine rings of S, hence q is finite. They are
   domains by restriction to the function field of the integral C over nonempty opens.
   Finite-type permanence gives excellence (lem-exc-finite-type-localization-excellent)
   and Noetherianness (lem-weil-pbc-finite-type-over-noetherian). Finite morphisms are
   projective in the bundle sense (lem-trf-finite-projective-bundle).
3. Apply affine Stein factorization (lem-weil-pbc-stein-factorization-affine) on the
   affine cover. It gives properness of g and geometrically connected nonempty fibres.
   Thus g is surjective and its image is irreducible. The domain charts make S₀ reduced,
   so it is integral. Dominance of f and the factorization imply dominance of q.
4. The generic fibre is proper by lem-pc-proper-base-change. Its global sections form
   a finite field extension (lem-pc-h0-proper-variety). Smoothness gives geometric
   reducedness (sbc-lem-smooth-geometrically-reduced), hence separability by
   lem-pc-proper-geometrically-reduced-global-sections-separable. Flat base change to
   the fraction field (lem-sc-fraction-field-sections-base-change) identifies the
   generic relative spectrum with the spectrum of this field, giving the stated t.
5. The generic fibre of g is canonically the original generic fibre as a scheme,
   equipped with its new scalar field, not its field-base-change along that extension.
   Finite separability makes that field map etale
   (lem-weil-pbc-finite-separable-extension-etale). Its base change is etale
   (lem-weil-pbc-etale-scheme-base-change), and the graph of the new scalar map is a
   clopen section (lem-weil-pbc-etale-section-clopen-immersion). It is thus an open of
   the smooth base-changed original curve, hence smooth over the new field. It is
   geometrically connected by affine Stein. After every field extension it is smooth,
   hence regular (lem-weil-pbc-smooth-over-field-regular-local), and nonempty connected,
   hence integral (lem-sc-regular-connected-integral). Its dimension is one because
   its underlying scheme is the original generic fibre (def-kun-topological-krull-dimension).
-/
theorem exists_stein_smooth_generic_curve
    {C S : Scheme.{u}} [IsIntegral C] [IsIntegral S]
    [IsNoetherian C] [IsNoetherian S]
    (hC : Orgogozo.IsExcellentScheme C) (hS : Orgogozo.IsExcellentScheme S)
    (f : C ⟶ S) [IsProper f] [IsDominant f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    [Smooth (f.fiberToSpecResidueField η)] [IrreducibleSpace (f.fiber η)]
    (hdim : topologicalKrullDim (f.fiber η) = 1) :
    ∃ (S₀ : Scheme.{u}) (q : S₀ ⟶ S) (g : C ⟶ S₀),
      IsIntegral S₀ ∧ IsNoetherian S₀ ∧ Orgogozo.IsExcellentScheme S₀ ∧
      g ≫ q = f ∧ IsFinite q ∧ IsDominant q ∧ IsProjectiveBundle q ∧
      IsProper g ∧ GeometricallyConnected g ∧
      (∀ (U : S.Opens), IsAffineOpen U →
        IsIso (g.app (q ⁻¹ᵁ U))) ∧
      ∀ (η₀ : S₀), IsGenericPoint η₀ Set.univ →
        q η₀ = η ∧ (q.residueFieldMap η₀).hom.Finite ∧
        @Algebra.IsSeparableExtension (S.residueField (q η₀)) (S₀.residueField η₀)
          _ _ (q.residueFieldMap η₀).hom.toAlgebra ∧
        Smooth (g.fiberToSpecResidueField η₀) ∧
        GeometricallyIntegral (g.fiberToSpecResidueField η₀) ∧
        topologicalKrullDim (g.fiber η₀) = 1 ∧
        ∃ t : f.fiber η ⟶ Spec (S₀.residueField η₀),
          t ≫ S₀.fromSpecResidueField η₀ = f.fiberι η ≫ g ∧
          IsIso ((Scheme.ΓSpecIso (S₀.residueField η₀)).inv ≫ t.appTop) := by
  sorry

end AlgebraicGeometry
