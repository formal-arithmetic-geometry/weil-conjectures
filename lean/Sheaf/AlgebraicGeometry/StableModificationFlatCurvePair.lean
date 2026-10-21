/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Sober
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.ChowLemma
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import Sheaf.TraceFormula.TemkinStableModification

/-!
# Stable modification of a flat multipointed relative curve

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, §3.2.2 and Theorem 3.4,
Step 3 and the first sentence of Step 4, printed pp. 158, 160--161; Temkin,
Stable modification of relative curves, §1.2 and Theorems 1.1 and 1.5
(blueprint: lem-trf-stable-modification-flat-curve-pair).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Stable modification of a flat curve with a flat, zero-dimensional closed marking.
Neither input family is required to be proper or separated. Empty markings and empty
fibres are allowed. The marking structure map is written as `i ≫ f`.

Source: ILO, Exposé X, §3.2.2 and Theorem 3.4, Steps 3--4; Temkin, §1.2 and
Theorems 1.1 and 1.5 (blueprint: lem-trf-stable-modification-flat-curve-pair).

Proof: (1) Apply `lem-trf-temkin-stable-modification` to the multipointed curve. The smooth
and etale generic fibres are semistable. This gives a proper generically finite alteration
and a projective-bundle modification of both the curve and its marking, with generic-fibre
isomorphisms and semistability preserved by base change.
(2) Apply `lem-weil-pbc-chow-noetherian` to that alteration. Take the schematic image of the
isomorphism open in the Chow model, using `lem-weil-pbc-scheme-image-qc-kernel` and
`lemma-nagata-immersion-open-in-scheme-image`; no density in the entire model is needed.
(3) This image is integral: its dense open is integral and, on affine charts, its coordinate
rings embed in sections on that open, hence in its function field.
(4) The refined base is proper over the original base. Its immersion into finite projective
space is proper over the separated projective space, hence closed, by
`lem-weil-pbc-proper-over-separated` and `lem-weil-pbc-proper-immersion-closed`.
It is Noetherian and excellent by `lem-weil-pbc-finite-type-over-noetherian` and
`lem-exc-finite-type-localization-excellent`.
(5) Remove from the finite open of the original alteration the proper image of the complement
of its Chow isomorphism open. The resulting dense open gives finiteness of the composite;
the composite is dominant because both factors are dominant.
(6) Base-change the semistable marked modification to the refined base. Relative Proj
base change (`lemma-nagata-relative-proj-base-change-arbitrary`), compatibility of symmetric
algebras with pullback, and closed-immersion base change preserve projective-bundle
projectivity. The generic-fibre isomorphisms of both maps are preserved.
(7) The marking map factors as a closed immersion into the inverse image of the old marking
followed by the base change of the proper curve modification. The quotient-ideal description
of closed immersions and `lem-weil-pbc-proper-fp-permanence` make it proper.
The completed local equation and the smooth marking are exactly those from Temkin.
There is no prime-to-an-integer or degree condition. -/
theorem exists_stableModification_flatCurvePair
    {S C H : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    (hS : ∀ U : S.Opens, IsAffineOpen U → IsExcellent Γ(S, U))
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (f : C ⟶ S) (i : H ⟶ C) [IsClosedImmersion i]
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    [QuasiCompact (i ≫ f)] [QuasiSeparated (i ≫ f)]
    (hCdim : ∀ s : S, (f.fiber s).IsPureDimension 1)
    (hHdim : ∀ s : S, ((i ≫ f).fiber s).IsPureDimension 0)
    [Smooth (f.fiberToSpecResidueField η)]
    [Etale ((i ≫ f).fiberToSpecResidueField η)] :
    ∃ (S' : Scheme.{u}) (_ : IsIntegral S') (_ : IsNoetherian S') (r : S' ⟶ S),
      (∀ U : S'.Opens, IsAffineOpen U → IsExcellent Γ(S', U)) ∧
      IsHProjective r ∧ DenseRange r.base ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (r ∣_ U)) ∧
      ∃ (C' H' : Scheme.{u}) (g : C' ⟶ S') (i' : H' ⟶ C')
        (m : C' ⟶ pullback f r) (n : H' ⟶ pullback (i ≫ f) r),
        m ≫ pullback.snd f r = g ∧
        i' ≫ g = n ≫ pullback.snd (i ≫ f) r ∧
        i' ≫ m ≫ pullback.fst f r = n ≫ pullback.fst (i ≫ f) r ≫ i ∧
        IsProjectiveBundle m ∧ IsProper n ∧
        (∀ η' : S', IsGenericPoint η' (Set.univ : Set S') →
          IsIso (pullback.snd m ((pullback.snd f r).fiberι η')) ∧
          IsIso (pullback.snd n ((pullback.snd (i ≫ f) r).fiberι η'))) ∧
        Flat g ∧ LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g ∧
        (∀ s : S', (g.fiber s).IsPureDimension 1) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S')
          (x : (pullback (C := Scheme.{u}) g s : Scheme.{u})),
          (∃ U : (pullback g s : Scheme.{u}).Opens,
            x ∈ U ∧ Smooth (U.ι ≫ pullback.snd g s)) ∨
            Orgogozo.IsOrdinaryDoublePoint (pullback.snd g s) x) ∧
        IsClosedImmersion i' ∧ Etale (i' ≫ g) ∧
        ∀ x : H', ∃ U : C'.Opens, i' x ∈ U ∧ Smooth (U.ι ≫ g) := by
  sorry

end AlgebraicGeometry
