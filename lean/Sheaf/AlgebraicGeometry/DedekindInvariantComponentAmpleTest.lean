/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Connected.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Polynomial.Derivative
import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.DedekindDomain.Dvr
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Sheaf.AlgebraicGeometry.StrictHenselizationDVR
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.RingTheory.RegularLocalDimOneIffNormal
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.AmplePullback
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.AlgebraicGeometry.LimitFibreProducts
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent

/-! # Strict-local invariant components detect ampleness

Source: Bosch–Lütkebohmert–Raynaud, Néron Models, §6.4, Proposition 2,
initial reductions, printed pp.153–154 (PDF pp.159–160); Stacks Tags 09MT,
0D2P and 01VK (blueprint: lem-sfb-dedekind-invariant-component-ample-test).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonObj
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Flat separably closed field tests and strictly henselian trait tests, on invariant
nonempty connected clopen subschemes surjective over the test base with geometrically
connected generic fibre, detect absolute ampleness over an affine Dedekind base.
The two test hypotheses split the disjunction of allowed test rings. Strict henselianity of
a trait is spelled out as in the node: separably closed residue field, and every simple
residue root of a monic polynomial lifts to a root. For a field the
fraction-field generic fibre is the scheme itself. The displayed factorization uses
exactly the action obtained by the monoidal base-change functor `Over.pullback`.

Source: BLR, Néron Models, §6.4 Proposition 2, initial reductions, pp.153–154
(blueprint: lem-sfb-dedekind-invariant-component-ample-test).

Proof:
1. The empty scheme is quasi-compact and satisfies the ample-locus condition vacuously.
For each prime of D, localize D. Localization is flat by
lem-weil-pbc-localization-flat and lem-weil-pbc-flat-morphism-affine-criterion;
lem-sc-dedekind-localization-dvr makes the non-generic localization a DVR.
2. Over the generic point take a separable closure (lem-pc-field-extension-fpqc-cover).
Over a DVR take its strict henselization. Use
lem-weil-pbc-strict-henselization-local-structure,
lem-weil-pbc-henselian-local-root-lifting and lem-sc-strict-henselization-dvr
for the same ring. Flat local maps are faithfully flat and surjective on spectra by
lem-pc-local-flat-faithful-flat-reflects-surjective and
lem-weil-pbc-faithfully-flat-surjective-spectrum. Affine morphism permanence and
lem-pc-flat-compose make this an allowed flat test and an fpqc cover.
Base change preserves smoothness, separatedness, finite type and invertibility by
lem-pc-proper-base-change, lem-pod-separated-finite-type-base-change and
lem-weil-pbc-invertible-pullback-tensor.
3. The test base is Noetherian and normal, using lem-sc-dvr-dimension-one and
lem-weil-pbc-regular-local-dim-one-iff-normal. The source is Noetherian and normal by
lem-weil-pbc-finite-type-over-noetherian and lem-sfb-smooth-normal-ascent.
By lem-trf-normal-topologically-noetherian-components it is a finite disjoint union
of clopen integral connected components. By lem-pc-smooth-flat and
lem-weil-pbc-flat-lfp-open each component maps openly to the base, hence is either
surjective or lies entirely over the generic point.
4. Each component is invariant: every orbit over the residue field of a point is
connected by geometric connectedness of H's fibres and contains that point by the
unit law. Its image lies in that component. The open-immersion factorization
property gives the required morphism, also after every field extension.
5. For any separably closed field test, lem-pc-dense-separable-points gives a rational
point on every component. The theorem
lem-sbc-connected-rational-point-geometrically-connected makes it geometrically
connected. The field hypothesis and lem-trf-finite-coproduct-ample-with-points,
with no point summands, give ampleness on the full test scheme, including the empty one.
6. A component meeting the closed fibre of a strict trait is surjective. By
lem-sfb-strict-local-sections-meet-dense-fibre-opens it has a section. Its generic
fibre is a nonempty open of an integral scheme, hence connected; the rational-point
geometric-connectedness theorem applies. The trait hypothesis gives ampleness there.
7. For a generic-only component, apply step 5 to a separable closure of the fraction
field; its composite to S is flat. Its inclusion is affine by
lem-trf-closed-embedding-affine. Use lem-weil-pbc-pullback-ample-invertible and
lem-sfb-space-relative-ampleness-fpqc-descent to descend ampleness to the component.
Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to identify the scheme
and algebraic-space versions, preserving line modules and tensor pullbacks.
8. Finite-coproduct ampleness gives ampleness on the entire strict trait test.
The same fpqc descent over the affine local base gives ampleness after localization
at every prime of D. Relative and absolute ampleness agree for affine bases.
9. Express each localization as the filtered colimit of principal localizations by
lem-weil-pbc-localization-colimit-principal-localizations. By
lem-weil-pbc-spec-small-colimit-limit and lem-weil-pbc-limit-fibre-products, the
localized source is the corresponding inverse limit. Transition maps are affine;
finite type over a Noetherian base gives qcqs sources. Apply
lem-trf-ample-affine-limit-descent to get ampleness over a principal neighbourhood.
10. Finitely many such principal neighbourhoods cover Spec D. They form an fpqc
cover. Relative-ampleness descent gives relative ampleness over Spec D, and since
Spec D is affine this is precisely the required absolute ampleness on X. -/
theorem isAmple_of_dedekind_invariant_component_tests
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (hdim : ringKrullDim D ≤ 1)
    (H X : Over (Spec (.of D))) [GrpObj H] [ModObj H X]
    [Smooth H.hom] [IsSeparated H.hom] [LocallyOfFiniteType H.hom]
    [QuasiCompact H.hom] [GeometricallyConnected H.hom]
    [Smooth X.hom] [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (L : X.left.Modules) [L.IsInvertible]
    (hfield : ∀ (R : Type u) [Field R] [IsSepClosed R]
      (t : Spec (.of R) ⟶ Spec (.of D)) [Flat t]
      (Y : Over (Spec (.of R))) (j : Y ⟶ (Over.pullback t).obj X)
      [IsOpenImmersion j.left], IsClosed (Set.range j.left) → ConnectedSpace Y.left →
      Surjective Y.hom → GeometricallyConnected Y.hom →
      (∃ b : (Over.pullback t).obj H ⊗ Y ⟶ Y,
        (𝟙 ((Over.pullback t).obj H) ⊗ₘ j) ≫
          Functor.LaxMonoidal.μ (Over.pullback t) H X ≫
          (Over.pullback t).map (γ[H,X]) = b ≫ j) →
      @IsAmple Y.left ((tensorPullback (j.left ≫ pullback.fst X.hom t)).obj L)
        ((invertible_pullback_tensor (j.left ≫ pullback.fst X.hom t)).1 L).2)
    (htrait : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
      IsSepClosed (IsLocalRing.ResidueField R) →
      (∀ f : Polynomial R, f.Monic → ∀ a₀ : R, f.eval a₀ ∈ IsLocalRing.maximalIdeal R →
        IsUnit (f.derivative.eval a₀) →
        ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R) →
      ∀ (t : Spec (.of R) ⟶ Spec (.of D)) [Flat t]
      (Y : Over (Spec (.of R))) (j : Y ⟶ (Over.pullback t).obj X)
      [IsOpenImmersion j.left], IsClosed (Set.range j.left) → ConnectedSpace Y.left →
      Surjective Y.hom →
      GeometricallyConnected (pullback.snd Y.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) →
      (∃ b : (Over.pullback t).obj H ⊗ Y ⟶ Y,
        (𝟙 ((Over.pullback t).obj H) ⊗ₘ j) ≫
          Functor.LaxMonoidal.μ (Over.pullback t) H X ≫
          (Over.pullback t).map (γ[H,X]) = b ≫ j) →
      @IsAmple Y.left ((tensorPullback (j.left ≫ pullback.fst X.hom t)).obj L)
        ((invertible_pullback_tensor (j.left ≫ pullback.fst X.hom t)).1 L).2) :
    IsAmple X.left L := by
  sorry

end AlgebraicGeometry
