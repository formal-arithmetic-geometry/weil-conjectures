/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth

import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Stalk
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreFlatCriterion
import WeilConjectures.RingTheory.FlatLocalizedModuleBaseChange

/-! # Cohen-Macaulay loci under extension of fields and base change

Source: Stacks Project, Algebra, Tags 00RJ and 00RK
(blueprint: lem-pur-cohen-macaulay-field-extension).

## Main statements

- `stalk_depth_eq_ringKrullDim_iff_of_field_extension`: the absolute pointwise assertion.
- `fibre_depth_eq_ringKrullDim_iff_geometric`: either some or every geometric lift tests
  the ordinary fibre condition.
- `fibre_depth_eq_ringKrullDim_locus_baseChange`: the relative locus pulls back exactly.

Cohen-Macaulayness is expressed using the recorded depth and ring Krull dimension,
with the natural inclusion of `ℕ∞` into `WithBot ℕ∞`. The stalks in question are
Noetherian local rings because the schemes over the relevant fields are locally
of finite type. No assumption is made on the characteristic or separability.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The Cohen-Macaulay condition at a point is invariant under arbitrary field extension.

Source: Stacks Project, Algebra, Tag 00RJ (lemma-extend-field-CM-locus).
(blueprint: lem-pur-cohen-macaulay-field-extension)

Proof (steps 1-7 of the node):
1. Choose an affine finite-type neighbourhood of the image point. A field is Noetherian,
   so its finite-type algebra is finitely presented, and every module over the field is
   flat. The quasi-finite polynomial chart theorem gives an affine neighbourhood with
   a locally finitely presented quasi-finite map to affine n-space, where n is the
   topological dimension at the point. Open restriction preserves this dimension and
   the local rings.
2. Write the chart as A = k[t_1,...,t_n] → C. A finite presentation of C over A also
   gives one over k. Affine fibre products identify its base change with
   A_K = K[t_1,...,t_n] → C_K = C ⊗[k] K. Their stalks are the prime localizations at
   the corresponding primes. The tensor comparison sends c ⊗ (a ⊗ l) to ca ⊗ l,
   with inverse c ⊗ l ↦ c ⊗ (1 ⊗ l).
3. Base change preserves the chart's local quasi-finiteness and finite presentation;
   the new source is flat over K. Dimension at the point is preserved by field
   extension, so the base-changed chart has the same n.
4. Apply the polynomial-chart fibre-flat criterion over k and K. The dimension clauses
   already hold, so the two Cohen-Macaulay conditions are equivalent to flatness of
   the localized chart maps A_p → C_q and (A_K)_pK → (C_K)_qK.
5. Flatness ascends by localized module base change, using the equivalence between
   flatness over a localization and over its original ring.
6. Field-extension base change is faithfully flat. Localization gives flat local
   maps, hence faithfully flat maps on the source stalks. Compose flat maps on the
   polynomial side and descend flatness along C_q → (C_K)_qK using
   `Module.Flat.of_flat_of_faithfullyFlat`.
7. The resulting equivalence of flatness gives the equivalence of Cohen-Macaulayness.
   Affine open neighbourhoods cover every pair of points under consideration. Neither
   ascent nor descent requires separability or finite generation of K over k. -/
theorem stalk_depth_eq_ringKrullDim_iff_of_field_extension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    ((IsLocalRing.depth
        (R := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x')
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x') :
          WithBot ℕ∞) =
      ringKrullDim
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x')) ↔
    (IsLocalRing.depth
        (R := X.presheaf.stalk
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x'))
        (X.presheaf.stalk
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x')) :
          WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x')) := by
  sorry

/-- Ordinary fibre Cohen-Macaulayness is equivalent both to the existence of a
Cohen-Macaulay geometric lift and to Cohen-Macaulayness at every geometric lift.

Source: Stacks Project, Algebra, Tags 00RJ and 00RK; fibre products and ordinary
fibres as in Schemes, Tags 01JO and 01K0, followed by algebraic-closure base change.
(blueprint: lem-pur-cohen-macaulay-field-extension)

Proof (step 8 of the node): For s in S, the ordinary fibre is locally of finite type
over κ(s), as seen by tensoring finite-type affine charts with κ(s). Its geometric
fibre is its base change to a chosen algebraic closure Ω of κ(s). Apply the
field-extension assertion at each point above y: its local ring is Cohen-Macaulay
if and only if the ordinary fibre local ring at y is Cohen-Macaulay. There is a
lift of every y: on an affine neighbourhood field-extension base change is
faithfully flat and its map on spectra is surjective. Thus both the existential
test and the universal test give precisely the ordinary locus. This also handles
an arbitrary choice of algebraic closure. -/
theorem fibre_depth_eq_ringKrullDim_iff_geometric
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (y : f.fiber s)
    (Ω : Type u) [Field Ω] [Algebra (S.residueField s) Ω]
    [IsAlgClosure (S.residueField s) Ω] :
    (((IsLocalRing.depth (R := (f.fiber s).presheaf.stalk y)
          ((f.fiber s).presheaf.stalk y) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber s).presheaf.stalk y)) ↔
      ∃ z : (pullback (f.fiberToSpecResidueField s)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω))) : Scheme.{u}),
        (pullback.fst (f.fiberToSpecResidueField s)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))) z = y ∧
        (IsLocalRing.depth
            (R := (pullback (f.fiberToSpecResidueField s)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))).presheaf.stalk z)
            ((pullback (f.fiberToSpecResidueField s)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))).presheaf.stalk z) :
                WithBot ℕ∞) =
          ringKrullDim ((pullback (f.fiberToSpecResidueField s)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))).presheaf.stalk z)) ∧
    (((IsLocalRing.depth (R := (f.fiber s).presheaf.stalk y)
          ((f.fiber s).presheaf.stalk y) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber s).presheaf.stalk y)) ↔
      ∀ z : (pullback (f.fiberToSpecResidueField s)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω))) : Scheme.{u}),
        (pullback.fst (f.fiberToSpecResidueField s)
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))) z = y →
        (IsLocalRing.depth
            (R := (pullback (f.fiberToSpecResidueField s)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))).presheaf.stalk z)
            ((pullback (f.fiberToSpecResidueField s)
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))).presheaf.stalk z) :
                WithBot ℕ∞) =
          ringKrullDim ((pullback (f.fiberToSpecResidueField s)
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)))).presheaf.stalk z)) :=
  by
  sorry

/-- The relative Cohen-Macaulay locus commutes with any Noetherian base change.

Source: Stacks Project, Algebra, Tag 00RK (lemma-CM-locus-commutes-base-change).
(blueprint: lem-pur-cohen-macaulay-field-extension)

Proof (step 9 of the node): For x' in X ×_S S', put s' = f'(x'), s = g(s'),
and x = p(x'). The residue-field map κ(s) → κ(s') is a field extension. The
universal property of fibre products identifies the fibre X'_{s'} with
X_s ×_{Spec κ(s)} Spec κ(s'), compatibly with x' and x: a map into either side
is a map to X and a map to Spec κ(s') having equal composites to S.
The fibre X_s is locally of finite type over κ(s). Apply the field-extension
assertion to this fibre and κ(s')/κ(s). Its pointwise equivalence says exactly
that x' belongs to the new relative locus if and only if p(x') belongs to the
old one, proving the displayed equality of sets. -/
theorem fibre_depth_eq_ringKrullDim_locus_baseChange
    {X S S' : Scheme.{u}} [IsNoetherian X] [IsNoetherian S] [IsNoetherian S']
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) :
    {x' : (pullback f g : Scheme.{u}) |
      (IsLocalRing.depth
          (R := ((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
            ((pullback.snd f g).asFiber x'))
          (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
            ((pullback.snd f g).asFiber x')) : WithBot ℕ∞) =
        ringKrullDim (((pullback.snd f g).fiber ((pullback.snd f g) x')).presheaf.stalk
          ((pullback.snd f g).asFiber x'))} =
      (pullback.fst f g) ⁻¹' {x : X |
        (IsLocalRing.depth (R := (f.fiber (f x)).presheaf.stalk (f.asFiber x))
            ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))} := by
  sorry

end AlgebraicGeometry
