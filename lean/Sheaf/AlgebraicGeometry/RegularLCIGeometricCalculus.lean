/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.RingTheory.FiniteSpectrumMaximalPrimes
import Sheaf.AlgebraicGeometry.SmoothPairRegularEquations
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.RingTheory.SmoothConormalSequenceExact
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Regular immersions and intrinsic virtual dimension

Source: Stacks Project, Divisors, Tags 0E9J, 067P, 067Q, 067R; Algebra,
Tags 00NR, 061L, 00LN, 065K, 06A9, 00ON; Morphisms, Tags 02FX, 02G1, 01T2,
01TG, 01TH (blueprint: lem-per-regular-lci-geometric-calculus).

The dimension formula uses finite witnesses and integer subtraction. Codimension and
smooth relative dimension may vary between components. Every pointwise assertion permits
an empty source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An immersion of regular Noetherian schemes is regular, expressed after factoring through
an open ambient scheme. Source: Stacks, Divisors, Tag 0E9J
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Steps 1 and 2): factor the immersion as closed followed by open. At a source
point the ambient and quotient local rings are regular. Apply
`lem-weil-pbc-regular-local-quotient-kernel-parameters`, then
`lem-weil-pbc-regular-local-generators-regular-sequence` to its parameter prefix. Clear
its finitely many denominators on an affine neighbourhood and apply
`lem-exc-regular-sequence-principal-neighbourhood`. Invert one further element outside
this prime to make the generators generate the whole defining ideal. Localization
preserves the multiplication injections, and the final quotient remains nonzero at
this point. Conormal freeness makes the resulting length independent of equations. -/
theorem exists_regularClosedImmersion_factor_of_regular
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Y ⟶ X) [IsImmersion i] (hY : IsRegularScheme Y) (hX : IsRegularScheme X) :
    ∃ (U : X.Opens) (j : Y ⟶ U.toScheme) (c : Y → ℕ),
      j ≫ U.ι = i ∧ IsRegularClosedImmersionWithCodimension j c := by
  sorry

/-- Codimension is locally constant, is the rank of the conormal stalk, and is independent
of regular equations. Source: Stacks, Algebra, Tag 00LN; Divisors, Tags 063D, 063J
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 2): local regular generators give a basis of the conormal by
`lem-weil-pbc-regular-sequence-conormal-free`; localize the basis at each source point.
The stalk conormal is the cotangent module of the kernel of the surjective stalk map,
over the quotient local ring. This gives its finite rank and shows that the generator
length is constant on a neighbourhood. Reducing any two free-module bases modulo the
maximal ideal proves equality of their lengths and hence uniqueness of `c`. -/
theorem regularClosedImmersion_codimension_rank_unique
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (i : Y ⟶ X) (c : Y → ℕ) (hi : IsRegularClosedImmersionWithCodimension i c) :
    IsLocallyConstant c ∧
      (∀ y : Y, Module.finrank
        (X.presheaf.stalk (i y) ⧸ RingHom.ker (i.stalkMap y).hom)
        (RingHom.ker (i.stalkMap y).hom).Cotangent = c y) ∧
      ∀ d : Y → ℕ, IsRegularClosedImmersionWithCodimension i d → d = c := by
  sorry

/-- Flat base change preserves regular closed immersions and their codimension function.
Source: Stacks, Divisors, Tag 067P (blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 3): on affine charts tensor each multiplication injection for the regular
sequence with the flat base algebra, using `lem-weil-pbc-flat-tensor-exact`. The quotient
base-change isomorphism `lem-weil-pbc-tensor-quotient-base-change` identifies the resulting
maps with multiplication by the images of the equations. At points of the pullback,
`lem-weil-pbc-weakly-regular-sequence-localization-prime` gives regularity, including the
nonzero quotient condition. Spread to neighbourhoods as in Step 2. Conormal freeness
identifies the new rank with the old length. No flatness of the quotient is required. -/
theorem regularClosedImmersion_flat_baseChange
    {Y X X' : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X] [IsNoetherian X']
    (i : Y ⟶ X) (g : X' ⟶ X) [Flat g] (c : Y → ℕ)
    (hi : IsRegularClosedImmersionWithCodimension i c) :
    IsRegularClosedImmersionWithCodimension (pullback.snd i g)
      (fun y ↦ c (pullback.fst i g y)) := by
  sorry

/-- Composition preserves regular closed immersions and adds their codimensions.
Source: Stacks, Divisors, Tag 067Q; Algebra, Tag 065K
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 4): locally choose regular generators `a` for `j` and regular generators
`b` for `i` in the quotient by `a`. Lift the `b` to the ambient ring. The concatenated
list generates the composite ideal. Its initial multiplication tests are those of `a`;
its later tests are those of `b` in the quotient. Its final quotient is the nonzero
smallest local ring. Spread as in Step 2, and apply conormal freeness to obtain the sum
of the two lengths. -/
theorem regularClosedImmersion_comp_codimension
    {Z Y X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] [IsNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) (c : Z → ℕ) (d : Y → ℕ)
    (hi : IsRegularClosedImmersionWithCodimension i c)
    (hj : IsRegularClosedImmersionWithCodimension j d) :
    IsRegularClosedImmersionWithCodimension (i ≫ j) (fun z ↦ c z + d (i z)) := by
  sorry

/-- A section of a separated smooth morphism of relative dimension `r` is a regular
closed immersion of codimension `r`. Source: Stacks, Divisors, Tag 067R; Algebra, Tag 06A9
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 5): `lem-weil-pbc-section-separated-closed-immersion` gives closedness.
Both the identity of the base and the given map are smooth, so
`lem-pur-smooth-pair-regular-immersion` supplies regular equations for the section.
On affine charts write the section as a split algebra map with kernel `J`.
`lem-weil-pbc-smooth-conormal-sequence-exact` identifies `J/J²` with the pullback of smooth
differentials. By `lem-sc-smooth-omega-finite-locally-free` their rank is `r`. Conormal
freeness identifies this with the equation length. This also proves the case `r = 0`. -/
theorem regularClosedImmersion_smooth_section
    {S V : Scheme.{u}} [IsNoetherian S] [IsNoetherian V]
    (p : V ⟶ S) (r : ℕ) [IsSeparated p] [SmoothOfRelativeDimension r p]
    (s : S ⟶ V) (hs : s ≫ p = 𝟙 S) :
    IsRegularClosedImmersionWithCodimension s (fun _ ↦ r) := by
  sorry

/-- Smoothness preserves regularity over a regular Noetherian base.
Source: Stacks, Algebra, Tag 07NF (blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 6): on compatible affine charts, smoothness gives smooth ring maps and
regularity of the base gives regular Noetherian chart rings. Apply
`lem-weil-pbc-regular-ring-smooth-ascent` to obtain regular target chart rings. This is
regularity of the source scheme. In particular it applies to affine space, whose
projection is smooth by `sbc-lem-affine-space-smooth`. -/
theorem isRegularScheme_of_smooth_over_regular
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (f : Y ⟶ X) [Smooth f] (hX : IsRegularScheme X) : IsRegularScheme Y := by
  sorry

/-- A finite-type map of regular affine schemes has an affine-space closed presentation;
every such presentation is regular. Source: Stacks, Morphisms, Tag 01T2; Divisors, Tag 0E9J
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Steps 6 and 7): write the map as `Spec B → Spec A`.
`lem-weil-pbc-lft-affine-pairs` gives finite generation of `B` as an `A`-algebra.
Choose finitely many generators: polynomial evaluation is surjective, and its spectrum
gives the closed immersion over `X`. Affine space is regular by smooth ascent and
`sbc-lem-affine-space-smooth`. Apply the regular-immersion result of Steps 1 and 2 to
any closed presentation, since its source and ambient scheme are regular. -/
theorem regular_affine_finiteType_closed_presentation
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X] [IsAffine Y] [IsAffine X]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : IsRegularScheme Y) (hX : IsRegularScheme X) :
    (∃ (r : ℕ) (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) X),
      i ≫ (AffineSpace (ULift.{u} (Fin r)) X ↘ X) = f ∧ IsClosedImmersion i) ∧
    ∀ (r : ℕ) (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) X),
      i ≫ (AffineSpace (ULift.{u} (Fin r)) X ↘ X) = f → IsClosedImmersion i →
        ∃ c : Y → ℕ, IsRegularClosedImmersionWithCodimension i c := by
  sorry

/-- The virtual dimension of a regular-closed/smooth factorization is locally constant
and equals the intrinsic local-dimension expression. Source: Stacks, Algebra, Tag 00ON;
Morphisms, Tags 02FX, 02G1; ILO XVI, Definitions 2.5.1–2.5.3
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Steps 8 and 9): at `z = i(y)`, apply
`lem-weil-pbc-flat-height-formula` to the flat Noetherian local map of the smooth morphism.
`lem-sbc-scheme-fibre-stalk-quotient` identifies its fibre quotient with the fibre stalk.
`lem-kun-dimension-formula` on a finite-type field chart of that fibre gives
`dim O_P,z + trdeg κ(z)/κ(x) = dim O_X,x + r(z)`. Localize the regular equations of `i`
using `lem-weil-pbc-weakly-regular-sequence-localization-prime` and apply
`lem-trf-regular-sequence-dimension-formula` to obtain `dim O_Y,y + c(y) = dim O_P,z`.
The closed-immersion stalk map identifies the residue fields of `z` and `y`.
`lem-weil-pbc-noetherian-local-finite-krull-dimension` makes the dimensions finite;
finite type makes the residue transcendence degree finite. Rearrange in the integers.
Conormal rank gives local constancy of `c`, and
`sbc-lem-smooth-relative-dimension-locally-constant` gives that of `r`. Empty sources and
zero lengths require no separate nonemptiness or positivity assumption (node Step 11). -/
theorem regular_lci_virtual_dimension_formula
    {Y X P : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X] [IsNoetherian P]
    [IsAffine Y] [IsAffine X] (f : Y ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : IsRegularScheme Y) (hX : IsRegularScheme X)
    (i : Y ⟶ P) (p : P ⟶ X) [Smooth p] (hi : i ≫ p = f)
    (c : Y → ℕ) (hc : IsRegularClosedImmersionWithCodimension i c)
    (r : P → ℕ) (hr : ∀ z : P,
      topologicalKrullDimAt (p.asFiber z) = (r z : WithBot ℕ∞)) :
    IsLocallyConstant (fun y : Y ↦ (r (i y) : ℤ) - (c y : ℤ)) ∧
      ∀ y : Y, ∃ dx dy t : ℕ,
        ringKrullDim (X.presheaf.stalk (f y)) = (dx : WithBot ℕ∞) ∧
        ringKrullDim (Y.presheaf.stalk y) = (dy : WithBot ℕ∞) ∧
        @Algebra.trdeg (X.residueField (f y)) (Y.residueField y) _ _
          (f.residueFieldMap y).hom.toAlgebra = (t : Cardinal) ∧
        (r (i y) : ℤ) - (c y : ℤ) = (dy : ℤ) - (dx : ℤ) + (t : ℤ) := by
  sorry

/-- Two regular-closed/smooth factorizations give the same virtual dimension.
Source: ILO XVI, Definitions 2.5.1–2.5.3 and the Stacks dimension formulas above
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 9): apply the intrinsic formula to both factorizations at the same
source point. The two local-ring dimensions and the canonical residue extension depend
only on `f` and the point. The finite witnesses of their Krull dimensions and cardinal
transcendence degree are unique, so both integer differences agree. The argument is
pointwise and is vacuous on the empty source, as in node Step 11. -/
theorem regular_lci_virtual_dimension_independent
    {Y X P Q : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    [IsNoetherian P] [IsNoetherian Q] [IsAffine Y] [IsAffine X]
    (f : Y ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : IsRegularScheme Y) (hX : IsRegularScheme X)
    (i : Y ⟶ P) (p : P ⟶ X) [Smooth p] (hi : i ≫ p = f)
    (j : Y ⟶ Q) (q : Q ⟶ X) [Smooth q] (hj : j ≫ q = f)
    (c d : Y → ℕ) (hc : IsRegularClosedImmersionWithCodimension i c)
    (hd : IsRegularClosedImmersionWithCodimension j d)
    (r : P → ℕ) (s : Q → ℕ)
    (hr : ∀ z : P, topologicalKrullDimAt (p.asFiber z) = (r z : WithBot ℕ∞))
    (hs : ∀ z : Q, topologicalKrullDimAt (q.asFiber z) = (s z : WithBot ℕ∞)) :
    ∀ y : Y, (r (i y) : ℤ) - (c y : ℤ) = (s (j y) : ℤ) - (d y : ℤ) := by
  sorry

/-- A quasi-finite morphism has finite residue extensions and residue transcendence degree
zero. Both the node's finite-fibre convention and Stacks quasi-finiteness are accepted.
Source: Stacks, Morphisms, Tags 01TG, 01TH; Algebra, Tag 0ALW
(blueprint: lem-per-regular-lci-geometric-calculus).

Proof (node Step 10): for a finite-type morphism with finite fibres, every affine fibre
chart is a finite-type field algebra with finite spectrum.
`lem-pqf-finite-spectrum-maximal-primes` makes all its primes maximal. Every point of the
finite fibre is closed, hence also open. In the Stacks formulation isolation is given.
`lem-weil-pbc-isolated-fibre-point-residue-finite` now gives finite residue extensions.
In a finite-dimensional field extension the powers of each element are linearly
dependent, so the extension is algebraic and its transcendence degree is zero.
There are no source points to check in the empty case (node Step 11). -/
theorem finite_residue_extension_trdeg_zero_of_quasiFinite
    {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X] (f : Y ⟶ X)
    (hf : (LocallyOfFiniteType f ∧ QuasiCompact f ∧ f.HasFiniteFibres) ∨ f.IsQuasiFinite) :
    ∀ y : Y,
      @FiniteDimensional (X.residueField (f y)) (Y.residueField y) _ _
        (f.residueFieldMap y).hom.toAlgebra.toModule ∧
      @Algebra.trdeg (X.residueField (f y)) (Y.residueField y) _ _
        (f.residueFieldMap y).hom.toAlgebra = 0 := by
  sorry

end AlgebraicGeometry
