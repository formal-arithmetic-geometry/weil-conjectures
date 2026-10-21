/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Regular.RegularSequence
public import Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover

/-!
# Centred affine coordinates for a smooth section

Source: blueprint main-20261015, sk-thm-dnc, Local construction; Stacks Tags 054L,
024T, 067U, 00LN and 0633 (blueprint: lem-trf-smooth-section-centred-coordinates).

The chart witness packages the affine neighbourhoods, the actual etale map and its
coordinate functions. Its conormal frame and monomial formulas use the published
conormal algebra and symmetric comparison, including their restriction maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SmoothSectionCentredCoordinates

/-- One centred affine chart, with the algebra and monomial conclusions, for the section.
Here `T` and `U` are affine opens of the original schemes. The containment `mapsInto`
identifies `U` with an open in the base change to `T`, and `sectionPreimage` says that
its intersection with the section is exactly `T`. The Cartesian zero square specifies
the scheme-theoretic zero fibre. The coordinate ring map is polynomial evaluation in
the actual pullbacks of the standard affine-space coordinates.

The conormal basis lives on `s ⁻¹ᵁ U`, which is the very same open as `T`. Products of its
images under the symmetric-algebra inclusion are sent by the canonical comparison to
the classes of the coordinate monomials. Those classes are sections of the fixed
degree pieces, so the formulas commute with restrictions, including on overlaps.
Source: sk-thm-dnc, Local construction; Stacks Tags 054L, 024T, 00LN, 0631--0633
(blueprint: lem-trf-smooth-section-centred-coordinates). -/
structure Chart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S)
    (s : S ⟶ V) [IsClosedImmersion s] where
  T : S.affineOpens
  U : V.affineOpens
  mapsInto : U.1 ≤ g ⁻¹ᵁ T.1
  openInBaseChange : IsOpenImmersion
    (pullback.lift U.1.ι (g.resLE T.1 U.1 mapsInto) (g.resLE_comp_ι mapsInto).symm)
  sectionInto : T.1 ≤ s ⁻¹ᵁ U.1
  sectionPreimage : s ⁻¹ᵁ U.1 = T.1
  e : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) T.1.toScheme
  over : e ≫ (AffineSpace (ULift.{u} (Fin d)) T.1.toScheme ↘ T.1.toScheme) =
    g.resLE T.1 U.1 mapsInto
  etale : Etale e
  separated : IsSeparated e
  zeroFiber : IsPullback (s.resLE U.1 T.1 sectionInto) (𝟙 T.1.toScheme) e
    (AffineSpace.homOfVector (𝟙 T.1.toScheme) (fun _ ↦ 0))
  x : Fin d → Γ(V, U.1)
  coordinates : ∀ j : Fin d,
    x j = U.1.topIso.hom (e.appTop (AffineSpace.coord T.1.toScheme (ULift.up j)))
  algebraEtale : (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x).Etale
  algebraFlat : (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x).Flat
  sectionIdeal : Ideal.map (MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x)
    (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) Γ(S, T.1)))) =
      s.ker.ideal U
  quotient : Γ(V, U.1) ⧸ s.ker.ideal U ≃+* Γ(S, T.1)
  augmentation : ∀ b : Γ(V, U.1),
    quotient (Ideal.Quotient.mk (s.ker.ideal U) b) = s.appLE U.1 T.1 sectionInto b
  regular : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn x)
  coordinateLift : Fin d → (ConormalGradedAlgebra.power s 1).val.obj (op U.1)
  coordinateLift_value : ∀ j : Fin d,
    (ConormalGradedAlgebra.powerInclusion s 1).val.app (op U.1) (coordinateLift j) = x j
  conormalBasis : Module.Basis (Fin d) Γ(S, s ⁻¹ᵁ U.1)
    ((ConormalGradedAlgebra.piece s 1).val.obj (op (s ⁻¹ᵁ U.1)))
  conormalBasis_value : ∀ j : Fin d,
    conormalBasis j = ConormalGradedAlgebra.representative s 1 U.1 (coordinateLift j)
  monomials : ∀ α : Fin d →₀ ℕ,
    ∃ a : (ConormalGradedAlgebra.power s α.degree).val.obj (op U.1),
      (ConormalGradedAlgebra.powerInclusion s α.degree).val.app (op U.1) a =
          α.prod (fun j k ↦ x j ^ k) ∧
      (ConormalGradedAlgebra.symmetricComparison s).right.hom.app (op (s ⁻¹ᵁ U.1))
          (α.prod (fun j k ↦
            (@id ((SymmetricAlgebraSheaf.algebra (ConormalGradedAlgebra.piece s 1)).right.obj.obj
              (op (s ⁻¹ᵁ U.1)))
              ((SymmetricAlgebraSheaf.inclusion (ConormalGradedAlgebra.piece s 1)).val.app
                (op (s ⁻¹ᵁ U.1)) (conormalBasis j))) ^ k)) =
        ConormalGradedAlgebra.homogeneousClass s
          (ConormalGradedAlgebra.presentation s).algebra
          (ConormalGradedAlgebra.presentation s).inclusion α.degree U.1 a

/-- A smooth separated finite-type map with a closed section has a Zariski affine cover
with centred separated etale coordinates, regular coordinate sequence and the specified
conormal monomial description. The section is regular of codimension `d`, its conormal
module is locally free of rank `d`, and its canonical symmetric comparison is invertible.
Source: sk-thm-dnc, Local construction; Stacks Tags 054L, 024T, 067U, 00LN and 0633
(blueprint: lem-trf-smooth-section-centred-coordinates).

Proof:
1. At `s(t)`, use lem-sc-standard-smooth-local-relative-dimension and
   lem-sc-standard-smooth-etale-polynomial-chart to get an etale chart of dimension `d`.
2. Refine the base inside the inverse image of the source chart, using affine opens as
   a basis and affine fibre products. Translate each coordinate by its value on the
   section. Etale base change and composition preserve the chart; its affine source
   makes it separated.
3. Its zero fibre is separated etale over the base, and the section is clopen there by
   lem-weil-pbc-etale-section-clopen-immersion. Remove the closed complementary component.
4. Choose an affine source neighbourhood of `s(t)`, then an affine base neighbourhood
   inside its inverse image, and take their affine fibre product. The zero square stays
   Cartesian. These base opens cover `S`; take the empty cover when `S` is empty.
5. The affine etale ring map is flat. Its zero fibre has ring `B/(x)`, identified with
   the base ring by the section augmentation; this gives exactly the section ideal.
6. Multiplication by each variable is injective modulo earlier variables in a polynomial
   ring. Apply lem-trf-flat-tensor-preserves-injection to get coordinate regularity in
   `B`. The final quotient is the nonzero base chart ring. This includes the empty list.
7. Apply lem-pur-regular-sequence-graded-polynomial: degree-one coordinate classes and
   all homogeneous coordinate monomials are bases of the respective graded pieces.
8. These local equations give IsRegularClosedImmersionWithCodimension. The affine
   conormal comparison and lem-sc-affine-conormal-frame give locally free rank `d`.
9. The canonical comparison of lem-pur-conormal-graded-algebra is polynomial evaluation
   on each affine chart by the symmetric-algebra affine comparison and its free-module
   polynomial description. It sends each basis monomial to its coordinate monomial class.
10. All these formulas use the single sheaf comparison, hence commute with restriction.
    The quasi-coherent iso-on-affine-cover theorem makes it globally invertible.
    For `d = 0`, both graded algebras are the base ring in degree zero and zero above. -/
theorem exists_centred_coordinates {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    (∃ (A : Type u) (c : A → Chart d g s), ⨆ a, (c a).T.1 = ⊤) ∧
      IsRegularClosedImmersionWithCodimension s (fun _ ↦ d) ∧
      (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison s) := by
  sorry

end AlgebraicGeometry.SmoothSectionCentredCoordinates
