/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Sheaf.RingTheory.GRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import Sheaf.RingTheory.GRingCompletionRegular
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Sheaf.RingTheory.LocalizationRegular
import Sheaf.Paper.NormalLocusOpen
import Sheaf.RingTheory.RegularComposition
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Sheaf.RingTheory.EquivariantMarkedCylinderAlgebraization

/-!
# Partial algebraization with a marking and prime-to-ell degree

Source: ILO, Travaux de Gabber, Expose V, 2.1.2 and 3.1.1--3.1.4, pp. 64--66,
and Expose IX, 1.3, p. 132
(blueprint: lem-per-prime-to-ell-marked-algebraization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A normal complete local scheme has a marked partial algebraization after a finite
prime-to-ell extension. The affine and local-global-section conditions express a local
scheme; integrality is repeated as instance data for its function field and follows from
normality. The completion is explicitly maximal-ideal-adic, and its map to `W` is the
canonical map through the stalk. The function-field algebra is required to induce `p`.
Regularity is tested on the global ring map between the affine schemes, using
`RingHom.IsRegular` (flat with geometrically regular fibres). Equal characteristic is
expressed by equality of the characteristics of the local ring and its residue field;
in that case the selected finite map is literally an identity, after equality of schemes.

Source: ILO, Travaux de Gabber, Expose V, 2.1.2 and 3.1.1--3.1.4, pp. 64--66,
and Expose IX, 1.3, p. 132
(blueprint: lem-per-prime-to-ell-marked-algebraization).

Proof:
1. Write `X = Spec A` and `Z = V(I)`. Use
   lem-per-prime-to-ell-equivariant-cohen-presentation to obtain `A⁺ = Bᴴ`.
   Its finite integral injection gives a finite surjection of prime-to-ell generic degree.
   A finite domain over a complete local ring is complete local. Invariant fractions
   integral over `Bᴴ` lie in the normal ring `B` and are invariant, proving normality.
   In equal characteristic take `A⁺ = A` and the identity.
2. Apply lem-per-equivariant-marked-cylinder-algebraization to `IA⁺`. It supplies a
   quasi-finite algebra over `D[T]`, where `D` is complete regular local of dimension
   `d - 1`, with ell a unit, and identifies the completed marked local ring with `A⁺`.
3. Complete local rings are excellent; finite type and localization preserve excellence.
   Faithful flatness of completion embeds the local ring `L` in `A⁺`. Contracting
   principal ideals proves `L` integrally closed, hence a normal domain.
4. Kill the finitely generated kernel of `C → L` by inverting a product of elements
   outside the marked maximal ideal. This makes the algebra a domain without changing
   its marked completed local ring, finite type, or quasi-finiteness over `D[T]`.
5. Excellent normalization gives a dense normal open. The normal-locus openness lemma
   then gives a principal normal neighbourhood of the marked point. Its spectrum is `W`.
6. The injection `D → A⁺` implies dominance of `W → Spec D`. The marked point is closed
   over the closed point, and ell remains a unit in both coordinate rings.
7. Quasi-finiteness over the affine line and base change bound every fibre dimension by
   one, including empty fibres (dimension minus infinity).
8. Completion preserves dimension, and finite integral injections preserve dimension.
   The universally catenary dimension formula at the marked point, whose residue
   extension is finite, gives generic transcendence degree one. The dimension theorem
   for a finite type domain over a field gives generic fibre dimension one.
9. Excellence makes `L` a G-ring, so `L → completion L` is regular. Localization is
   regular, and composition is regular: fibres outside primes contained in the marked
   maximal ideal are zero, and the other fibres are the Noetherian completion fibres.
10. The algebraized ideal extends to `IA⁺`, proving the equality of inverse-image closed
    sets. It is nonzero because `I` is nonzero and `A → A⁺` injective; thus its zero set
    in the domain defining `W` is nowhere dense. This also covers the empty marking. -/
theorem exists_primeToEll_marked_algebraization
    (ell : ℕ) (hEll : ell.Prime)
    (X : Scheme.{u}) [IsAffine X] [IsIntegral X] [IsNoetherian X]
    [IsLocalRing Γ(X, ⊤)]
    [IsAdicComplete (IsLocalRing.maximalIdeal Γ(X, ⊤)) Γ(X, ⊤)]
    (hNormal : IsNormalScheme X) (d : ℕ) (hd : 2 ≤ d)
    (hDim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hInv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (Z : Set X) (hZ : IsClosed Z) (hRare : IsNowhereDense Z) :
    ∃ (Xplus Y₀ W : Scheme.{u})
      (_ : IsAffine Xplus) (_ : IsIntegral Xplus) (_ : IsNoetherian Xplus)
      (_ : IsLocalRing Γ(Xplus, ⊤))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Γ(Xplus, ⊤)) Γ(Xplus, ⊤))
      (_ : IsAffine Y₀) (_ : IsIntegral Y₀) (_ : IsNoetherian Y₀)
      (_ : IsLocalRing Γ(Y₀, ⊤))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Γ(Y₀, ⊤)) Γ(Y₀, ⊤))
      (_ : IsAffine W) (_ : IsIntegral W) (_ : IsNoetherian W)
      (p : Xplus ⟶ X) (f₀ : W ⟶ Y₀) (w : W) (Z_W : Set W)
      (g : Xplus ⟶ W),
      IsNormalScheme Xplus ∧ IsFinite p ∧ Surjective p ∧
      (∃ (_ : Algebra X.functionField Xplus.functionField),
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Xplus.functionField)) ≫
          X.fromSpecFunctionField = Xplus.fromSpecFunctionField ≫ p ∧
        Nat.Coprime (Module.finrank X.functionField Xplus.functionField) ell) ∧
      IsRegularScheme Y₀ ∧ IsExcellent Γ(Y₀, ⊤) ∧
      topologicalKrullDim Y₀ = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      IsExcellent Γ(W, ⊤) ∧ IsNormalScheme W ∧
      IsDominant f₀ ∧ LocallyOfFiniteType f₀ ∧ QuasiCompact f₀ ∧
      (∀ y : Y₀, topologicalKrullDim (f₀.fiber y) ≤ (1 : WithBot ℕ∞)) ∧
      topologicalKrullDim (f₀.fiber (genericPoint Y₀)) = (1 : WithBot ℕ∞) ∧
      IsClosed ({w} : Set W) ∧ IsClosed ({f₀ w} : Set Y₀) ∧
      IsClosed Z_W ∧ IsNowhereDense Z_W ∧
      (∃ e : Xplus ≅ Spec (.of
          (AdicCompletion (IsLocalRing.maximalIdeal (W.presheaf.stalk w))
            (W.presheaf.stalk w))),
        g = e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (W.presheaf.stalk w)
            (AdicCompletion (IsLocalRing.maximalIdeal (W.presheaf.stalk w))
              (W.presheaf.stalk w)))) ≫ W.fromSpecStalk w) ∧
      p ⁻¹' Z = g ⁻¹' Z_W ∧ RingHom.IsRegular (g.appTop).hom ∧
      (∀ y : Y₀, IsUnit (ell : Y₀.presheaf.stalk y)) ∧
      (∀ v : W, IsUnit (ell : W.presheaf.stalk v)) ∧
      (ringChar Γ(X, ⊤) = ringChar (IsLocalRing.ResidueField Γ(X, ⊤)) →
        ∃ h : Xplus = X, p = eqToHom h) := by
  sorry

end AlgebraicGeometry
