/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Sheaf.AlgebraicGeometry.GeometricDimensionFunction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.CohenGabberFinitePresentations
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.RingTheory.FiniteHenselianAlgebraLocalModel
import Sheaf.RingTheory.WeierstrassHenselianCylinder
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.RingTheory.GRingCompletionRegular
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.LocalDimensionFunctionCalculus
import Sheaf.AlgebraicGeometry.RegularStrictLocalModel
import Sheaf.RingTheory.ElkikFiniteEtaleAwayCompletion

/-!
# Gabber's partial algebraization of complete normal strictly local schemes

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose V, 3.1.3 and Remark 3.1.4;
Expose XVII, final paragraph of 6.5, printed p. 300
(blueprint: lem-per-gabber-partial-algebraization).

The input local scheme is written `Spec A`. The base is `Spec D`. The completed strict
localization is the spectrum of the maximal-ideal completion of the published
`Scheme.strictHenselizationRing z`. The regular map is its canonical completion map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Partial algebraization, with a finite normal cover and a regular complete base of dimension
one less. Normality of a local domain is `IsDomain` together with `IsIntegrallyClosed`.
An isomorphism for the finite cover in equal characteristic allows transport of all the data
to the identity cover. The isomorphism `e` identifies the actual completion morphism with
`e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _))`, so regularity is asserted for the
canonical completion map, rather than for an unspecified morphism.

Source: ILO, Expose V, 3.1.3 and Remark 3.1.4; Expose XVII, final paragraph of 6.5, p. 300
(blueprint: lem-per-gabber-partial-algebraization).

Proof:
1. Apply `lem-per-cohen-gabber-finite-presentations` to A. It gives an injective finite
   map A → A' with A' normal and a generically etale power-series presentation over a field
   or a complete discrete valuation ring. In equal characteristic take A' = A. By
   `lem-weil-pbc-finite-over-complete-local-product`, A' is complete local Noetherian.
   Finiteness gives integrality (`pqf-lem-finite-integral-lft`); injective lying over
   (`lem-weil-pbc-integral-injective-lying-over`) gives surjectivity on spectra.
   The base D with the last power-series variable removed has dimension d - 1, is complete
   regular local Noetherian, and has residue characteristic different from ell.
2. Multiply the etale denominator by the last variable. Etale composition and cancellation
   (`lem-weil-pbc-etale-composition-cancellation`) preserve the etale-away property.
   `lem-per-weierstrass-henselian-cylinder` supplies a distinguished polynomial g and a
   Noetherian henselian cylinder H whose g-adic and maximal-ideal completions are the original
   power-series ring. The coordinate change identifies the etale open with D(g).
3. `lem-per-elkik-finite-etale-away-completion` descends the finite algebra A' to a finite
   H-algebra C whose completed tensor product is A'.
4. `lem-per-finite-henselian-algebra-local-model` makes C a Noetherian strictly henselian
   local ring and realizes Spec C as the strict localization of a finite-type D-scheme Z
   at a geometric point z. The separably closed residue field and nonzero local completed
   tensor product give exactly that lemma's hypotheses.
5. `lem-weil-pbc-completion-finite-extension` identifies the completed tensor product with
   the maximal-ideal completion of C. The unique prime over the maximal ideal follows from
   `lem-weil-pbc-finite-algebra-local-radical`, integrality, and
   `lem-weil-pbc-integral-prime-over-maximal-maximal`. This yields e with its canonical
   completion morphism.
6. D is excellent by `lem-per-complete-local-excellence`. Finite-type excellence
   (`lem-exc-finite-type-localization-excellent`) and `lem-per-regular-strict-local-model`
   applied to the identity of Z give excellence and Noetherianity of its strict localization.
   Its G-ring property gives regularity of the canonical completion map by
   `lem-weil-pbc-g-ring-completion-regular`.
7. Excellence implies universal catenarity; `lem-per-local-dimension-function-calculus`
   supplies a dimension function on the local scheme Spec C. This gives all conclusions.
-/
theorem gabber_partial_algebraization
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [IsStrictlyHenselianLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hExcellent : IsExcellent A) (ell : ℕ) (hPrime : ell.Prime)
    (hInvertible : IsUnit (ell : A)) (d : ℕ) (hd : 2 ≤ d)
    (hDimension : topologicalKrullDim (Spec (.of A)) = (d : WithBot ℕ∞)) :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ Spec (.of A)) (D : CommRingCat.{u})
      (_ : IsLocalRing D) (_ : IsNoetherianRing D)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal D) D)
      (Z : Scheme.{u}) (f : Z ⟶ Spec D)
      (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (z : Spec (.of Ω) ⟶ Z)
      (_ : IsLocalRing (Scheme.strictHenselizationRing z))
      (e : X' ≅ Spec (.of (AdicCompletion
        (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing z))
        (Scheme.strictHenselizationRing z)))),
      IsFinite p ∧ Surjective p ∧
      (∀ x : X', IsDomain (X'.presheaf.stalk x) ∧
        IsIntegrallyClosed (X'.presheaf.stalk x)) ∧
      IsExcellent D ∧ IsRegularScheme (Spec D) ∧
      topologicalKrullDim (Spec D) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      IsUnit (ell : D) ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      IsNoetherianRing (Scheme.strictHenselizationRing z) ∧
      IsExcellent (Scheme.strictHenselizationRing z) ∧
      (∃ δ : Scheme.strictHenselizationScheme z → ℤ,
        Scheme.IsGeometricDimensionFunction (Scheme.strictHenselizationScheme z) δ) ∧
      RingHom.IsRegular (algebraMap (Scheme.strictHenselizationRing z)
        (AdicCompletion (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing z))
          (Scheme.strictHenselizationRing z))) ∧
      (ringChar A = ringChar (IsLocalRing.ResidueField A) → IsIso p) := by
  sorry

end AlgebraicGeometry
