/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.VeryTameDivisorialAction
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.EffectiveQCartierWeilDivisor
public import Sheaf.TraceFormula.Modification
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.FaithfullyFlatNormalRingDescent
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingNormal
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-! # Invariant boundaries on very tame finite quotients

Source: ILO, Travaux de Gabber, VIII 5.3.8, p.125; eigenparameters in VIII 5.3.5;
strict local invariant quotients in VIII 5.4.1
(blueprint: lem-per-very-tame-boundary-quotient-cartier).

The four auxiliary definitions specify the reduced image, the actual ideal of a
boundary in the geometric stalk, and its inertia order and invariant subring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closed image of a boundary. For a finite map its support is the
set-theoretic image, since finite maps are closed.
Source: ILO VIII 5.3.8 (blueprint: lem-per-very-tame-boundary-quotient-cartier). -/
def quotientBoundaryIdeal {X Y : Scheme.{u}} (q : X ⟶ Y) (B : X.IdealSheafData) :
    Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure (q '' (B.support : Set X)))

/-- The extended boundary ideal in the actual geometric stalk. Its generators
are germs of functions vanishing on the pullback of the closed subscheme.
Source: ILO VIII 5.3.8 (blueprint: lem-per-very-tame-boundary-quotient-cartier). -/
def boundaryStrictLocalIdeal {X : Scheme.{u}} (B : X.IdealSheafData)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    Ideal (strictLocalRing X t) :=
  Ideal.span {r | ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (s : Γ(W.left, ⊤)), (pullback.fst W.hom B.subschemeι).appTop s = 0 ∧
      strictLocalGerm X t W w s = r}

/-- The order of geometric inertia; ordinary point stabilizers are not substituted.
Source: ILO VIII 5.3.8 (blueprint: lem-per-very-tame-boundary-quotient-cartier). -/
def boundaryInertiaOrder {X : Scheme.{u}} {G : Type v} [Group G]
    (a : G →* Aut X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : ℕ :=
  Nat.card {g : G // t ≫ (a g).hom = t}

/-- The actual fixed subring of the strict local ring under geometric inertia.
It is the intersection of equalizers of the canonical automorphism maps with identity.
Source: ILO VIII 5.4.1 (blueprint: lem-per-very-tame-boundary-quotient-cartier). -/
def boundaryInvariantRing {X : Scheme.{u}} {G : Type v} [Group G]
    (a : G →* Aut X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) : Subring (strictLocalRing X t) :=
  ⨅ (g : G) (hg : t ≫ (a g).hom = t),
    (automorphismStrictLocalMap (a g) t hg).eqLocus (RingHom.id _)

/-- The quotient image of an invariant SNC subboundary is the support of an effective
Q-Cartier Weil divisor. Its reduced inverse image under a regular modification is a
union of ambient normal-crossings components, normal crossings itself, and strict if
the ambient divisor is strict. After adjoining the inertia roots of unity the boundary
has an eigen-equation whose inertia-order power cuts out a Cartier divisor downstairs.

Source: ILO VIII 5.3.8, p.125, using VIII 5.3.5 and 5.4.1
(blueprint: lem-per-very-tame-boundary-quotient-cartier).

Proof:
1. Use lem-per-finite-quotient-strict-local-invariants to identify the quotient stalk
   with A^H and obtain finiteness and Noetherianity. Use
   lem-per-regular-boundary-divisorial-chart and lem-sc-strict-henselization-regular
   for the regular fs chart. The regular-local-localization and regular-ring-normal
   lemmas make A normal. An integral fraction in Frac(A^H) lies in A and is fixed,
   hence lies in A^H. Faithfully flat strict henselization and
   lem-sfb-faithfully-flat-normal-ring-descent give normality of Y; strict
   henselization is Noetherian by lem-sc-strict-henselization-noetherian.
2. Apply lem-per-very-tame-equivariant-sharp-chart. Its eigenparameters differ by units
   from regular boundary parameters. The UFD boundary factorization gives an equation
   u times their product with nonnegative exponents. Reducedness, including after
   etale pullback by lem-trf-etale-reduced-cartier-descent, makes the exponents zero
   or one. Their selected product b is an eigenvector and b^N is fixed. The empty
   product is 1.
3. Finiteness gives integrality. Incomparability and going down for normal integral
   extensions identify heights; lying over supplies a height-one prime upstairs
   over each such prime downstairs. The normal decomposition and admissible affine
   invariant charts show that every image boundary component has codimension one.
   They define the reduced effective Weil divisor E.
4. Set c=b^N in A^H. It is a non-zero-divisor. Lying over and primality give
   c in p iff b in a prime above p, so its zero set is exactly the boundary image.
5. By lem-trf-normal-domain-principal-divisor-kernel the height-one local rings are
   DVRs. Write e_i for the ramification index at each selected parameter prime.
   Units map to units, so the orders of fractions multiply by e_i. For
   f=product(t_i^e_i), the invariant f^N has coefficient N at each downstairs
   boundary component and zero elsewhere, by the UFD boundary factorization.
6. N divides |G|. Raising the preceding equation to |G|/N gives local equations
   of |G|E at all strict local points. Apply
   lem-per-weil-divisor-strict-local-cartier-test to obtain one global effective
   Cartier divisor of this Weil divisor, with the asserted local equations.
7. Pull it back along the modification. Its equations remain nonzero at generic
   points and hence in the regular domain stalks, so the pullback is Cartier.
   Its support is the inverse image of D, contained in the ambient transformed boundary.
8. On normal-crossings etale charts use lem-sfb-etale-stalk-invariants for regularity
   and the UFD boundary factorization to express the pullback equation as a unit
   times parameter powers. Its radical is the selected reduced parameter product.
   Etale reduced Cartier descent makes these the equations of the reduced inverse
   image. It is normal crossings and a union of ambient components. In the strict
   case retain the selected global components; their regular intersections and
   codimensions are those in IsStrictNormalCrossingsBoundary. -/
theorem veryTame_boundary_quotient_cartier
    {X Y : Scheme.{u}} [IsNoetherian X] (hX : IsRegularScheme X)
    {G : Type v} [Group G] [Finite G] (a : G →* Aut X)
    (B Bbar : X.IdealSheafData)
    (hB : IsStrictNormalCrossingsBoundary B)
    (hBbar : IsStrictNormalCrossingsBoundary Bbar)
    (hsub : B.support ≤ Bbar.support)
    (hBinv : ∀ g : G, B.comap (a g).hom = B)
    (hBbarinv : ∀ g : G, Bbar.comap (a g).hom = Bbar)
    (hvery : IsVeryTameDivisorialAction Bbar.support.compl a)
    (q : X ⟶ Y) (hq : IsAdmissibleFiniteSchemeQuotient a q) :
    (∃ E : Y.WeilDivisor, E.IsEffectiveQCartier ∧
      Scheme.WeilDivisor.support E = q '' (B.support : Set X)) ∧
    (∀ y : Y, ∃ (W : Scheme.{u}) (e : W ⟶ Y), Etale e ∧
      ∃ (w : W) (_hw : e w = y) (c : Γ(W, ⊤)),
        c ∈ nonZeroDivisors Γ(W, ⊤) ∧
          W.zeroLocus {c} = e ⁻¹' (q '' (B.support : Set X))) ∧
    (∀ (Y' : Scheme.{u}) (h : Y' ⟶ Y), SchemeModification h →
      IsRegularScheme Y' →
      ((quotientBoundaryIdeal q Bbar).comap h).radical.IsNormalCrossingsDivisor →
      ((quotientBoundaryIdeal q B).comap h).radical.IsNormalCrossingsDivisor ∧
      (∃ S : Finset (irreducibleComponents
          ((quotientBoundaryIdeal q Bbar).comap h).radical.subscheme),
        (((quotientBoundaryIdeal q B).comap h).radical.support : Set Y') =
          ⋃ Z ∈ S, ((quotientBoundaryIdeal q Bbar).comap h).radical.subschemeι '' Z.val) ∧
      (IsStrictNormalCrossingsBoundary ((quotientBoundaryIdeal q Bbar).comap h).radical →
        IsStrictNormalCrossingsBoundary ((quotientBoundaryIdeal q B).comap h).radical)) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      (∃ ζ : boundaryInvariantRing a t, IsPrimitiveRoot ζ (boundaryInertiaOrder a t)) →
      ∃ (b : strictLocalRing X t)
        (χ : ∀ (g : G) (_hg : t ≫ (a g).hom = t), (boundaryInvariantRing a t)ˣ)
        (c : boundaryInvariantRing a t),
        b ∈ nonZeroDivisors (strictLocalRing X t) ∧
        boundaryStrictLocalIdeal B t = Ideal.span {b} ∧
        (∀ (g : G) (hg : t ≫ (a g).hom = t),
          automorphismStrictLocalMap (a g) t hg b = (χ g hg).val.val * b ∧
            (χ g hg) ^ boundaryInertiaOrder a t = 1) ∧
        c.val = b ^ boundaryInertiaOrder a t ∧
        c ∈ nonZeroDivisors (boundaryInvariantRing a t) ∧
        (Ideal.span {c}).radical =
          (Ideal.comap (boundaryInvariantRing a t).subtype
            (boundaryStrictLocalIdeal B t)).radical := by
  sorry

end AlgebraicGeometry
