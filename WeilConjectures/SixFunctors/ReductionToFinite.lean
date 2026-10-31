/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSix
public import WeilConjectures.SixFunctors.ScalarSixAdmissibleThickness
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.IntegralModels
import WeilConjectures.AlgebraicGeometry.DerivedNakayama
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit

/-! # Isomorphisms reduce to finite coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-reduction-to-finite/_section.md and sk-prop-reduction-to-finite.proof.md
(blueprint: sk-prop-reduction-to-finite).

The coefficient presentations are precisely the endpoints of listed identity maps:
finite ell-primary rings, integral and field finite subextensions, and the fixed
finite-subextension-valued condensed algebraic closure. All categories and scalar
functors are the existing ordinary, uncompleted internal-module constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Specialization of Mathlib's exact-functor and shift-compatible-transformation
predicates to the existing finite-Tor constructible full subcategories. Their triangles
are inherited from the ambient derived categories, using the already stated thickness
and Tor-amplitude results. The existential shift isomorphisms are the exact-functor
structure in the source, not an additional property of the coefficient rings.
Source: latest blueprint reduction-to-finite, exactness hypothesis
(blueprint: sk-prop-reduction-to-finite). -/
def ReductionToFiniteExact (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (Λ : ScalarSixRing.{u}) (hΛ : ListedCoefficientMap ell (𝟙 Λ))
    (F G : ConstantModelConstructibleFiniteTor Λ.X X.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.left) (θ : F ⟶ G) : Prop :=
  letI : (constantModelBoundedConstructible Λ.X X.left).IsTriangulated :=
    (sfbAdmissibleConstructibleThickness ell Λ
      (listedCoefficientCtf ell (𝟙 Λ) hΛ).1 k X).1
  letI : (constantModelBoundedConstructible Λ.X Y.left).IsTriangulated :=
    (sfbAdmissibleConstructibleThickness ell Λ
      (listedCoefficientCtf ell (𝟙 Λ) hΛ).1 k Y).1
  letI : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ.X X.left)).IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.2.2.2.2.2.2.1
  letI : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ.X Y.left)).IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ.X Y.left).2.2.2.2.2.2.2.1
  letI : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ.X X.left)).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.2.2.1
  letI : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ.X Y.left)).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ.X Y.left).2.2.2.1
  Exists fun [_instF : F.CommShift ℤ] ↦ Exists fun [_instG : G.CommShift ℤ] ↦
    F.IsTriangulated ∧ G.IsTriangulated ∧ NatTrans.CommShift θ ℤ

/-- A coefficient-compatible natural transformation of exact functors on Dctf is
invertible for every admissible coefficient if it is invertible for every finite
ell-primary coefficient. The two displayed isomorphisms express the scalar square
object by object; its equality is exactly compatibility with the transformation.
Source: latest blueprint reduction-to-finite, Proposition
(blueprint: sk-prop-reduction-to-finite).

Proof:
1. Scalar-six supplies the ordinary scalar functors on Dctf, including integral
reduction, localization, and finite-field extension to the algebraic closure. Its
composition, unit, counit and evaluation compatibilities give the source's examples
built covariantly from the six operations and their canonical transformations.
2. For an integral input, integral_models gives derived completeness of both output
objects. The assumed square identifies the reduction of theta with its finite-residue
component, which is invertible by the finite hypothesis. The morphism clause of
reduction_and_derived_nakayama therefore makes the integral component invertible.
This argument applies to every integral input, including torsion complexes.
3. Naturality makes the isomorphism locus invariant under isomorphism. Exactness and
shift compatibility make it closed under shifts and cones: the three components on
a distinguished triangle form a triangle morphism, and the two-out-of-three lemma
for its isomorphic components applies. The zero object is in this locus.
4. integral_models generates rational constructible objects by finite cones and shifts
of localized integral extensions by zero. Integral Dbc equals Dctf, so step 2 applies
to these integral generators. The scalar square for localization then gives their
rational components; step 3 gives every rational object. Rational Dbc equals Dctf by
finiteCoefficientDescentTwoColimit.
5. The same descent theorem writes every algebraic-closure object as the extension
of an object over a finite subfield. Apply step 4, the scalar square and naturality
along that descent isomorphism. Together with the finite hypothesis this exhausts
the coefficient list; the ground finite subfield includes Z_ell and Q_ell. -/
theorem reductionToFinite (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (F G : ∀ (Λ : ScalarSixRing.{u}), ListedCoefficientMap ell (𝟙 Λ) →
      ConstantModelConstructibleFiniteTor Λ.X X.left ⥤
        ConstantModelConstructibleFiniteTor Λ.X Y.left)
    (θ : ∀ (Λ : ScalarSixRing.{u}) (hΛ : ListedCoefficientMap ell (𝟙 Λ)),
      F Λ hΛ ⟶ G Λ hΛ)
    (hexact : ∀ (Λ : ScalarSixRing.{u}) (hΛ : ListedCoefficientMap ell (𝟙 Λ)),
      ReductionToFiniteExact ell k X Y Λ hΛ (F Λ hΛ) (G Λ hΛ) (θ Λ hΛ))
    (hscalar : ∀ (Λ Λ' : ScalarSixRing.{u})
      (hΛ : ListedCoefficientMap ell (𝟙 Λ)) (hΛ' : ListedCoefficientMap ell (𝟙 Λ'))
      (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a)
      (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      ∃ (eF : (scalarExceptionalChange ell k a ha Y).obj ((F Λ hΛ).obj K) ≅
          (F Λ' hΛ').obj ((scalarExceptionalChange ell k a ha X).obj K))
        (eG : (scalarExceptionalChange ell k a ha Y).obj ((G Λ hΛ).obj K) ≅
          (G Λ' hΛ').obj ((scalarExceptionalChange ell k a ha X).obj K)),
        (scalarExceptionalChange ell k a ha Y).map ((θ Λ hΛ).app K) ≫ eG.hom =
          eF.hom ≫ (θ Λ' hΛ').app ((scalarExceptionalChange ell k a ha X).obj K))
    (hfinite : ∀ (Λ : ScalarSixRing.{u}) (hΛ : ListedCoefficientMap ell (𝟙 Λ)),
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A),
        (∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0) ∧
          Λ = (⟨cartesianFinitePointRing A⟩ : ScalarSixRing.{u})) →
      ∀ K : ConstantModelConstructibleFiniteTor Λ.X X.left, IsIso ((θ Λ hΛ).app K)) :
    ∀ (Λ : ScalarSixRing.{u}) (hΛ : ListedCoefficientMap ell (𝟙 Λ))
      (K : ConstantModelConstructibleFiniteTor Λ.X X.left), IsIso ((θ Λ hΛ).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
