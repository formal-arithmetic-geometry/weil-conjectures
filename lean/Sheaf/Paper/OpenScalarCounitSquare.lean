/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence
public import Sheaf.SixFunctors.OpenScalarTensorData
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.OpenScalarTensorNormalization
import Sheaf.Paper.KFlatScalarComparisonNormalization

/-! # Open extension preserves the normalized scalar counit

Source: Stacks Project, sites-modules.tex, Tag 0E8I; sites-cohomology.tex, Tag 07A6;
blueprint, det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-open-scalar-counit-square).

All categories are ordinary uncompleted unbounded constant-ring module derived categories.
The open extension, scalar restriction square and tensor square are the published ones.
Unit equations express identity comparisons on the open without identifying distinct
functors by definitional equality. Naturality is retained at the natural-transformation level.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The exact open adjunction in the recorded sheafified extension coordinates.
The coordinate change is the unit-preserving uniqueness map `reductionOpenModel`.
Consequently this unit is the sectionwise open unit, descended termwise.
Source: Stacks Tags 03DI, 03DJ and 07A6
(blueprint: lem-sp-open-scalar-counit-square). -/
def openScalarCounitAdjunction (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j R).mapDerivedCategory ⊣ constantPullback (A := R) j :=
  (OpenScalarTensor.openAdj R j).ofNatIsoLeft (reductionOpenModel R j).symm

/-- Scalar multiplication identifies extension along the identity coefficient map with
identity. This is the unique left-adjoint comparison whose right-adjoint comparison is
the published sectionwise identity scalar unitor, so it retains counit normalization.
Source: Stacks Tag 07A6 (blueprint: lem-sp-open-scalar-counit-square). -/
def openScalarCounitScalarUnitor (R : Type u) [CommRing R] [Finite R]
    (W : Scheme.{u}) : scalarExtensionFunctor (RingHom.id R) W ≅ 𝟭 _ :=
  (proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := W) (RingHom.id R))).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (sfOpenDerivedCoefficientRestrictionId W R).symm)

/-- The open unit is invertible, and restriction determines any arrow whose source is
an open extension. The unit is the section-normalized one of `openScalarCounitAdjunction`;
its inverse is the sectionwise identification of restriction of extension with the input.
Source: Stacks Tags 03DI, 03DJ and 07A6
(blueprint: lem-sp-open-scalar-counit-square).

Proof: apply lem-sf-open-tensor-normalization to the constant ring on the small pro-etale
site. The extension presheaf on an object over X has its single original summand, and
sheafification restricts to the original sheaf, so its unit is the identity under this
sectionwise identification. Exact termwise localization preserves that identification.
The normalized coordinate change in reductionOpenModel preserves the unit. For h with
source j! M the adjunction sends h to eta_M followed by restriction of h. Equality of
restrictions therefore gives equality of adjuncts; injectivity of the Hom bijection gives
h = h'. This does not assert faithfulness of restriction on the ambient category. -/
theorem openScalarCounitUnit (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ M : proEtaleDerivedCategory X R,
      (openScalarCounitAdjunction R j).unit.app M ≫
          (openSquareDerivedPullbackModel R j).hom.app
            ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj M) =
        (sfIntrinsicDerivedOpenUnit R j).app M) ∧
    IsIso (openScalarCounitAdjunction R j).unit ∧
      ∀ (M : proEtaleDerivedCategory X R) (N : proEtaleDerivedCategory Z R),
        Function.Injective (fun h :
          (sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj M ⟶ N ↦
            (constantPullback (A := R) j).map h) := by
  sorry

/-- The specified scalar restriction and tensor comparisons restrict to identity
comparisons, written with their canonical open units and scalar/pullback identifications.
Source: Stacks Tags 03DI, 0E8I and 07A6
(blueprint: lem-sp-open-scalar-counit-square).

Proof: the scalar restriction map is sfOpenRestrictionDerived, the termwise descent of
the identity on the extension presheaves, as in lem-cbc-proetale-extension-zero and
lem-sf-open-extension-scalar-restriction-coherence. Its adjunction unit equation gives
the first equality after the canonical constant-pullback coordinate change. For tensor,
lem-fix-open-scalar-tensor-normalization identifies the common-right-adjoint comparison
with the balanced tensor map: the inverse is the open adjunct of scalar extension of
the A-unit followed by inverse lambda. Transport by reductionOpenModel preserves units
and gives the second equality. Since the units are invertible by openScalarCounitUnit,
these equations say exactly that the restricted comparisons are identities. -/
theorem openScalarCounitRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ L : proEtaleDerivedCategory X B,
      (openScalarCounitAdjunction A j).unit.app ((scalarRestriction φ X).obj L) ≫
          (constantPullback (A := A) j).map ((sfOpenRestrictionDerived j φ).hom.app L) ≫
          (OpenScalarTensor.rightSquare φ j).inv.app
            ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L) =
        (scalarRestriction φ X).map ((openScalarCounitAdjunction B j).unit.app L)) ∧
    (∀ M : proEtaleDerivedCategory X A,
      (openScalarCounitAdjunction B j).unit.app ((scalarExtensionFunctor φ X).obj M) ≫
          (constantPullback (A := B) j).map ((reductionOpenScalarIso φ j).inv.app M) =
        (scalarExtensionFunctor φ X).map ((openScalarCounitAdjunction A j).unit.app M) ≫
          (tensorPullbackIso φ j).inv.app
            ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M)) := by
  sorry

/-- Open extension and scalar restriction preserve the specified derived scalar counit.
This equality of natural transformations includes the equation at every ambient L and
its naturality, with no boundedness, flatness, constructibility or Tor condition.
Source: Stacks Tags 0E8I and 07A6; det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-open-scalar-counit-square).

Proof: put f = epsilon_Z(j!_B L) after T_Z(a_L), and g = j!_B(epsilon_X L) after E.
By lem-sfb-kflat-scalar-comparison-normalization, inverse lambda is the scalar-adjunction
mate of the identity-on-actions rightSquare, for the representative-normalized scalar
adjunction of lem-pur-sheaf-ring-derived-coefficient-adjunction. Its transpose formula
(def-weil-pbc-adjunction-mate) identifies restriction of f with epsilon_X(L), using the
first equation of openScalarCounitRestriction. Its second equation identifies restriction
of g with the same arrow. Precompose f and g with E inverse. Their common source is now
an open extension, so openScalarCounitUnit gives equality. Cancel E inverse. The scalar
counits and both specified comparisons are natural; extensionality gives the asserted
equality of natural transformations on the entire unbounded category. -/
theorem openScalarCounitSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Functor.whiskerRight (sfOpenRestrictionDerived j φ).hom (scalarExtensionFunctor φ Z) ≫
        Functor.whiskerLeft (sfIntrinsicExtensionByZero j B).mapDerivedCategory
          (proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := Z) φ)).counit =
      Functor.whiskerLeft (scalarRestriction φ X) (reductionOpenScalarIso φ j).hom ≫
        Functor.whiskerRight (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).counit
            (sfIntrinsicExtensionByZero j B).mapDerivedCategory := by
  sorry

/-- Identity coefficient maps give identity comparisons under the canonical scalar
unitors, and their scalar counit is the scalar multiplication unitor.
Source: Stacks Tag 07A6 (blueprint: lem-sp-open-scalar-counit-square).

Proof: the scalar restriction comparison is identity on every extension-presheaf section;
its termwise localization obeys the identity law of
lem-sf-open-extension-scalar-restriction-coherence. The balanced tensor comparison has
identity normalization by lem-fix-open-scalar-tensor-normalization, transported through
the unit-preserving reductionOpenModel. The scalar adjunction formulas x to x tensor 1
and x tensor a to a x identify its counit with multiplication for the identity ring map.
Equivalently this is the counit equation for the left-adjoint uniqueness unitor defined
above. All constructions apply to empty opens, whole opens and zero complexes. -/
theorem openScalarCounitIdentity (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ L : proEtaleDerivedCategory X R,
      (sfOpenRestrictionDerived j (RingHom.id R)).hom.app L ≫
          (sfOpenDerivedCoefficientRestrictionId Z R).hom.app
            ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj L) =
        (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
          ((sfOpenDerivedCoefficientRestrictionId X R).hom.app L)) ∧
    (∀ M : proEtaleDerivedCategory X R,
      (reductionOpenScalarIso (RingHom.id R) j).hom.app M ≫
          (sfIntrinsicExtensionByZero j R).mapDerivedCategory.map
            ((openScalarCounitScalarUnitor R X).hom.app M) =
        (openScalarCounitScalarUnitor R Z).hom.app
          ((sfIntrinsicExtensionByZero j R).mapDerivedCategory.obj M)) ∧
    (∀ (W : Scheme.{u}) (L : proEtaleDerivedCategory W R),
      (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := W) (RingHom.id R))).counit.app L =
        (openScalarCounitScalarUnitor R W).hom.app
            ((scalarRestriction (RingHom.id R) W).obj L) ≫
          (sfOpenDerivedCoefficientRestrictionId W R).hom.app L) := by
  sorry

end AlgebraicGeometry.ProEtale
