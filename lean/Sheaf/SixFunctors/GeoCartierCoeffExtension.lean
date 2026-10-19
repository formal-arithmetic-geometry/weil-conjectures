module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar

public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.NormalizedEtaleOriginWitnesses
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Data.Finite.Defs
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Derived scalar extension for a supported constant sheaf

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md,
paragraph 4; Stacks Project, Tags 07A6, 0D6D and 0G7E.
(blueprint: lem-geo-cartier-coeff-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The ordinary direct image of the constant rank-one module on a closed subscheme.
Source: Stacks Tag 03QP(1), used in the coefficient-extension comparison.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def supportedConstantModule {A : Type (u + 1)} [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- Push forward the coefficient unit on `D`. The constant-sheaf adjunction sends the
generator `1` of `A` to the constant section `1` of `B`, with the A-action restricted
along `φ`; hence a constant section `a` goes to `φ a`.
Source: sk-lem-geo-cartier.proof.md, paragraph 4; Stacks 07A6.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def coefficientUnitModule {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedConstantModule (A := A) i ⟶
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).obj
        (supportedConstantModule (A := B) i) := by
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 D)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  let x : (((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
      ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)))) :=
    (constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} B) hT).unit.app
      (ModuleCat.of B B) (1 : B)
  let h : ModuleCat.of A A ⟶
      ((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
        ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) :=
    ModuleCat.ofHom
      (Y := ((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
        ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))))
      (LinearMap.toSpanSingleton A
        (((sheafSections D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (Opposite.op (Scheme.Etale.mk (𝟙 D)))).obj
          ((Sheaf.restrictScalars D.smallEtaleTopology φ).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
              (ModuleCat.of B B)))) x)
  let k : (constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)) :=
    (constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} A) hT).homEquiv _ _ |>.symm h
  exact (lowerStar (ModuleCat.{u + 1} A) i).map k ≫
    (lowerStarRestrictScalarsIso φ i).inv.app
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))

/-- The degree-zero derived object underlying `i_* A_D`.
Source: Stacks Tag 03QP(1), used in the coefficient-extension comparison.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def supportedConstantDerived {A : Type (u + 1)} [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor
    (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
    (supportedConstantModule i)

/-- The degree-zero image of the specified direct-image coefficient unit, transported
by the canonical compatibility of exact restriction with the single functor.
Source: sk-lem-geo-cartier.proof.md, paragraph 4; Stacks 07A6.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def coefficientUnitDerived {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    supportedConstantDerived (A := A) i ⟶
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).obj
        (supportedConstantDerived (A := B) i) :=
  exactDerivedScalarUnitMap (Sheaf.restrictScalars Z.smallEtaleTopology φ)
    (coefficientUnitModule φ i)

/-- The specified comparison is the adjunct of the actual direct-image coefficient unit.
Source: sk-lem-geo-cartier.proof.md, paragraph 4; Stacks 07A6.
(blueprint: lem-geo-cartier-coeff-extension) -/
noncomputable def supportedCoefficientComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension Z.smallEtaleTopology φ).obj
      (supportedConstantDerived (A := A) i) ⟶ supportedConstantDerived (A := B) i :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).homEquiv
        (supportedConstantDerived (A := A) i) (supportedConstantDerived (A := B) i)).symm
    (coefficientUnitDerived φ i)

/-- Derived scalar extension of the supported constant sheaf along finite coefficients is the
specified adjunct of the coefficient-unit map.  It is an isomorphism, natural in the coefficient
map, normalized to the identity coefficient map, and coherent under successive extensions.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
sk-lem-geo-cartier.proof.md, paragraph 4; Stacks Project, Tags 07A6, 0D6D and 0G7E.
Proof:
1. The ordinary coefficient unit sends a local constant `a` to `φ a`. Apply ordinary
direct image, embed in degree zero, and take its adjunct using
lem-pur-sheaf-ring-derived-coefficient-adjunction. This is the defined comparison.
2. A closed immersion is finite and its geometric fibre is one point on `D`, empty
off `D`. By lemma-weil-pbc-finite-stalk-formula and
lem-weil-pbc-constant-sheaf-geometric-stalk its supported constant stalk is `A` on
`D` and zero off `D`. Compute derived scalar extension on a flat-term K-flat
representative using lem-pur-derived-change-of-rings. By lem-kun-stalk-as-pullback
and lem-kun-inverse-image-monoidal its stalk is `A tensor_A^L B = B` on `D`, zero
off `D`. The normalized adjunct formula is multiplication `a tensor b` to `φ(a)b`,
an isomorphism, or the map zero to zero. Exactness of geometric stalks and
lemma-weil-pbc-geometric-stalk-conservative detect the isomorphism on every
cohomology sheaf. Apply this to all three coefficient maps; no coefficient
flatness or boundedness is needed.
3. The coefficient units commute with composition before applying direct image.
The canonical exact restriction composition isomorphism preserves this equation
in the derived category. Naturality of the adjunction hom equivalences gives
coefficient naturality of the specified comparisons.
4. For the identity coefficient map, the ordinary unit is identity after the
sectionwise restriction identification. Taking its adjunct gives precisely the
canonical left-adjoint identity isomorphism `normalizedOriginScalarUnit`.
5. The unit normalization of lem-sfb-successive-derived-quotient-normalization
identifies the canonical scalar associator with `pbcFixedScalarExtensionComp`.
The two sides of the final equation are adjuncts of the same composite
coefficient unit by Step 3. Uniqueness of adjuncts proves their equality and
iterated coherence.
(blueprint: lem-geo-cartier-coeff-extension) -/
theorem geoCartierCoeffExtension
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (φ : A →+* B) (ψ : B →+* C) :
    IsIso (supportedCoefficientComparison φ i) ∧
    IsIso (supportedCoefficientComparison ψ i) ∧
    IsIso (supportedCoefficientComparison (ψ.comp φ) i) ∧
    coefficientUnitDerived (ψ.comp φ) i = coefficientUnitDerived φ i ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map (coefficientUnitDerived ψ i) ≫
      (Sheaf.derivedRestrictScalarsCompIso Z.smallEtaleTopology rfl).hom.app
        (supportedConstantDerived (A := C) i) ∧
    supportedCoefficientComparison (RingHom.id A) i =
      (AlgebraicGeometry.ProEtale.normalizedOriginScalarUnit Z.smallEtaleTopology
        (RingHom.id A) rfl).hom.app (supportedConstantDerived (A := A) i) ∧
    (AlgebraicGeometry.ProEtale.pbcFixedScalarExtension Z.smallEtaleTopology ψ).map
        (supportedCoefficientComparison φ i) ≫ supportedCoefficientComparison ψ i =
      (AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology
        φ ψ (ψ.comp φ) rfl).hom.app (supportedConstantDerived (A := A) i) ≫
          supportedCoefficientComparison (ψ.comp φ) i := by
  sorry

end AlgebraicGeometry.Etale
