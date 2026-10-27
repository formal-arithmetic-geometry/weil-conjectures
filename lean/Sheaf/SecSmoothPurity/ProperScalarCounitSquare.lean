module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
public import Sheaf.Paper.FourCorners
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# Direct-image restriction and the scalar counit square

Source: Stacks Project, Cohomology on Sites, Tags 07A6, 0D6D and 0D6E;
blueprint det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-proper-scalar-counit-square).

The scalar extension, geometric adjunction and balanced pullback comparison are the
published canonical constructions. The direct-image comparison below specializes the
normalized ring-sheaf comparison, in the inverse direction. The theorem identifies its
resolution normalization and states both counit equations on the entire unbounded category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Exact termwise scalar restriction along the specified constant-ring map.
Source: Stacks Tags 03DA and 07A6
(blueprint: lem-sp-proper-scalar-counit-square). -/
abbrev directImageScalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    T.proEtaleDerivedCategory B ⥤ T.proEtaleDerivedCategory A :=
  (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The representative-normalized extension/restriction adjunction already used by the
canonical balancing comparison. Source: Stacks Tag 07A6
(blueprint: lem-sp-proper-scalar-counit-square). -/
abbrev directImageScalarAdjunction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    directImageScalarExtension φ T ⊣ directImageScalarRestriction φ T :=
  proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)

/-- The comparison D is the inverse of the normalized ring-sheaf comparison d.
The coefficient-square proof is the naturality of the constant-section map, so no
extra coefficient compatibility is assumed. Source: Stacks Tag 0D6E
(blueprint: lem-sp-proper-scalar-counit-square). -/
def directImageScalarRestrictionIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y) :
    directImageScalarRestriction φ Z ⋙ directImageConstantPush A h ≅
      directImageConstantPush B h ⋙ directImageScalarRestriction φ Y :=
  (proEtaleRingRestrictionDerivedDirectImage h
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
    (proEtaleConstantInverseImageMap_naturality h
      (CommRingCat.ofHom (RingHom.ulift φ))).symm).symm

/-- The proper scalar counit square, which in fact needs no properness.
The already defined natural transformation `directImageScalarComparison` is gamma.
The first clause gives its defining geometric transpose, the second its naturality,
the third the compatibility of the composite adjunctions and the scalar counit square.
The final clause identifies D with the direct-image restriction comparison on every
K-injective representative, using the same composition normalization kappa.

Source: Stacks Tags 07A6, 0D6D and 0D6E; blueprint det-sp-tower-gluing, Levels
(blueprint: lem-sp-proper-scalar-counit-square).

Proof:
1. The geometric Hom bijection defines gamma uniquely by transposing
   chi followed by T_Z(e^A). Its unit formula and naturality of chi and e^A
   give the first two clauses (def-weil-pbc-proetale-operations).
2. Apply lem-weil-pbc-ring-sheaf-change-adjunction to the B-geometric counit.
   The triangle identity gives r_Z(e^B) after b inverse equal to e^A followed
   by P_A(d), with precisely the specified d. Constant-section naturality
   supplies the coefficient square (prop-weil-pbc-proetale-constant-ring-map).
3. On a flat-term K-flat resolution P of r_Y(H), the scalar counit is the
   B-linear extension of P to H, x tensor b mapping to b g(x).
   Pullback preserves these resolutions (lem-weil-pbc-ringed-pullback-preserves-kflat).
   The balanced chi inverse and the scalar counit after pullback give the same
   extension. Sheaf tensor universality and localization prove the counit equality
   (lem-pur-sheaf-ring-derived-coefficient-adjunction and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
4. Substitute that equality in the composite-adjunction counit formula
   (def-weil-pbc-composite-adjunction). Naturality of the scalar counit and step 2
   give the displayed composite-adjunction equation.
5. Geometrically transpose both sides of the scalar square. Step 4, naturality
   of chi and cancellation of d with D give T_Z(e^A) followed by chi on both
   sides. Injectivity of the geometric Hom bijection gives the scalar square.
6. Write the two coefficient factorizations as identity-topos coefficient
   morphisms. The normalization of lem-weil-pbc-ringed-topoi-derived-pushforward-composition
   gives d as kappa for the first factorization times inverse kappa for the second.
   For a K-injective J and a resolution j of its restriction, the first factor
   is the class of h_*(j); the exact restriction comparisons cancel in the second.
   Inverting gives exactly lem-weil-proetale-direct-image-restriction-of-scalars,
   expressed by the final equality with the canonical Q and resolution factors.
   No restriction-preservation of K-injectivity, flatness or boundedness is used. -/
theorem properScalarCounitSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (h : Z ⟶ Y) :
    (∀ N : Z.proEtaleDerivedCategory A,
      (proEtaleConstantRingDerivedPullback B h).map
          ((directImageScalarComparison φ h).app N) ≫
        (directImageConstantAdjunction B h).counit.app
          ((directImageScalarExtension φ Z).obj N) =
      (directImageScalarPullbackIso φ h).hom.app ((directImageConstantPush A h).obj N) ≫
        (directImageScalarExtension φ Z).map
          ((directImageConstantAdjunction A h).counit.app N)) ∧
    (∀ (N N' : Z.proEtaleDerivedCategory A) (v : N ⟶ N'),
      (directImageScalarExtension φ Y).map ((directImageConstantPush A h).map v) ≫
          (directImageScalarComparison φ h).app N' =
        (directImageScalarComparison φ h).app N ≫
          (directImageConstantPush B h).map ((directImageScalarExtension φ Z).map v)) ∧
    (∀ H : Z.proEtaleDerivedCategory B,
      ((directImageScalarPullbackIso φ h).inv.app
          ((directImageScalarRestriction φ Y).obj ((directImageConstantPush B h).obj H)) ≫
        (proEtaleConstantRingDerivedPullback B h).map
          ((directImageScalarAdjunction φ Y).counit.app ((directImageConstantPush B h).obj H)) ≫
        (directImageConstantAdjunction B h).counit.app H =
      (directImageScalarExtension φ Z).map
          ((proEtaleConstantRingDerivedPullback A h).map
            ((directImageScalarRestrictionIso φ h).inv.app H)) ≫
        (directImageScalarExtension φ Z).map
          ((directImageConstantAdjunction A h).counit.app
            ((directImageScalarRestriction φ Z).obj H)) ≫
        (directImageScalarAdjunction φ Z).counit.app H) ∧
      ((directImageScalarExtension φ Y).map
          ((directImageScalarRestrictionIso φ h).hom.app H) ≫
        (directImageScalarAdjunction φ Y).counit.app ((directImageConstantPush B h).obj H) =
      (directImageScalarComparison φ h).app ((directImageScalarRestriction φ Z).obj H) ≫
        (directImageConstantPush B h).map ((directImageScalarAdjunction φ Z).counit.app H))) ∧
    (∀ (J : CochainComplex (Z.proEtaleRingModules (proEtaleConstantRing Z B)) ℤ)
      [J.IsKInjective]
      (I : CochainComplex (Z.proEtaleRingModules (proEtaleConstantRing Z A)) ℤ)
      [I.IsKInjective]
      (j : ((proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := Z) φ)).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
      [QuasiIso j],
      QuasiIso (((proEtaleConstantRingPushforward A h).mapHomologicalComplex (.up ℤ)).map j) ∧
      (directImageScalarRestrictionIso φ h).hom.app (DerivedCategory.Q.obj J) ≫
          (directImageScalarRestriction φ Y).map
            ((proEtaleConstantRingPushforward B h).rightDerivedFunctorObjQIso J).hom ≫
          (proEtaleRingRestrictScalars
            (proEtaleConstantRingMap (T := Y) φ)).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantRingPushforward B h).mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (proEtaleRingRestrictionDirectImage h
                (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
                (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
                (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
                (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison h B)
                (proEtaleConstantInverseImageMap_naturality h
                  (CommRingCat.ofHom (RingHom.ulift φ))).symm) (.up ℤ)).hom.app J) ≫
          DerivedCategory.Q.map
            (((proEtaleConstantRingPushforward A h).mapHomologicalComplex (.up ℤ)).map j) =
        (directImageConstantPush A h).map
            ((proEtaleRingRestrictScalars
              (proEtaleConstantRingMap (T := Z) φ)).mapDerivedCategoryFactors.hom.app J) ≫
          (directImageConstantPush A h).map (DerivedCategory.Q.map j) ≫
          ((proEtaleConstantRingPushforward A h).rightDerivedFunctorObjQIso I).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
