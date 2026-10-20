/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Composition and boundary dualizing objects on the comparison class

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
cor-weil-boundary-duality-discharge.md, first proof paragraph
(blueprint: lem-weil-boundary-dualizing-composition).

All comparison data below are constructed from the existing compact-support composition,
its actual adjunctions, and the site-comparison unit. No pro-etale ambient adjunction is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Restrict the actual ambient right adjoint to bounded below objects.
Source: the boundary-duality proof, preparation and restriction of adjoints
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryUpperShriekPlus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] :
    DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  _root_.DerivedCategory.TStructure.t.plus.lift
    (_root_.DerivedCategory.Plus.ι ⋙ rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f)
    (fun K ↦ plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} Λ) f K.obj K.property)

/-- Restriction of the ambient adjunction along the fully faithful D+ inclusions.
Source: boundary-duality proof and Stacks Tag 0DV0
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryAdjunctionPlus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [CompactSpace Y] :
    rightDerivedLowerShriekPlus (ModuleCat.{u + 1} Λ) f ⊣ boundaryUpperShriekPlus Λ f :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} Λ) f).symm (Iso.refl _)

/-- The canonical mate θ: (gf)-times to f-times g-times, with the specified orientation.
Source: boundary-duality proof; Stacks Tag 0DV0, composition of adjunctions
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryCompositionIso {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] [CompactSpace Y] [CompactSpace S] :
    boundaryUpperShriekPlus Λ (f ≫ g) ≅
      boundaryUpperShriekPlus Λ g ⋙ boundaryUpperShriekPlus Λ f :=
  conjugateIsoEquiv (boundaryAdjunctionPlus Λ (f ≫ g))
    ((boundaryAdjunctionPlus Λ f).comp (boundaryAdjunctionPlus Λ g))
    (rightDerivedLowerShriekPlusCompIso Λ f g)

/-- The site unit, after applying f-times and ν_X^*, gives ρ_H (also λ_W at A).
Source: boundary-duality proof, explicit comparison-unit transport
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryOriginIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (H : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj H.obj) ≅
      (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.obj H.obj) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.mapIso
    ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso
      (@asIso _ _ _ _
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app H.obj)
        (ProEtale.isIso_derivedComparisonAdjunction_unit_app
          (ModuleCat.{u + 1} Λ) Y H.obj H.property)))

/-- The prescribed pro-etale composition: P_f(λ_g inverse), ρ inverse, ν^*(θ inverse), λ_gf.
Source: boundary-duality proof, final displayed composite, with A replaced by H
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryProCompositionIsoApp {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] [CompactSpace Y] [CompactSpace S]
    (H : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategory.obj H.obj)) ≅
      (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (f ≫ g)).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategory.obj H.obj) :=
  (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso
      (boundaryOriginIso Λ g H).symm ≪≫
    (boundaryOriginIso Λ f ((boundaryUpperShriekPlus Λ g).obj H)).symm ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.mapIso
      (ObjectProperty.ι _ |>.mapIso ((boundaryCompositionIso Λ f g).app H).symm) ≪≫
    boundaryOriginIso Λ (f ≫ g) H

/-- The constant coefficient object in degree zero, in D+.
Source: boundary-duality proof, evaluation at A
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryCoefficientPlus (S : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨constantComplex Λ S, ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
    (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩⟩

/-- Evaluation of θ inverse at the coefficient unit. For f=i and g=a_T this is κ_e.
The structure map of Z is i followed by a_T, so its target is exactly omega_Z.
Source: boundary-duality proof, closed-immersion specialization
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryDualizingEtaleIso {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] [CompactSpace Y] [CompactSpace S] :
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) g) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (f ≫ g) :=
  (ObjectProperty.ι _).mapIso
    ((boundaryCompositionIso Λ f g).app (boundaryCoefficientPlus Λ S)).symm

/-- λ_W, including the canonical identification of the pulled-back coefficient unit.
Source: boundary-duality proof, comparison-unit formula for lambda
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryDualizingComparisonIso {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) a) ≅
      (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) a).obj (𝟙_ _) :=
  boundaryOriginIso Λ a (boundaryCoefficientPlus Λ S) ≪≫
    (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) a).mapIso
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategory.mapIso
          (_root_.DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} Λ) S).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso
          (ProEtale.comparisonUpperStarUnitIso Λ S) ≪≫
        _root_.DerivedCategory.singleFunctorObjUnitIso _)

/-- The prescribed composite identifying the pro-etale dualizing objects.
For a closed immersion f=i and g=a_T this is Ri_p! omega_T,p = omega_Z,p.
The input and output are the actual constant-coefficient dualizing objects.
Source: boundary-duality proof, final displayed composite
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryDualizingProIso {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] [CompactSpace Y] [CompactSpace S] :
    (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
        ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g).obj (𝟙_ _)) ≅
      (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (f ≫ g)).obj (𝟙_ _) :=
  (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).mapIso
      (boundaryDualizingComparisonIso Λ g).symm ≪≫
    (boundaryOriginIso Λ f
      ((boundaryUpperShriekPlus Λ g).obj (boundaryCoefficientPlus Λ S))).symm ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.mapIso
      (boundaryDualizingEtaleIso Λ f g) ≪≫
    boundaryDualizingComparisonIso Λ (f ≫ g)

/-- The two compatibility assertions for the explicitly constructed comparisons.
The first equation is epsilon_gf composed with alpha = the pasted counits after theta.
The second says that the displayed pro-etale isomorphisms are natural on D+ etale inputs.
Source: boundary-duality proof, steps 4 and 7
(blueprint: lem-weil-boundary-dualizing-composition). -/
def BoundaryCompositionCompatibility {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f] [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] [CompactSpace Y] [CompactSpace S] :
    Prop :=
  (∀ H : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    (rightDerivedLowerShriekPlusCompIso Λ f g).hom.app
        ((boundaryUpperShriekPlus Λ (f ≫ g)).obj H) ≫
        (boundaryAdjunctionPlus Λ (f ≫ g)).counit.app H =
      (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} Λ) g).map
          ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} Λ) f).map
            ((boundaryCompositionIso Λ f g).hom.app H)) ≫
        (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} Λ) g).map
          ((boundaryAdjunctionPlus Λ f).counit.app ((boundaryUpperShriekPlus Λ g).obj H)) ≫
        (boundaryAdjunctionPlus Λ g).counit.app H) ∧
  (∀ (H H' : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (h : H ⟶ H'),
    (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).map
        ((ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) g).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategory.map h.hom)) ≫
        (boundaryProCompositionIsoApp Λ f g H').hom =
      (boundaryProCompositionIsoApp Λ f g H).hom ≫
        (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (f ≫ g)).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).mapDerivedCategory.map h.hom))

/-- The compatibility assertion with exactly the finite-field and finite-type scope.
The lets only prepare derived typeclass instances inside this definition of a proposition;
they are not binders in a theorem statement. All right adjoints and comparison maps are
those defined above. Arbitrary positive n is retained.
Source: boundary-duality proof, preparation of all three compactifications
(blueprint: lem-weil-boundary-dualizing-composition). -/
def BoundaryCompositionOverFiniteField (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  ∀ (X Y S : Scheme.{u})
    (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k)) (aS : S ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g],
    f ≫ aY = aX → g ≫ aS = aY →
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
    letI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
    letI : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated aS
    BoundaryCompositionCompatibility (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) f g

/-- The closed-immersion specialization, with no compactification or boundedness premise
added to the finite-type hypotheses: its first component is κ_e and its second is κ_p.
The structure map a_Z is i followed by a_T. Both components use the canonical mate above.
The pro-etale functors are definitionally sfFiniteExceptionalFixed at the chosen
compactifications, and sfFiniteExceptional is their recorded intrinsic realization.
Source: boundary-duality discharge, first proof paragraph and its site-comparison transport
(blueprint: lem-weil-boundary-dualizing-composition). -/
noncomputable def boundaryClosedDualizingIsos
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Z T : Scheme.{u}}
    (aT : T ⟶ Spec (.of D.k)) [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i] :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  letI : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated aT
  (boundaryDualizingEtaleIso (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i aT,
    @id ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
          (HasCompactification.compactification i)).obj
        ((ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
          (HasCompactification.compactification aT)).obj (𝟙_ _)) ≅
      (ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E n)
        (HasCompactification.compactification (i ≫ aT))).obj (𝟙_ _))
      (boundaryDualizingProIso (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) i aT))

/-- Dualizing objects compose, with the canonical mate and its pasted-counit normalization,
and the same identification is natural on the bounded-below etale comparison class.
`boundaryDualizingEtaleIso` and `boundaryDualizingProIso` are its values at A, in particular
for every closed immersion i and structure map a_T, with a_Z=i followed by a_T.
Source: boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-dualizing-composition).

Proof:
1. Finite type over a field makes all schemes Noetherian, quasi-compact and quasi-separated.
   Nagata gives compactifications of f, g, gf and the structure maps. Their ambient schemes
   are finite type over k, hence have finite dimension (use bound 0 for the empty scheme).
   Apply thm-amb-etale-exceptional-adjoint to the compact-support candidates.
2. The comparison unit at a bounded-below L is invertible. By
   thm-sf-ambient-adjoint-class, nu^* f-times L is bounded below. Exact nu^* reflects zero
   cohomology sheaves, by its full faithfulness on degree-zero objects; hence f-times L
   is bounded below. This justifies restriction of the ambient adjunction.
3. Use lem-amb-etale-compact-comparisons for the canonical D+ composition alpha. Exact
   open extension and bounded-below injective representatives show that the left functors
   preserve D+. Apply lem-cat-right-adjoint-composition to the restricted adjunctions:
   its representing Hom bijections give exactly boundaryCompositionIso, independent
   of compactification choices.
4. Adjunction.comp_counit_app and rightAdjointUniq_hom_counit give the first equation
   in BoundaryCompositionCompatibility, with theta oriented from (gf)-times to f-times g-times.
5. A closed immersion is proper, hence separated finite type. Specialize f=i and g=a_T
   and evaluate theta inverse at A in degree zero to obtain boundaryDualizingEtaleIso.
   Evaluation of the same counit equation proves its normalization.
6. Use lem-pe-constant-left-module-inverse-image for the constant coefficient unit.
   Applying nu^* f-times to the comparison unit gives boundaryOriginIso. At A, including
   the coefficient-unit identification, this is boundaryDualizingComparisonIso.
7. Paste the inverse lambda_T, inverse rho, nu^* kappa_e and lambda_Z as in
   boundaryDualizingProIso. For a general D+ input H use boundaryProCompositionIsoApp.
   Naturality of units, theta and the functors gives the second equation. These are
   the comparison-class Hom bijections of thm-sf-ambient-adjoint-class, so the counit
   normalization is inherited from step 4. No ambient pro-etale adjunction is asserted.
-/
theorem boundary_dualizing_composition
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) : BoundaryCompositionOverFiniteField D l E n hn := by
  sorry

end AlgebraicGeometry.Etale
