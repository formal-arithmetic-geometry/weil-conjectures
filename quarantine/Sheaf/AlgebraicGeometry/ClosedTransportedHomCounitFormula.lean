module

public import Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Closed transported Hom bijections and counit

Source: blueprint main-20261015, thm-sf-ambient-adjoint-class.proof.md,
finite transported Hom chain and its inverse at the identity
(blueprint: lem-pur-closed-transported-hom-counit-formula).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A]
variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
variable (hij : IsCompl (Set.range i.base) (Set.range j.base))

/-- The termwise pro-etale closed direct image. Exactness is supplied by the existing
closed-immersion theorem, with precisely the quasi-compact complementary open.
Source: blueprint finite transported Hom chain, exact-derived identification
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportDirectImage :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory

/-- The canonical exact-functor comparison from total right derived direct image to
termwise direct image, characterized by the total-derived comparison on complexes.
Source: blueprint finite transported Hom chain, exact-derived identification
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportDirectImageIso :
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor ≅
      closedTransportDirectImage A i j hij :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory

/-- Identity extension followed by exact closed direct image gives the canonical
pro-etale compact-support normalization at `(id_Z,i)`.
Source: blueprint finite transported Hom chain, identity-extension identifications
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportProetNormalization :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅ closedTransportDirectImage A i j hij :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) Z) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _ ≪≫ closedTransportDirectImageIso A i j hij

/-- The canonical comparison lambda, obtained by descending the specified underived
comparison mate termwise, with the canonical composition identifications.
Source: blueprint finite transported Hom chain, direct-image comparison
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportComparison :
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory ⋙
        closedTransportDirectImage A i j hij :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := A) i j hij
  letI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A))) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The ordinary etale identity-open compact-support normalization, followed by the
canonical exact-direct-image comparison.
Source: blueprint finite transported Hom chain, etale closed normalization
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportEtaleNormalization :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) Z) _ ≪≫
    Functor.leftUnitor _ ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory

variable [Finite A]

/-- The ordinary etale exceptional right adjoint, read through the normalized closed
compact-support presentation. Its data comes from the existing Brown adjunction.
Source: blueprint finite transported Hom chain, F adjoint to G
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportEtaleRight :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (Compactification.ofIsProper i)
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (Compactification.ofIsProper i)).rightAdjoint

/-- The actual etale adjunction F adjoint to G, transported only on its left functor
by the canonical closed normalization; G remains the existing exceptional right adjoint.
Source: blueprint finite transported Hom chain, F adjoint to G
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportEtaleAdjunction :
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory ⊣
      closedTransportEtaleRight A i :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (Compactification.ofIsProper i)
  (Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper i))).ofNatIsoLeft (closedTransportEtaleNormalization A i)

/-- The etale object E_L = G U_X L, before exact comparison pullback.
Source: blueprint finite transported Hom chain, definition of E_L
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportEtaleValue :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor ⋙
    closedTransportEtaleRight A i

/-- The exceptional functor is the already defined finite transported exceptional functor
at the identity-open compactification, with its ordinary etale adjoint instance supplied
by the existing Brown theorem.
Source: blueprint finite transported Hom chain, definition of Ri!L
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportExceptional :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (Compactification.ofIsProper i)
  sfFiniteExceptionalAt A (Compactification.ofIsProper i)

/-- The allowed targets are exactly L in D+ for which E_L is in D+.
No etale-origin condition on L is imposed.
Source: blueprint finite transported Hom chain, bounded-below domain
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportAllowedTarget :
    ObjectProperty (DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  fun L ↦ DerivedCategory.TStructure.t.plus L ∧
    DerivedCategory.TStructure.t.plus ((closedTransportEtaleValue A i).obj L)

/-- The specified four-factor Hom map: precompose with lambda, use the comparison
adjunction, use F adjoint to G, then apply exact comparison pullback on Z.
Source: blueprint finite transported Hom chain, the displayed four arrows
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportHomMap
    (H : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (f : (closedTransportDirectImage A i j hij).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj H) ⟶ L) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj H ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
        ((closedTransportEtaleValue A i).obj L) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
    ((closedTransportEtaleAdjunction A i).homEquiv H _
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ L
        ((closedTransportComparison A i j hij).hom.app H ≫ f)))

/-- The expanded candidate counit is lambda inverse, followed by comparison pullback
of the etale counit, followed by the comparison counit at L. This defines a map,
without asserting an exceptional adjunction outside the specified relative domain.
Source: blueprint finite transported Hom chain, inverse image of the identity
(blueprint: lem-pur-closed-transported-hom-counit-formula). -/
def closedTransportCounit
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (closedTransportDirectImage A i j hij).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
          ((closedTransportEtaleValue A i).obj L)) ⟶ L :=
  (closedTransportComparison A i j hij).inv.app ((closedTransportEtaleValue A i).obj L) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      ((closedTransportEtaleAdjunction A i).counit.app
        ((comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctor.obj L)) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).counit.app L

/-- Expanded relative Hom bijections, the identity-open compact-support normalization,
and the unique inverse image of the identity, with its naturality on allowed targets.
All module categories are ordinary fixed constant-coefficient module sheaves.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-existence,
thm-sf-ambient-adjoint-class.proof.md, displayed finite transported Hom chain;
sk-prop-a1 first closed localization triangle
(blueprint: lem-pur-closed-transported-hom-counit-formula).

Proof plan:
1. The closed immersion is proper and qcqs (lem-weil-pbc-closed-immersion-proper,
   pqf-lem-proper-basic). Finite type over the field gives a finite dimension bound
   (lem-kun-dimension-finite-type), choosing zero for the empty scheme. Apply
   lem-pur-closed-unbounded-compact-support-normalization for F and its bounds.
   The quasi-compact complement gives exact pro-etale direct image by
   lem-exc-proetale-closed-exact. Exact-functor derived factorization and the
   exact-derived-functor theorem identify its total derived functor with P on every
   representing complex, using the canonical comparison, not an arbitrary isomorphism.
2. Apply sk-thm-pe-direct-image-comparison to i and H in D+. Exactness identifies its
   canonical mate with the descended underived mate closedTransportComparison.
   The identity-open comparison has no additional automorphism. The normalization in
   lem-coef-proper-identity-open-site-comparison therefore identifies the compact-support
   comparison with lambda inverse after removing the two identity extensions.
3. Put E=G U_X L, bounded below by hypothesis. The etale normalization preserves the
   lower bound of H. The comparison adjunction and F adjoint to G give the middle
   bijections. The last map is comparison full faithfulness on H,E in D+ by
   thm-weil-pbc-site-comparison. Lem-coef-relative-hom-change-of-presentation identifies
   this four-factor composite with the specified relative exceptional adjunction.
   L need not be of etale origin. The exceptional value is definitionally S_Z E.
4. Reverse the four bijections on the identity of S_Z E. Full faithfulness sends it
   back to the identity of E. Lem-weil-pbc-adjunct-counit-identity for F adjoint to G
   sends that to the etale counit. The same lemma for S_X adjoint to U_X sends it
   to S_X of that counit followed by e_X. Inverse precomposition by lambda gives
   precisely closedTransportCounit. Bijectivity gives its uniqueness.
5. Naturality of the two Hom adjunctions and lambda proves naturality in H and L.
   For u:L to L', put v=G U_X(u). Naturality of the etale counit, lambda inverse and
   the comparison counit successively gives P S_Z(v) followed by t_L' equal to
   t_L followed by u. Restrict throughout to L,E_L in D+; no unbounded exceptional
   adjunction is asserted. -/
theorem closed_transported_hom_counit_formula
    (P : PurityFiniteSetting.{u}) {Z U X : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of P.field.k))]
    [X.Over (Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of P.field.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (fun [_hfin : Finite P.Coefficient] ↦
    (PreservesFiniteLimits (lowerStar (ModuleCat.{u + 1} P.Coefficient) i) ∧
      PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} P.Coefficient) i)) ∧
    (∀ K : CochainComplex (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} P.Coefficient)) ℤ,
      IsIso ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ∧
    (∀ H : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)),
      (compactSupportSiteComparison P.Coefficient (Compactification.ofIsProper i)).hom.app H ≫
          (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            ((closedTransportEtaleNormalization P.Coefficient i).hom.app H.obj) =
        (closedTransportProetNormalization P.Coefficient i j hij).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.obj
              H.obj) ≫
          (closedTransportComparison P.Coefficient i j hij).inv.app H.obj) ∧
    (∀ L : DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)),
      closedTransportAllowedTarget P.Coefficient i L →
      (closedTransportExceptional P.Coefficient i).obj L =
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.obj
          ((closedTransportEtaleValue P.Coefficient i).obj L)) ∧
    (∀ (H : DerivedCategory (Sheaf Z.smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)))
        (L : DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))),
      DerivedCategory.TStructure.t.plus H →
      closedTransportAllowedTarget P.Coefficient i L →
      Function.Bijective (closedTransportHomMap P.Coefficient i j hij H L)) ∧
    (∀ (L : DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
        (t : (closedTransportDirectImage P.Coefficient i j hij).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.obj
              ((closedTransportEtaleValue P.Coefficient i).obj L)) ⟶ L),
      closedTransportAllowedTarget P.Coefficient i L →
      (closedTransportHomMap P.Coefficient i j hij
          ((closedTransportEtaleValue P.Coefficient i).obj L) L t = 𝟙 _ ↔
        t = closedTransportCounit P.Coefficient i j hij L)) ∧
    (∀ (H H' : DerivedCategory
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (L L' : DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
        (v : H' ⟶ H)
        (f : (closedTransportDirectImage P.Coefficient i j hij).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.obj
            H) ⟶ L) (u : L ⟶ L'),
      DerivedCategory.TStructure.t.plus H → DerivedCategory.TStructure.t.plus H' →
      closedTransportAllowedTarget P.Coefficient i L →
      closedTransportAllowedTarget P.Coefficient i L' →
      closedTransportHomMap P.Coefficient i j hij H' L'
          ((closedTransportDirectImage P.Coefficient i j hij).map
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.map
              v) ≫ f ≫ u) =
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.map v ≫
          closedTransportHomMap P.Coefficient i j hij H L f ≫
          (closedTransportExceptional P.Coefficient i).map u) ∧
    (∀ (L L' : DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) (u : L ⟶ L'),
      closedTransportAllowedTarget P.Coefficient i L →
      closedTransportAllowedTarget P.Coefficient i L' →
      (closedTransportDirectImage P.Coefficient i j hij).map
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.map
            ((closedTransportEtaleValue P.Coefficient i).map u)) ≫
          closedTransportCounit P.Coefficient i j hij L' =
        closedTransportCounit P.Coefficient i j hij L ≫ u))
      (_hfin := Equiv.ulift.finite_iff.mpr
        (Padic.finite_coefficientExtensionRing
          P.coefficients.l P.extension P.level P.level_pos)) := by
  sorry

end AlgebraicGeometry.ProEtale
