/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.Compactification.CategoryBaseChange
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.UnboundedClassicalComparison
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.CharP.Basic

/-!
# Transport and uniqueness for classical exceptional adjunctions

Source: the opening comparison paragraph and the four-Hom calculation of
`sk-lem-geo-affine-local`, including its unit and counit normalizations.
(blueprint: lem-geo-affine-local-classical-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale

/-- The fixed comparison functor induces an equivalence onto the full classical subcategory.
Source: the opening comparison step of `sk-lem-geo-affine-local`
(blueprint: lem-geo-affine-local-classical-transport).

Proof: lift the exact comparison to its classical essential image. The unbounded comparison
is fully faithful, and every classical object is isomorphic to its image. Thus the lift is
fully faithful and essentially surjective. Its associated equivalence has exactly the lifted
functor, so composing it with the full-subcategory inclusion gives the original functor
by definitional equality. This also covers the empty scheme and the zero coefficient ring. -/
theorem nonempty_classicalComparisonData
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ell : A) ^ r = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] :
    Nonempty (ClassicalComparisonData X A) := by
  obtain ⟨himage, _, hsurj⟩ :=
    finiteClassicalUnboundedComparison k hbase ell hEll A hA X
  obtain ⟨⟨ff⟩, _, _⟩ := unboundedClassicalComparison.{u, u} k hbase hEll A
    (by obtain ⟨r, _, hr⟩ := hA; exact ⟨r, hr⟩) (𝟙 X)
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let P : ObjectProperty (ProEtaleD X A) := IsClassicalComplexFor X A
  let L := ObjectProperty.lift P F himage
  have : F.Full := ff.full
  have : F.Faithful := ff.faithful
  have : L.EssSurj := ⟨fun K ↦ by
    obtain ⟨M, ⟨e⟩⟩ := hsurj K.obj K.property
    exact ⟨M, ⟨P.isoMk e⟩⟩⟩
  have : L.Full := inferInstanceAs (ObjectProperty.lift P F himage).Full
  have : L.Faithful := inferInstanceAs (ObjectProperty.lift P F himage).Faithful
  have : L.IsEquivalence := {}
  exact ⟨⟨L.asEquivalence, rfl⟩⟩

/-- Counit normalization determines the unique comparison of two right adjoints.
Source: the four-Hom calculation and its counit normalization
(blueprint: lem-geo-affine-local-classical-transport).

Proof: right-adjoint uniqueness supplies an isomorphism and its counit equation. If another
isomorphism has that equation, the inverse of the second Hom adjunction takes both component
maps to the first counit. Injectivity of this bijection identifies the components, then
naturality and isomorphism extensionality identify the isomorphisms. -/
theorem existsUnique_rightAdjoint_counit
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    {L : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L ⊣ R') :
    ∃! e : R ≅ R', ∀ N,
      L.map (e.hom.app N) ≫ a'.counit.app N = a.counit.app N := by
  refine ⟨a.rightAdjointUniq a', fun N ↦
    a.rightAdjointUniq_hom_app_counit a' N, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (a'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, he N,
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]

/-- The normalized four-Hom comparison includes both adjunction equations.
Source: clause (2) of `sk-lem-geo-affine-local`
(blueprint: lem-geo-affine-local-classical-transport). -/
def classicalCompositeComparisonOfIso
    {C E D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} E]
    [Category.{u + 1} D] {L : C ⥤ D} {R : D ⥤ C}
    {L' : E ⥤ D} {R' : D ⥤ E} {LP : E ⥤ C} {P : C ⥤ E}
    (a : L ⊣ R) (a' : L' ⊣ R') (ap : LP ⊣ P) (c : LP ⋙ L ≅ L') :
    ClassicalCompositeComparison L R L' R' LP P a a' ap where
  composite := c
  comparison := ((ap.comp a).ofNatIsoLeft c).rightAdjointUniq a'
  canonical := rfl
  unit_compatibility := fun K ↦
    ((ap.comp a).ofNatIsoLeft c).unit_rightAdjointUniq_hom_app a' K
  counit_compatibility := fun Y ↦
    ((ap.comp a).ofNatIsoLeft c).rightAdjointUniq_hom_app_counit a' Y

/-- Conjugate an ordinary derived functor through the classical equivalences. Its native
comparison follows from a supplied ordinary/native square.
Source: the comparison transport in the opening step of `sk-lem-geo-affine-local`
(blueprint: lem-geo-affine-local-classical-transport). -/
def classicalTransportNative
    {P S : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A)
    (F : EtaleD P A ⥤ EtaleD S A) (G : ProEtaleD P A ⥤ ProEtaleD S A)
    (e : F ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ⋙ G) :
    (CP.equivalence.inverse ⋙ F ⋙ CS.equivalence.functor) ⋙
        (ObjectProperty.ι (IsClassicalComplexFor S A)) ≅
      (ObjectProperty.ι (IsClassicalComplexFor P A)) ⋙ G :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (eqToIso CS.native) ≪≫ e) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (eqToIso CP.native.symm) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight CP.equivalence.counitIso _ ≪≫
        Functor.leftUnitor _) _

/-- Exact pullback restricts to the classical categories, with the specified native formula.
Source: the comparison transport for clause (2)
(blueprint: lem-geo-affine-local-classical-transport). -/
def classicalUpperStarDataOfComparison
    {P S : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A) (g : P ⟶ S) :
    ClassicalUpperStarData P S A g where
  functor := CS.equivalence.inverse ⋙
    (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙ CP.equivalence.functor
  ambient := classicalTransportNative CS CP _ _ (unboundedDirectImagePullbackIso A g).symm

/-- A normalized counit square forces the unit square for the same comparison maps.
Source: clause (1), final sentence, and the mate calculation in clause (2)
(blueprint: lem-geo-affine-local-classical-transport). -/
def classicalAdjunctionComparisonOfCounit
    {C D C' D' : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} C'] [Category.{u + 1} D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {bC : C ⥤ C'} {bD : D ⥤ D'} (a : L ⊣ R) (a' : L' ⊣ R')
    (left : L ⋙ bD ≅ bC ⋙ L') (right : R ⋙ bC ≅ bD ⋙ R')
    (hc : ∀ Y : D, bD.map (a.counit.app Y) = left.hom.app (R.obj Y) ≫
      L'.map (right.hom.app Y) ≫ a'.counit.app (bD.obj Y)) :
    ClassicalAdjunctionComparison L R L' R' bC bD a a' where
  left_comparison := left
  right_comparison := right
  counit_base_change := hc
  unit_base_change := by
    let t : TwoSquare bC L L' bD := .mk _ _ _ _ left.inv
    have ht : (mateEquiv a a' t).natTrans = right.hom := by
      apply NatTrans.ext
      funext Y
      apply (a'.homEquiv _ _).symm.injective
      simp only [Adjunction.homEquiv_counit]
      change L'.map ((mateEquiv a a' t).app Y) ≫ a'.counit.app (bD.obj Y) = _
      rw [mateEquiv_counit]
      change left.inv.app (R.obj Y) ≫ bD.map (a.counit.app Y) = _
      rw [hc Y]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    intro X
    have hu := unit_mateEquiv a a' t X
    change bC.map (a.unit.app X) ≫ (mateEquiv a a' t).natTrans.app (L.obj X) =
      a'.unit.app (bC.obj X) ≫ R'.map (left.inv.app X) at hu
    rw [ht] at hu
    rw [← Category.assoc, hu, Category.assoc, ← R'.map_comp]
    simp

/-- Transport an ordinary exceptional adjunction, retaining its actual counit and the
native compact-support comparison.
Source: clause (2), opening comparison and four-Hom argument
(blueprint: lem-geo-affine-local-classical-transport). -/
def classicalExceptionalDataOfAdjunction
    {P S : Scheme.{u}} {A : Type (u + 1)} [CommRing A] {f : P ⟶ S}
    (c : Compactification f) (CP : ClassicalComparisonData P A)
    (CS : ClassicalComparisonData S A)
    (R : EtaleD S A ⥤ EtaleD P A)
    (a : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R)
    (e : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) :
    ClassicalExceptionalAdjunctionData P S A f c CP CS
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) where
  left := CP.equivalence.inverse ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CS.equivalence.functor
  right := CS.equivalence.inverse ⋙ R ⋙ CP.equivalence.functor
  adjunction := (CP.equivalence.symm.toAdjunction.comp a).comp CS.equivalence.toAdjunction
  left_native := rfl
  left_formula := classicalTransportNative CP CS _ _ e
  left_eq := rfl
  left_etale := classicalTransportModel CP CS _ _ rfl
  left_etale_normalization := rfl
  right_counit_normalized := fun _ adjJ ↦ existsUnique_rightAdjoint_counit _ adjJ

end AlgebraicGeometry.ProEtale
