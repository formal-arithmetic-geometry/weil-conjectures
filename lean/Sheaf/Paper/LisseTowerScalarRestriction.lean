/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData

/-! # The scalar square for the fixed finite coefficient realization

Source: Stacks Project, Tags 03DA, 06YY, 099Z and 09B1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization

/-- The ordinary functor whose exact localization is the fixed realization.
Source: Stacks Tags 03CY and 06YY
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerFixedSheafRealization {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (constantAdicQuotientMap d.ideal n)) ⋙
    lisseTowerFiniteSheafRealization f d n

instance lisseTowerFixedSheafRealization_additive {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFixedSheafRealization f d n).Additive := by
  unfold lisseTowerFixedSheafRealization
  infer_instance

instance lisseTowerFixedSheafRealization_limits {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteLimits (lisseTowerFixedSheafRealization f d n) := by
  unfold lisseTowerFixedSheafRealization
  infer_instance

instance lisseTowerFixedSheafRealization_colimits {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    PreservesFiniteColimits (lisseTowerFixedSheafRealization f d n) := by
  unfold lisseTowerFixedSheafRealization
  infer_instance

/-- The exact composition comparison; it does not change the fixed realization.
Source: Stacks Tag 05RU
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerFixedRealizationIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (lisseTowerFixedSheafRealization f d n).mapDerivedCategory ≅
      lisseTowerFixedRealization f d n := by
  unfold lisseTowerFixedSheafRealization lisseTowerFixedRealization normalizationRestrict
  exact Functor.mapDerivedCategoryCompIso _ _

/-- Forget the scalar action after associated-module-sheaf realization.
Source: Stacks Tag 03CY
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerCoefficientRealizationForgetIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B R : Type (u + 1)) [CommRing B] [CommRing R] (q : R →+* B)
    (S : Sheaf J RingCat.{u + 1})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙
        ProEtale.finiteCoefficientModulePresheaf C R ⋙
        PresheafOfModules.sheafification a)) ⋙ SheafOfModules.toSheaf S ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) := by
  let G := sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
  change (G ⋙ sheafToPresheaf _ _) ⋙ presheafToSheaf _ _ ≅ G
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (asIso (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit) ≪≫
      Functor.rightUnitor G

/-- Forgetting the scalar action identifies realization with the original abelian sheaf.
The identification is the counit of ordinary abelian sheafification.
Source: Stacks Tag 03CY
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerFixedForgetIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerFixedSheafRealization f d n ⋙ SheafOfModules.toSheaf _ ≅
      sheafCompose (ProEt.topology Z)
        (forget₂ (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) AddCommGrpCat.{u + 1}) := by
  exact lisseTowerCoefficientRealizationForgetIso (ProEt.topology Z) _ _
    (constantAdicQuotientMap d.ideal n) _ (lisseTowerFiniteScalarMap f d n)

/-- Scalar restriction does not change the underlying abelian sheaf.
Source: Stacks Tag 03CZ
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerRestrictForgetIso {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (a : R ⟶ S) :
    pbcRestrict a ⋙ SheafOfModules.toSheaf _ ≅ SheafOfModules.toSheaf _ := Iso.refl _

/-- The etale comparison followed by the prescribed fixed realization.
Source: Stacks Tags 099Z and 03CY
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
abbrev lisseTowerEtaleRealization {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) Z).mapDerivedCategory ⋙
      lisseTowerFixedRealization f d n

/-- The type of the ordinary consecutive scalar square.
Source: Stacks Tags 03DA and 06YY
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
abbrev LisseTowerScalarSquare {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  sheafCompose (ProEt.topology Z)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n)) ⋙
        lisseTowerFixedSheafRealization f d (n + 1) ≅
    lisseTowerFixedSheafRealization f d n ⋙
      pbcRestrict ((adicTowerInverseImage f).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))

/-- Fixed-ring restriction preserves the underlying abelian sheaf.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerFixedRestrictForgetIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        sheafCompose J (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}) := Iso.refl _

/-- Normalize a scalar square against specified comparisons of underlying objects.
Keeping this generic prevents reduction of the concrete adic coefficient constructions.
Source: Stacks Tag 03DA
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def lisseTowerScalarSquareNormalized
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} {G : C ⥤ E} {G' : C' ⥤ E}
    (c : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G) : Prop :=
  (Functor.isoWhiskerRight c H' ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F r ≪≫ a).hom =
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q a' ≪≫ q).hom

/-- The square is normalized by the identity on the original fixed sections.
Source: Stacks Tags 03CY and 03DA
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def LisseTowerScalarSquareSections {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : Prop :=
  lisseTowerScalarSquareNormalized c
    (lisseTowerRestrictForgetIso ((adicTowerInverseImage f).map
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))))
    (lisseTowerFixedForgetIso f d n) (lisseTowerFixedForgetIso f d (n + 1))
    (lisseTowerFixedRestrictForgetIso (ProEt.topology Z) (lisseTowerEtaleQuotient d n))

/-- Localize the ordinary square and paste the comparison coefficient mate.
Source: Stacks Tags 05RU and 03DA
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
def lisseTowerEtaleScalarIso {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) :
    normalizationRestrict Z.smallEtaleTopology (lisseTowerEtaleQuotient d n) ⋙
        lisseTowerEtaleRealization f d (n + 1) ≅
      lisseTowerEtaleRealization f d n ⋙
        pbcDerivedRestrict ((adicTowerInverseImage f).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) := by
  unfold pbcDerivedRestrict
  let k := Functor.isoWhiskerLeft
      (normalizationRestrict (ProEt.topology Z) (lisseTowerEtaleQuotient d n))
      (lisseTowerFixedRealizationIso f d (n + 1)).symm ≪≫
    Functor.mapDerivedCategorySquareIso c ≪≫
    Functor.isoWhiskerRight (lisseTowerFixedRealizationIso f d n)
      (pbcRestrict ((adicTowerInverseImage f).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).mapDerivedCategory
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (localIsomorphismComparisonCoefficients (lisseTowerEtaleQuotient d n))
      (lisseTowerFixedRealization f d (n + 1)) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ k ≪≫
    (Functor.associator _ _ _).symm

/-- Reflection of one actual normalized transition on every etale source through
its section-normalized coefficient square.
Source: Stacks Tags 06YY, 099Z and 09B1
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def LisseTowerScalarSquareReflects {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (c : LisseTowerScalarSquare f d n) : Prop :=
  ∀ (M : AdicTower X d)
    (C : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))))
    (C' : DerivedCategory
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (_hC : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C))
    (_hC' : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj C'))
    (e : (lisseTowerEtaleRealization f d (n + 1)).obj C ≅
      (adicTowerPullback f ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1)))
    (e' : (lisseTowerEtaleRealization f d n).obj C' ≅
      (adicTowerPullback f ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology
      (lisseTowerEtaleQuotient d n)).obj C'),
    (lisseTowerEtaleRealization f d (n + 1)).map δ ≫
        (lisseTowerEtaleScalarIso f d n c).hom.app C' ≫
        (pbcDerivedRestrict ((adicTowerInverseImage f).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map e'.hom =
      e.hom ≫ adicTowerRestrictedTransition d f M (n + 1) n (Nat.le_succ n) →
    ∀ V : Z.Etale, Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Z
        (lisseTowerEtaleQuotient d n) δ V)))

/-- Local universality of constant algebraic normalization arrows at this quotient.
Source: Stacks Tags 06YY and 03ED
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction). -/
@[irreducible] def LisseTowerConstantLocalUniversal (Z : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) : Prop :=
  ∀ (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk k)) →
      ∀ V : Z.Etale, Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow Z
          (lisseTowerEtaleQuotient d n)
          (normalizationConstantArrow Z.smallEtaleTopology (lisseTowerEtaleQuotient d n) k) V)))

/-- The consecutive fixed-realization square is uniquely normalized on sections and
reflects the universality of an actual normalized transition. This is a single
coefficient-change statement; it constructs neither a descended arrow nor any
realization or marking on further pro-etale objects.

Source: Stacks Project, Tags 03CY, 03DA, 06YY, 099Z and 09B1.
(blueprint: lem-weil-pbc-lisse-tower-scalar-restriction).

Proof: the completion quotient maps commute with consecutive quotient homomorphisms.
The constant-ring comparisons are natural in that diagram, as are inverse images.
Consequently the two associated module sheaves in the square are sheafifications of
the same additive presheaf with the same restricted scalar action. The identity on
that presheaf extends uniquely to an isomorphism of module sheaves. Its action on the
sheafification unit is the section equation; local generation proves uniqueness and
naturality. Restriction of scalars and realization are exact, so exact localization
produces the displayed derived square. For reflection, the inverse scalar mate of
this square is invertible: compute extension on flat resolutions, where its component
is the tensor identity, and use exact sheafification. The same computation applies
to comparison inverse image and to inverse image along f. The supplied descent equation
therefore identifies the image of the scalar adjunct of delta with the pulled
normalization isomorphism of M. Comparison is exact and conservative (its unit is
invertible on sheaves), and fixed realization is an equivalence, so this adjunct is
invertible. It is thus a universal scalar arrow. Restriction to each etale source
has the same invertible scalar mate: on a flat resolution both orders give the same
sheafified tensor product. The mate unit identity identifies the resulting unit arrow
with etaleIsomorphismNormalizationArrow, so that arrow is universal as well.
For a universal algebraic k, exact constant realization is universal by the existing
normalizationConstantArrow_isUniversal theorem. The same inverse-image tensor
calculation proves its universality on every etale source. This is the final conjunct.
No restriction-coherence assertion is included here; that equation is proved separately.
Empty bases and zero objects are included, with no finite Tor-amplitude assumption. -/
theorem lisseTower_scalar_restriction {X Z : Scheme.{u}} (f : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ∃! c : LisseTowerScalarSquare f d n,
      LisseTowerScalarSquareSections f d n c ∧ LisseTowerScalarSquareReflects f d n c ∧
        LisseTowerConstantLocalUniversal Z d n := by
  sorry

end AlgebraicGeometry.Scheme
