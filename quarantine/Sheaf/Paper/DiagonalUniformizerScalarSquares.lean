/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.DiagonalCoefficientDiagrams
public import Sheaf.Paper.CanonicalDiagonalRightDerived
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Paper.NormalizedScalarRestrictionPush
import Sheaf.Paper.InternalPullNormalizationExistence
import Sheaf.Paper.ComapUpperStarIsoMate

/-! # Perfect uniformizer reduction and direct image

Source: diagonal tower coefficient changes, paragraph (1), cofinal uniformizer quotients.
(blueprint: lem-diagonal-uniformizer-scalar-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a v w wc
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint Functor.rightDerivedFunctor
  Functor.mapDerivedCategory RestrictionSquare.mate Functor.leftDerivedFunctor quotientMap

private theorem mate_left_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L M : A ⥤ B} {R : B ⥤ A} {L' M' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ M) (e' : L' ≅ M')
    (s : G ⋙ M' ⟶ M ⋙ H) :
    (mateEquiv (adj.ofNatIsoLeft e) (adj'.ofNatIsoLeft e')
      (TwoSquare.mk _ _ _ _ s)).natTrans =
      (mateEquiv adj adj'
        (TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft G e'.hom ≫ s ≫ Functor.whiskerRight e.inv H))).natTrans := by
  ext K
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

private theorem changeRightModel
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG RG' : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (s : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG ordinary) :
    Nonempty (DiagonalTrace.ExactSquareOfUniverses F G U V RF RG' ordinary) := by
  let := RG.universal
  let := RG'.universal
  let e := Functor.rightDerivedUnique RG.R RG'.R RG.η RG'.η
    (HomologicalComplex.quasiIso C (.up ℤ))
  have he (P : CochainComplex C ℤ) :
      RG.η.app P ≫ e.hom.app (DerivedCategory.Q.obj P) = RG'.η.app P := by
    simpa only [e, Functor.rightDerivedNatIso_hom, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app RG.R RG'.R RG.η RG'.η
        (HomologicalComplex.quasiIso C (.up ℤ)) (𝟙 _) P
  refine ⟨{ iso := s.iso ≪≫ Functor.isoWhiskerLeft U.mapDerivedCategory e
            normalization := ?_ }⟩
  intro P
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc]
  rw [← e.hom.naturality]
  have hs := congrArg (fun k ↦ k ≫ e.hom.app
    (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P)))
    (s.normalization P)
  simpa only [Functor.comp_obj, Category.assoc, he] using hs

private theorem exactDerivedAdj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f) := by
  unfold CondensedRing.derivedUpperStarLowerStarAdjunction
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  refine Adjunction.derived_eq_ofNatIsoLeft
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

private theorem canonicalRestrictionSquare
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S) :
    Nonempty (RestrictionSquare a f
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f))
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))) := by
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules Λ Z) := fun Z ↦ by
    have := IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence Λ Z)
    exact HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules Λ' Z) := fun Z ↦ by
    have := IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence Λ' Z)
    exact HasDerivedCategory.ofIsGrothendieckAbelian _
  obtain ⟨b, hb⟩ := QuotientChange.internal_pull_normalization_exists a f
  let iso :
      (CondensedRing.lowerStar Λ' f).rightDerivedFunctor ⋙
        (Mod.comap (coefficientMap a S)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ f).rightDerivedFunctor := by
    have e := QuotientChange.restrictPush a f b
    unfold QuotientChange.F CondensedRing.moduleObjectDerivedPushforward at e
    exact e
  let rho :
      (CondensedRing.lowerStar Λ' f).rightDerivedFunctor ⋙
        (Mod.comap (coefficientMap a S)).mapDerivedCategory ⟶
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙
        (CondensedRing.lowerStar Λ f).rightDerivedFunctor := by
    have t := QuotientChange.scalarRestrictionPush a f
    unfold QuotientChange.F CondensedRing.moduleObjectDerivedPushforward at t
    exact t
  unfold RestrictionSquare canonicalDiagonalRightDerived
  refine ⟨{ iso := ?_, normalization := ?_ }⟩
  · exact iso
  · intro P
    have h := derived_mate_factors
      (CondensedRing.upperStarLowerStarAdjunction Λ' f)
      (CondensedRing.upperStarLowerStarAdjunction Λ f)
      (CondensedRing.comapUpperStarIso a f).symm P
    simp only [Iso.symm_hom] at h
    rw [CondensedRing.comapUpperStarIso_mate] at h
    have hm :
        (mateEquiv
          (Adjunction.mapDerivedCategoryRightDerivedAdjunction
            (CondensedRing.upperStarLowerStarAdjunction Λ' f))
          (Adjunction.mapDerivedCategoryRightDerivedAdjunction
            (CondensedRing.upperStarLowerStarAdjunction Λ f))
          (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso a f).inv)).natTrans =
        rho := by
      dsimp only [rho]
      unfold QuotientChange.scalarRestrictionPush QuotientChange.scalarRestrictionPull
        QuotientChange.adj
        QuotientChange.L QuotientChange.F CondensedRing.moduleObjectDerivedPullback
        CondensedRing.moduleObjectDerivedPushforward
        CondensedRing.derivedUpperStarLowerStarAdjunction
      rw [exactDerivedAdj, exactDerivedAdj, mate_left_transport]
      congr 2
      ext K
      simp only [TwoSquare.mk, TwoSquare.natTrans, id, Iso.trans_inv, Iso.symm_inv,
        Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
        CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    have he : iso.hom = rho := by
      have t := QuotientChange.normalized_scalar_restriction_push a f b hb
      unfold QuotientChange.F CondensedRing.moduleObjectDerivedPushforward at t
      exact t
    rw [← he] at hm
    have hd :
        ((Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap a S))
          (CondensedRing.upperStar Λ f)).symm ≪≫
          Functor.mapDerivedCategoryNatIso (CondensedRing.comapUpperStarIso a f).symm ≪≫
          Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ' f)
            (Mod.comap (coefficientMap a X))).hom =
        (CondensedRing.derivedComapUpperStarIso a f).inv := by
      simp only [CondensedRing.derivedComapUpperStarIso, Iso.trans_inv, Iso.symm_inv,
        Iso.trans_hom, Iso.symm_hom,
        Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rw [hd] at h
    have hmP := NatTrans.congr_app hm (DerivedCategory.Q.obj P)
    erw [hmP] at h
    simpa only [canonicalDiagonalUnit, chainDerivedUnit,
      Functor.rightDerivedFunctorUnitQ] using h

private theorem restrictionSquare
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f)) :
    Nonempty (RestrictionSquare a f R
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))) := by
  obtain ⟨s⟩ := canonicalRestrictionSquare (Λ := Λ) (Λ' := Λ') a f
  exact changeRightModel (CondensedRing.lowerStar Λ' f) (CondensedRing.lowerStar Λ f)
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a S))
    (canonicalDiagonalRightDerived _) (canonicalDiagonalRightDerived _) R
    (CondensedRing.comapLowerStarIso a f) s

attribute [local irreducible] canonicalDiagonalRightDerived

/-- A scalar/direct-image square with invertible mate on every complex.
Keeping the coefficient rings as parameters shares the derived-category instances
in the concrete uniformizer theorem. Source: coefficient changes paragraph (1).
(blueprint: lem-diagonal-uniformizer-scalar-squares). -/
structure ScalarSquareIsomorphisms
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f)) where
  square : RestrictionSquare a f R
    (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))
  isIso : ∀ K : DerivedCategory (Modules Λ X), IsIso ((square.mate a).app K)

-- The uniformizer hypothesis stays in the public interface; square existence is general.
set_option linter.unusedVariables false in
/-- The quotient reduction admits a full-unit-normalized restriction/direct-image
square with the canonical quotient right-derived model.

Proof: construct the two-term finite-free resolution of the actual quotient by
the power of the chosen uniformizer, pull it back to the two schemes, and use
the universal property of the two right-derived functors to transport the exact
restriction/direct-image comparison. The cochain-unit equation fixes the square
and gives the required normalization. This is the square-existence part of the
uniformizer scalar-square argument.
(blueprint: lem-diagonal-uniformizer-scalar-squares). -/
theorem diagonal_uniformizer_restriction_square
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f)) :
    Nonempty (RestrictionSquare (quotientMap l E π n) f R
      (canonicalDiagonalRightDerived
        (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f))) := by
  exact restrictionSquare
    (Λ := Profinite.padicIntegersRingObj.{u} l E.1)
    (Λ' := Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
    (quotientMap.{u} l E π n) f R

/-- The scalar mate of a normalized uniformizer-quotient square is invertible
on every integral derived object.

Proof: identify the mate after exact restriction with the projection comparison
for the two-term finite-free quotient resolution. It is invertible on each free
term, hence on the cone by the triangulated comparison theorem. Exact restriction
reflects isomorphisms, so the original mate is invertible for every unbounded
complex. This is the mate-invertibility part of the uniformizer scalar-square
argument and assumes the normalized square as input.
(blueprint: lem-diagonal-uniformizer-scalar-squares). -/
theorem diagonal_uniformizer_restriction_mate_isIso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f))
    (square : RestrictionSquare (quotientMap l E π n) f R
      (canonicalDiagonalRightDerived
        (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f))) :
    ∀ K : DerivedCategory
      (Modules (Profinite.padicIntegersRingObj.{u} l E.1) X),
      IsIso ((square.mate (quotientMap l E π n)).app K) := by
  sorry

/-- Uniformizer reduction has a normalized restriction/direct-image square whose
scalar mate is invertible on every complex.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), and the finite free
coefficient argument; Stacks Tags 070G, 070Y and 0D6E.
(blueprint: lem-diagonal-uniformizer-scalar-squares).

Proof: The quotient O_E/(pi^(n+1)) has the two-term free O_E-resolution with differential
pi^(n+1). The integer ring is a domain and the specified uniformizer is nonzero, so this
map is injective. Continuous functions on a profinite set preserve this short exact
sequence: finite residue classes have locally constant lifts on a finite clopen
partition, and the inverse of multiplication by pi^(n+1) on its image is continuous.
Pull back from the profinite point to either scheme by the exact monoidal inverse
image. This gives the same two-term free resolution of the pulled-back quotient ring.

Exact restriction of coefficients commutes with ordinary direct image. Compute derived
direct image using resolutions acyclic for the underlying ringed-topos direct image;
restriction need not preserve injectives. The universal full right-derived units give
the normalized derived restriction isomorphism, also for an arbitrary full universal
integral derived model R. This constructs s and its full-unit normalization.

After exact restriction to integral coefficients, the scalar mate is the projection
comparison for the two-term resolution just constructed. For each regular free term
this is the unitor, hence invertible. The derived direct images are triangulated, so
the comparison on their cones is invertible as well. This proves the projection
comparison for tensoring any input complex with the quotient resolution, without a
bound on that complex. The scalar-adjunction unit and the full-unit normalization of
s identify this comparison with the restriction of s.mate. Exact restriction of scalar
coefficients reflects isomorphisms, so s.mate is invertible. This is also the finite
free scalar perfect-model argument formalized by integralFiniteScalarPerfectModel;
its comparison must be identified with the normalized square used here.
No properness, projective-line cohomology, quotient flatness, trace, or Tate line
is required. The exponent is n+1, so n=0 is the residue field case, and ramification
changes only the nonzero scalar in the differential.
-/
theorem diagonal_uniformizer_scalar_squares
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj.{u} l E.1) f)) :
    Nonempty (ScalarSquareIsomorphisms (quotientMap l E π n) f R) := by
  obtain ⟨square⟩ := diagonal_uniformizer_restriction_square l E π hπ n f R
  refine ⟨{ square := square, isIso := ?_ }⟩
  exact diagonal_uniformizer_restriction_mate_isIso l E π hπ n f R square

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
