/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.LocalFrobeniusTrace
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible

/-! # Locally constructible adic sheaves as compatible local heart objects

Source: Bhatt--Scholze, Section 6.8, Definitions 6.8.6 and 6.8.8,
Propositions 6.8.4(5) and 6.8.14, and Remark 6.8.15
(blueprint: def-dl-a1-locally-constructible-adic-heart).

On a locally finite-type k0-scheme, separated finite-type opens form a basis.
A locally constructible sheaf is specified on this basis, with the canonical completed
restriction identifications and their cocycle. Different opens may use different finite
coefficient fields. Morphisms commute with every restriction identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (T : Over (Spec (.of D.k₀)))

/-- The coefficient prime is a unit in the finite base field itself.
Source: blueprint coefficient conventions
(blueprint: def-dl-a1-locally-constructible-adic-heart).
Proof: its image in the fixed algebraic closure is the unit finiteFieldDatumPrimeUnit.
The field embedding reflects units, giving the asserted unit in k0. -/
theorem dlAdicBasePrimeUnit : IsUnit (c.l : D.k₀) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  exact (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact c.different ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : c.l.Prime)).1 hdiv).symm)

/-- Transport the base-field unit to each residue field through the structure map.
Source: BS 6.8.6 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
@[instance_reducible]
def dlAdicBaseResidueInvertible (S : Scheme.{u}) [S.Over (Spec (.of D.k₀))] :
    ∀ x : S, Invertible (c.l : S.residueField x) :=
  fun x ↦ (by
    simpa using (dlAdicBasePrimeUnit D c).map
      ((S ↘ Spec (.of D.k₀)).residueFieldAlgebraMap x) :
        IsUnit (c.l : S.residueField x)).invertible

/-- Transport the same base-field unit through the fixed algebraic closure and
the geometric structure map. This supplies completed pullback at every Spec k point.
Source: BS 6.8.14 and the global finite-field coefficient conventions
(blueprint: def-dl-a1-locally-constructible-adic-heart). -/
@[instance_reducible]
def dlAdicGeometricResidueInvertible (S : Scheme.{u}) [S.Over (Spec (.of D.k))] :
    ∀ x : S, Invertible (c.l : S.residueField x) :=
  fun x ↦ (by
    simpa using (dlAdicBasePrimeUnit D c).map
      (((S ↘ Spec (.of D.k)).residueFieldAlgebraMap x).comp (algebraMap D.k₀ D.k)) :
        IsUnit (c.l : S.residueField x)).invertible

/-- The separated finite-type open basis, including the empty open.
Source: BS 6.8.6, Zariski-local version
(blueprint: def-dl-a1-locally-constructible-adic-heart). -/
def DlAdicFiniteOpen :=
  {U : T.left.Opens // LocallyOfFiniteType (U.ι ≫ T.hom) ∧
    QuasiCompact (U.ι ≫ T.hom) ∧ IsSeparated (U.ι ≫ T.hom)}

/-- Actual completed common-stage restriction along an inclusion of basis opens.
Source: BS Remark 6.8.15 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
def dlAdicOpenPull {U V : DlAdicFiniteOpen D T} (h : U.val ≤ V.val) :
    generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar V.val.toScheme ⥤
      generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar U.val.toScheme :=
  @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ (T.left.homOfLE h)
    (dlAdicBaseResidueInvertible D c U.val.toScheme)
    (dlAdicBaseResidueInvertible D c V.val.toScheme)

/-- The restriction compositor is the existing integral-normalized compositor,
with the equality of open inclusions inserted at its source.
Source: BS Remark 6.8.15 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
def dlAdicOpenPullComp {U V W : DlAdicFiniteOpen D T}
    (h : U.val ≤ V.val) (g : V.val ≤ W.val)
    (K : generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar W.val.toScheme) :
    (dlAdicOpenPull D c T (h.trans g)).obj K ≅
      (dlAdicOpenPull D c T h).obj ((dlAdicOpenPull D c T g).obj K) := by
  letI := dlAdicBaseResidueInvertible D c U.val.toScheme
  letI := dlAdicBaseResidueInvertible D c V.val.toScheme
  letI := dlAdicBaseResidueInvertible D c W.val.toScheme
  exact eqToIso (congrArg
      (fun f ↦ (commonStageDerivedPullback c.l c.Qbar f).obj K)
      (T.left.homOfLE_homOfLE h g).symm) ≪≫
    localQbarPullbackComposition c.l c.Qbar (T.left.homOfLE h) (T.left.homOfLE g) K

/-- Cartesian local heart data on every separated finite-type open. The cocycle includes
repeated opens; in particular it forces the usual identity normalization. This is the
basis description of a locally constructible adic sheaf, rather than a global choice
of a finite coefficient stage.
Source: BS 6.8.4(5), 6.8.6 and 6.8.14
(blueprint: def-dl-a1-locally-constructible-adic-heart). -/
structure DlAdicLocalData where
  value : ∀ U : DlAdicFiniteOpen D T, sfCommonStageHeart c.l U.val.toScheme c.Qbar
  restriction : ∀ {U V : DlAdicFiniteOpen D T} (h : U.val ≤ V.val),
    (dlAdicOpenPull D c T h).obj (value V).obj ≅ (value U).obj
  cocycle : ∀ {U V W : DlAdicFiniteOpen D T} (h : U.val ≤ V.val) (g : V.val ≤ W.val),
    (dlAdicOpenPullComp D c T h g (value W).obj).hom ≫
        (dlAdicOpenPull D c T h).map (restriction g).hom ≫ (restriction h).hom =
      (restriction (h.trans g)).hom

/-- Families of local heart arrows before imposing restriction compatibility.
Source: BS 6.8, descent (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
abbrev DlAdicLocalRaw :=
  InducedCategory (∀ U : DlAdicFiniteOpen D T, sfCommonStageHeart c.l U.val.toScheme c.Qbar)
    (fun F : DlAdicLocalData D c T ↦ F.value)

/-- A morphism is a family commuting with the canonical local identifications.
Source: BS 6.8, descent (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
def dlAdicLocalCompatible : MorphismProperty (DlAdicLocalRaw D c T) :=
  fun F G f ↦ ∀ {U V : DlAdicFiniteOpen D T} (h : U.val ≤ V.val),
    (F.restriction h).hom ≫ (f.hom U).hom =
      (dlAdicOpenPull D c T h).map (f.hom V).hom ≫ (G.restriction h).hom

/-- Compatibility is closed under identities and composition.
Source: BS 6.8, descent (blueprint: def-dl-a1-locally-constructible-adic-heart).
Proof: the identity equations are naturality of identities. For a composite, substitute
first the compatibility of the first arrow and then of the second; associativity and
preservation of composition by completed pullback give the required square. -/
theorem dlAdicLocalCompatible_multiplicative :
    (dlAdicLocalCompatible D c T).IsMultiplicative := by
  refine { id_mem := ?_, comp_mem := ?_ }
  · intro F U V h
    simp
  · intro F G H f g hf hg U V h
    dsimp [dlAdicLocalCompatible] at hf hg ⊢
    change (F.restriction h).hom ≫ ((f.hom U).hom ≫ (g.hom U).hom) = _
    rw [← Category.assoc, hf h, Category.assoc, hg h]
    simp [Functor.map_comp, Category.assoc]

/-- The preceding closure proof supplies the category laws for compatible arrows.
Source: BS 6.8, descent (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
instance dlAdicLocalCompatibleMultiplicative :
    (dlAdicLocalCompatible D c T).IsMultiplicative :=
  dlAdicLocalCompatible_multiplicative D c T

/-- The category of locally constructible common-stage adic sheaves; objects and arrows
are the explicit cartesian local data above. No global finite-stage condition is imposed.
Source: BS 6.8.4(5), 6.8.6 and 6.8.14
(blueprint: def-dl-a1-locally-constructible-adic-heart). -/
abbrev DlLocallyConstructibleAdicHeart := WideSubcategory (dlAdicLocalCompatible D c T)

/-- The zero family commutes with all restriction maps.
Source: BS Remark 6.8.15 (blueprint: def-dl-a1-locally-constructible-adic-heart).
Proof: completed pullback on an open is ordinary additive inverse image at the
integral stage; its rational and common-stage map formulas preserve zero.
Both composites in the compatibility square are therefore zero. -/
theorem dlAdicLocalCompatible_zero (F G : DlAdicLocalRaw D c T) :
    dlAdicLocalCompatible D c T (InducedCategory.homMk (fun U ↦ (0 : F.value U ⟶ G.value U))) :=
  by
    have hz (S : Scheme.{u})
        (A B : GeneralAlgebraicallyClosedCoefficients.Pair c.l c.Qbar S)
        (L : AlgebraicallyClosedCoefficients.Index c.l c.Qbar)
        (hA : A.stage ≤ L) (hB : B.stage ≤ L) :
        GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB 0 = 0 := by
      apply (GeneralAlgebraicallyClosedCoefficients.homCoordinates A B).injective
      have hcoord :=
        (GeneralAlgebraicallyClosedCoefficients.homCoordinates_existsUnique A B).exists.choose_spec
          L hA hB 0
      change (GeneralAlgebraicallyClosedCoefficients.homCoordinates A B)
        (GeneralAlgebraicallyClosedCoefficients.ofHom A B L hA hB 0) = _ at hcoord
      rw [hcoord]
      change GeneralAlgebraicallyClosedCoefficients.colimitOf A B L hA hB 0 =
        (GeneralAlgebraicallyClosedCoefficients.homCoordinates A B)
          ((GeneralAlgebraicallyClosedCoefficients.homCoordinates A B).symm 0)
      simp [GeneralAlgebraicallyClosedCoefficients.colimitOf]
    intro U V h
    let := dlAdicBaseResidueInvertible D c U.val.toScheme
    let := dlAdicBaseResidueInvertible D c V.val.toScheme
    let A := (F.value V).obj
    let B := (G.value V).obj
    obtain ⟨L, hA, hB⟩ := exists_ge_ge A.stage B.stage
    let : (rationalDerivedPullback c.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar L)
        (T.left.homOfLE h)).Additive :=
      (rationalDerivedPullback_existsUnique c.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar L)
        (T.left.homOfLE h)).exists.choose_spec.1
    have he := (commonStageDerivedPullback_existsUnique c.l c.Qbar
      (T.left.homOfLE h)).exists.choose_spec.2 A B L hA hB 0
    rw [hz] at he
    simp only [Functor.map_zero, comp_zero, zero_comp, hz] at he
    have hez {P P' Q Q' : generalAlgebraicallyClosedConstructibleCategory
        c.l c.Qbar U.val.toScheme} (hP : P = P') (hQ : Q = Q') :
        HEq (0 : P ⟶ Q) (0 : P' ⟶ Q') := by
      subst P'
      subst Q'
      rfl
    have hm : (dlAdicOpenPull D c T h).map (0 : A ⟶ B) = 0 :=
      eq_of_heq (he.trans (hez
        ((commonStageDerivedPullback_existsUnique c.l c.Qbar
          (T.left.homOfLE h)).exists.choose_spec.1 A).symm
        ((commonStageDerivedPullback_existsUnique c.l c.Qbar
          (T.left.homOfLE h)).exists.choose_spec.1 B).symm))
    change (F.restriction h).hom ≫ 0 =
      (dlAdicOpenPull D c T h).map (0 : A ⟶ B) ≫ (G.restriction h).hom
    rw [hm, comp_zero, zero_comp]

/-- The chosen zero is the literal componentwise zero family.
Source: BS 6.8.7 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
instance dlAdicLocalHomZero (F G : DlLocallyConstructibleAdicHeart D c T) : Zero (F ⟶ G) :=
  ⟨⟨⟨fun _ ↦ 0⟩, dlAdicLocalCompatible_zero D c T F.obj G.obj⟩⟩

/-- The componentwise zero families are absorbing for composition.
Source: BS 6.8.7 (blueprint: def-dl-a1-locally-constructible-adic-heart).
Proof: both equations are checked on each open, where they are the zero-composition
laws of the constructible heart. The forgetful maps on arrows are injective. -/
theorem dlAdicLocalZeroLaws :
    (∀ {X Y : DlLocallyConstructibleAdicHeart D c T} (f : X ⟶ Y)
      (Z : DlLocallyConstructibleAdicHeart D c T), f ≫ (0 : Y ⟶ Z) = 0) ∧
    (∀ (X : DlLocallyConstructibleAdicHeart D c T)
      {Y Z : DlLocallyConstructibleAdicHeart D c T} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = 0) := by
  constructor
  · intro X Y f Z
    ext U
    change (f.hom.hom U).hom ≫ 0 = 0
    exact comp_zero
  · intro X Y Z f
    ext U
    change 0 ≫ (f.hom.hom U).hom = 0
    exact zero_comp

/-- Zero arrows are literally the componentwise zero arrows.
Source: BS 6.8.7 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
instance dlLocallyConstructibleAdicHeartZero :
    HasZeroMorphisms (DlLocallyConstructibleAdicHeart D c T) where
  zero := dlAdicLocalHomZero D c T
  comp_zero := (dlAdicLocalZeroLaws D c T).1
  zero_comp := (dlAdicLocalZeroLaws D c T).2

/-- Restrict a locally constructible adic sheaf to a separated finite-type basis open.
Source: BS 6.8.6 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
def dlAdicLocalEvaluation (U : DlAdicFiniteOpen D T) :
    DlLocallyConstructibleAdicHeart D c T ⥤ sfCommonStageHeart c.l U.val.toScheme c.Qbar where
  obj F := F.obj.value U
  map f := f.hom.hom U

/-- Evaluation sends the specified zero family to its zero component.
Source: BS 6.8.7 (blueprint: def-dl-a1-locally-constructible-adic-heart).
Proof: evaluation extracts the given component from the literal zero family;
its underlying arrow in the ambient constructible category is zero. -/
theorem dlAdicLocalEvaluation_zero (U : DlAdicFiniteOpen D T)
    (F G : DlLocallyConstructibleAdicHeart D c T) :
    (dlAdicLocalEvaluation D c T U).map (0 : F ⟶ G) = 0 := by
  rfl

/-- Evaluation preserves the explicit componentwise zero arrows.
Source: BS 6.8.7 (blueprint: def-dl-a1-locally-constructible-adic-heart). -/
instance dlAdicLocalEvaluationZero (U : DlAdicFiniteOpen D T) :
    (dlAdicLocalEvaluation D c T U).PreservesZeroMorphisms where
  map_zero := dlAdicLocalEvaluation_zero D c T U

end WeilConjectures
