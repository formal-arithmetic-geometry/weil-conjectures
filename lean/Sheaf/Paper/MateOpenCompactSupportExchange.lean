/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.MateOpenRestrictionMaps
import Sheaf.Paper.OpenImmersionLocalizing
import Sheaf.Paper.MateOpenProperSupport
import Sheaf.Paper.MateOpenProperRestrictionIso
import all Sheaf.Paper.CompactificationRefinementLocalizing

/-! # The normalized compact-support comparison for an open square

Source: blueprint det-sf-mate-open-restriction, proof (2), and
 det-sf-comp-composition-interchange, proof (2)--(3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem mate_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {H : A ⥤ C} {H' : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : TwoSquare H L L' H') (M : B) :
    (mateEquiv a b θ).natTrans.app M =
      b.homEquiv _ _ (θ.natTrans.app (R.obj M) ≫ H'.map (a.counit.app M)) := by
  simp [mateEquiv, Adjunction.homEquiv_unit]

private def transposeRestriction
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
    {Q : C ⥤ A} {F : C ⥤ B} (δ : F ⋙ R ≅ Q) : Q ⋙ L ⟶ F where
  app M := (a.homEquiv _ _).symm (δ.inv.app M)
  naturality X Y f := by
    apply (a.homEquiv _ _).injective
    simp only [Functor.comp_map, a.homEquiv_naturality_left,
      a.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact δ.inv.naturality f

private def properRestrictionNatTrans
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z Z' Y V : Scheme.{u}} {a : Z' ⟶ Z} {q : Z' ⟶ V}
    {r : Z ⟶ Y} {v : V ⟶ Y} (sq : CommSq a q r v) :
    (lowerStar Λ r).rightDerivedFunctor ⋙ (upperStar Λ v).mapDerivedCategory ⟶
      (upperStar Λ a).mapDerivedCategory ⋙ (lowerStar Λ q).rightDerivedFunctor :=
  (mateEquiv
    ((derivedUpperStarLowerStarAdjunction Λ r).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ r))
    ((derivedUpperStarLowerStarAdjunction Λ q).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ q))
    (TwoSquare.mk _ _ _ _
      (((Functor.mapDerivedCategoryCompIso (upperStar Λ v) (upperStar Λ q)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((upperStarComp Λ q v).symm ≪≫
            eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ a r) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ r) (upperStar Λ a)).hom))).natTrans

private theorem properRestrictionNatTrans_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z Z' Y V : Scheme.{u}} {a : Z' ⟶ Z} {q : Z' ⟶ V}
    {r : Z ⟶ Y} {v : V ⟶ Y} (sq : CommSq a q r v) (B) :
    (properRestrictionNatTrans Λ sq).app B = mateOpenProperRestriction Λ sq B := by
  exact mate_component _ _ _ B

private def targetRestrictionNatTrans
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X V Y : Scheme.{u}} {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f) :
    (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c ⋙
        (upperStar Λ v).mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq) :=
  Functor.whiskerRight (mateOpenSquareExtension Λ sq c).hom
      ((lowerStar Λ c.g).rightDerivedFunctor ⋙ (upperStar Λ v).mapDerivedCategory) ≫
    Functor.whiskerLeft
      ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory)
      (properRestrictionNatTrans Λ (IsPullback.of_hasPullback c.g v).toCommSq) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory
        (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
          (pullback.fst c.g v)).unit).inv)
      (lowerStar Λ (pullback.snd c.g v)).rightDerivedFunctor

private theorem targetRestrictionNatTrans_app
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X V Y : Scheme.{u}} {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f) (M) :
    (targetRestrictionNatTrans Λ sq c).app M = mateOpenTargetLowerShriek Λ sq c M := by
  simp only [targetRestrictionNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, properRestrictionNatTrans_app, mateOpenTargetLowerShriek,
    Functor.comp_map, Functor.comp_obj, asIso_inv, NatIso.isIso_inv_app]

private theorem supported_open_counit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {V Y : Scheme.{u}} (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (B : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hz : IsZero ((upperStar Λ v.closedComplement).mapDerivedCategory.obj B)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).counit.app B) := by
  let c := v.closedComplement
  have hc : IsCompl (Set.range c.base) (Set.range v.base) := by
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v
  have hopen : IsIso ((upperStar Λ v).mapDerivedCategory.map (adj.counit.app B)) :=
    isIso_of_hom_comp_eq_id _ (adj.right_triangle_components B)
  apply (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl
    Λ c v hc).isIso_of_pairFunctor (adj.counit.app B)
  · exact (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ v) _).2 hopen
  · have hs := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ v c hc.symm.disjoint ((upperStar Λ v).mapDerivedCategory.obj B)
    have ht := hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ c).app B)
    exact hs.isIso ht _

/-- The left-functor comparison in a Cartesian open square, before choosing exceptional
right adjoints. Its open transpose is the inverse of the specified restriction mate.
Source: blueprint det-sf-mate-open-restriction, proof (2), and
 det-sf-comp-composition-interchange, proof (2)--(3).
(blueprint: lem-sfb-mate-open-compact-support-exchange).

Proof: The specified restriction map is a natural transformation: it is the composite
of the open-extension compositor, the canonical proper/open mate and the inverse open
unit. The proper/open mate is invertible by the normalized derived open-square
adjunction calculation, so this transformation is invertible. Transpose its inverse
under open extension/restriction to obtain the comparison. Proper image of extension
by zero has zero closed restriction on the whole localizing hull, by
mateOpenProperSupport. The open counit on this image is therefore invertible: its open
restriction is invertible by the triangle identity, and its closed restriction is a
map between zero objects. Thus the transposed comparison is invertible. Its adjunction
equation, followed by the original restriction transformation, is exactly the displayed
normalization. The argument includes identity and empty opens and unbounded inputs. -/
theorem mateOpenCompactSupportExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f)
    {U V : Scheme.{u}} (a : U ⟶ X) (q : U ⟶ V) (v : V ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion v] (sq : IsPullback a q f v) :
    ∃ β : ((localizingClosureProEtale Λ U).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq) ⋙
          (openImmersionLowerShriek Λ v).mapDerivedCategory) ≅
        ((localizingClosureProEtale Λ U).ι ⋙
          (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
          rightDerivedLowerShriekOfCompactification Λ c),
      ∀ M : (localizingClosureProEtale Λ U).FullSubcategory,
        mateOpenTargetLowerShriek Λ sq c M.obj ≫
            (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v).unit.app
              ((rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq)).obj M.obj) ≫
            (upperStar Λ v).mapDerivedCategory.map (β.hom.app M) = 𝟙 _ := by
  have hchar : ringChar k = p := ringChar.eq k p
  have : Fact (ringChar k).Prime := ⟨by
    rw [hchar]
    exact (CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rwa [hchar]⟩
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have : QuasiCompact a := inferInstance
  have : QuasiCompact v := inferInstance
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : QuasiCompact c.i := inferInstance
  let W : Over (Spec (.of k)) := Over.mk (c.g ≫ Y ↘ Spec (.of k))
  let V₀ : Over (Spec (.of k)) := Over.mk (v ≫ Y ↘ Spec (.of k))
  let Y₀ : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType W.hom :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (.of k)))
  have : QuasiCompact W.hom :=
    inferInstanceAs (QuasiCompact (c.g ≫ Y ↘ Spec (.of k)))
  have : IsSeparated W.hom :=
    inferInstanceAs (IsSeparated (c.g ≫ Y ↘ Spec (.of k)))
  have : LocallyOfFiniteType V₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (v ≫ Y ↘ Spec (.of k)))
  have : QuasiCompact V₀.hom :=
    inferInstanceAs (QuasiCompact (v ≫ Y ↘ Spec (.of k)))
  have : IsSeparated V₀.hom :=
    inferInstanceAs (IsSeparated (v ≫ Y ↘ Spec (.of k)))
  have : LocallyOfFiniteType Y₀.hom := inferInstanceAs
    (LocallyOfFiniteType (Y ↘ Spec (.of k)))
  have : QuasiCompact Y₀.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  have : IsSeparated Y₀.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  let r : W ⟶ Y₀ := Over.homMk c.g
  have : IsProper r.left := inferInstanceAs (IsProper c.g)
  let i : V₀ ⟶ Y₀ := Over.homMk v
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion v)
  have : QuasiCompact i.left := inferInstanceAs (QuasiCompact v)
  let d := c.ofIsPullback sq
  let : U.Over (Spec (.of k)) := ⟨a ≫ X ↘ Spec (.of k)⟩
  have : a.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (a ≫ X ↘ Spec (.of k)))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (a ≫ X ↘ Spec (.of k)))
  have : IsSeparated (U ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (a ≫ X ↘ Spec (.of k)))
  have : IsLocallyNoetherian V :=
    LocallyOfFiniteType.isLocallyNoetherian (v ≫ Y ↘ Spec (.of k))
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : QuasiCompact d.i := inferInstance
  have hD : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ d.Z
        ((openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K.obj) := by
    let : d.Z.Over (Spec (.of k)) := ⟨d.g ≫ v ≫ Y ↘ Spec (.of k)⟩
    have : LocallyOfFiniteType (d.Z ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (d.g ≫ v ≫ Y ↘ Spec (.of k)))
    have : QuasiCompact (d.Z ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (d.g ≫ v ≫ Y ↘ Spec (.of k)))
    have : IsSeparated (d.Z ↘ Spec (.of k)) :=
      inferInstanceAs (IsSeparated (d.g ≫ v ≫ Y ↘ Spec (.of k)))
    have : d.i.IsOver (Spec (.of k)) := ⟨by
      change d.i ≫ d.g ≫ v ≫ Y ↘ Spec (.of k) = a ≫ X ↘ Spec (.of k)
      rw [← Category.assoc d.i d.g, ← d.comm, ← Category.assoc q v, ← sq.w]
      rw [Category.assoc, comp_over]⟩
    obtain ⟨_, _, h, _⟩ :=
      (openImmersionLowerShriek_localizing ℓ k p hp hpl Λ hΛ d.i).2.2
    exact h
  let τ := targetRestrictionNatTrans Λ sq c
  have hτ (K) : IsIso (τ.app K) := by
    change IsIso ((targetRestrictionNatTrans Λ sq c).app K)
    rw [targetRestrictionNatTrans_app]
    unfold mateOpenTargetLowerShriek
    have := mateOpenProperRestriction_isIso Λ ℓ k hΛ r i
      ((openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ d.i).mapDerivedCategory.obj K))
    infer_instance
  have hτnat : IsIso τ := NatIso.isIso_of_isIso_app τ
  let L := (localizingClosureProEtale Λ U).ι
  let F := L ⋙ (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
    rightDerivedLowerShriekOfCompactification Λ c
  let Q := L ⋙ rightDerivedLowerShriekOfCompactification Λ d
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ v
  let δ : F ⋙ (upperStar Λ v).mapDerivedCategory ≅ Q :=
    asIso (Functor.whiskerLeft L τ)
  let β : Q ⋙ (openImmersionLowerShriek Λ v).mapDerivedCategory ⟶ F :=
    transposeRestriction adj δ
  have hβ (K) : IsIso (β.app K) := by
    have hz := mateOpenProperSupport Λ ℓ k hΛ r i _ (hD K)
    have hs : IsZero ((upperStar Λ v.closedComplement).mapDerivedCategory.obj
        (F.obj K)) := by
      exact hz.of_iso ((upperStar Λ v.closedComplement).mapDerivedCategory.mapIso
        ((lowerStar Λ c.g).rightDerivedFunctor.mapIso
          ((mateOpenSquareExtension Λ sq c).app K.obj)))
    have hc := supported_open_counit Λ v (F.obj K) hs
    change IsIso ((openImmersionLowerShriek Λ v).mapDerivedCategory.map
      (δ.inv.app K) ≫ adj.counit.app (F.obj K))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, ?_⟩
  intro K
  have he : adj.unit.app (Q.obj K) ≫
      (upperStar Λ v).mapDerivedCategory.map (β.app K) = δ.inv.app K := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  change mateOpenTargetLowerShriek Λ sq c K.obj ≫
    adj.unit.app (Q.obj K) ≫ (upperStar Λ v).mapDerivedCategory.map (β.app K) = 𝟙 _
  rw [he]
  change mateOpenTargetLowerShriek Λ sq c K.obj ≫ δ.inv.app K = 𝟙 _
  rw [← targetRestrictionNatTrans_app]
  exact δ.hom_inv_id_app K


end AlgebraicGeometry.ProEtale.CondensedRing
