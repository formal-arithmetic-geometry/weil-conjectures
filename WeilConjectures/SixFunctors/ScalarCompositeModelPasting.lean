/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.FiniteConstantRingedLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.SixFunctors.ScalarProperOpenInterchangeSquare
import WeilConjectures.AlgebraicGeometry.OpenExtensionConstructibleFiniteTor
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coefficient pasting on a fixed composite compactification

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Composition paragraph.
(blueprint: lem-route-scalar-composite-model-pasting).

The interchange families are specified by the published identity-on-restriction
normalization. Uniqueness in properOpenInterchange makes this a specification of the
canonical arrows. The compositor includes the actual proper and open compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The fixed compactification model Rp_* j_! on ordinary unbounded module categories.
Source: blueprint compact-support Composition paragraph
(blueprint: lem-route-scalar-composite-model-pasting). -/
def sfbScalarCompactModel (Λ : ScalarSixRing.{u}) {X B Y : Scheme.{u}}
    (j : X ⟶ B) [IsOpenImmersion j] (p : B ⟶ Y) :=
  (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙ RootCoordinateFace.lower Λ.X p

/-- The specified model comparison C = Rp_* delta after gamma, without flatness.
Source: blueprint compact-support comparison and Composition paragraph
(blueprint: lem-route-scalar-composite-model-pasting). -/
def sfbScalarCompactComparison {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X B Y : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] (p : B ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Y).obj ((sfbScalarCompactModel Λ j p).obj K) ⟶
      (sfbScalarCompactModel Λ' j p).obj ((scalarSixChange a X).obj K) :=
  (scalarDirectImageMate a p).app
      ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) ≫
    (RootCoordinateFace.lower Λ'.X p).map
      ((derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app K)

/-- The canonical composition of exact open extensions, conjugate to pullback composition.
Source: blueprint compact-support Composition paragraph, open composition identification
(blueprint: lem-route-scalar-composite-model-pasting). -/
def sfbScalarOpenComp (Λ : ScalarSixRing.{u}) {X B W : Scheme.{u}}
    (j : X ⟶ B) (l : B ⟶ W) [IsOpenImmersion j] [IsOpenImmersion l] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ.X l).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ.X (j ≫ l)).mapDerivedCategory :=
  Adjunction.leftAdjointCompIso
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X l)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (j ≫ l))
    (RootCoordinateFace.upperComp Λ.X j l).symm

/-- Rq_* of the normalized interchange, followed by proper and open composition.
Source: blueprint compact-support Composition paragraph, the fixed-model alpha
(blueprint: lem-route-scalar-composite-model-pasting). -/
def sfbScalarModelCompositor (Λ : ScalarSixRing.{u})
    {X B Y C S : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (p : B ⟶ Y) (i : Y ⟶ C) [IsOpenImmersion i] (q : C ⟶ S)
    (c : Compactification.BoundaryCompactification (p ≫ i))
    (ι : RootCoordinateFace.lower Λ.X p ⋙
        (openImmersionLowerShriek Λ.X i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (sfbScalarCompactModel Λ i q).obj ((sfbScalarCompactModel Λ j p).obj K) ⟶
      (sfbScalarCompactModel Λ (j ≫ c.obj.obj.i) (c.obj.obj.g ≫ q)).obj K :=
  (RootCoordinateFace.lower Λ.X q).map
      (ι.app ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K)) ≫
    (RootCoordinateFace.lowerComp Λ.X c.obj.obj.g q).inv.app
      ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K)) ≫
    (RootCoordinateFace.lower Λ.X (c.obj.obj.g ≫ q)).map
      ((sfbScalarOpenComp Λ j c.obj.obj.i).hom.app K)

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate derivedOpenImmersionShriekIso

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem leftAssociateEquality
    {C : Type*} [Category C] {W X Y Z : C}
    {f : W ⟶ Z} {g : W ⟶ X} {h : X ⟶ Y} {i : Y ⟶ Z}
    (he : f = g ≫ h ≫ i) : f = (g ≫ h) ≫ i := by
  simpa only [Category.assoc] using he

private theorem interchangeNaturality
    {B Y Z C : Type*} [Category B] [Category Y] [Category Z] [Category C]
    {P : B ⥤ Y} {I : Y ⥤ C} {L : B ⥤ Z} {R : Z ⥤ C}
    (ι : P ⋙ I ⟶ L ⋙ R) {B₀ B₁ : B} (d : B₀ ⟶ B₁)
    {U V : C} {A : Z} {Y₀ : Y}
    (t : U ⟶ V) (g : V ⟶ R.obj A) (e : A ⟶ L.obj B₀)
    (b : U ⟶ I.obj Y₀) (p : Y₀ ⟶ P.obj B₀)
    (he : t ≫ g ≫ R.map e = b ≫ I.map p ≫ ι.app B₀) :
    t ≫ g ≫ R.map (e ≫ L.map d) =
      (b ≫ I.map (p ≫ P.map d)) ≫ ι.app B₁ := by
  have hn := ι.naturality d
  simp only [Functor.comp_map] at hn
  calc
    _ = (t ≫ g ≫ R.map e) ≫ R.map (L.map d) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (b ≫ I.map p ≫ ι.app B₀) ≫ R.map (L.map d) := by rw [he]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← hn]

private theorem modelPasting
    {B C D B' C' D' : Type*}
    [Category B] [Category C] [Category D]
    [Category B'] [Category C'] [Category D']
    {F : B ⥤ C} {G : C ⥤ D} {H : B ⥤ D}
    {F' : B' ⥤ C'} {G' : C' ⥤ D'} {H' : B' ⥤ D'}
    {T : B ⥤ B'} {V : C ⥤ C'} {W : D ⥤ D'}
    (γF : F ⋙ V ⟶ T ⋙ F') (γG : G ⋙ W ⟶ V ⋙ G')
    (γH : H ⋙ W ⟶ T ⋙ H') (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    {A : C} {A' A'' : C'} {B₀ B₁ : B} {B₀' B₁' : B'}
    (t : A ⟶ F.obj B₀) (o : B₀ ⟶ B₁) (d : T.obj B₁ ⟶ B₁')
    (b₀ : V.obj A ⟶ A'') (b₁ : A'' ⟶ A') (t' : A' ⟶ F'.obj B₀') (o' : B₀' ⟶ B₁')
    (l : T.obj B₀ ⟶ B₀')
    (hc : γH.app B₀ ≫ c'.hom.app (T.obj B₀) =
      W.map (c.hom.app B₀) ≫ γG.app (F.obj B₀) ≫ G'.map (γF.app B₀))
    (ho : T.map o ≫ d = l ≫ o')
    (hi : V.map t ≫ γF.app B₀ ≫ F'.map l = (b₀ ≫ b₁) ≫ t') :
    W.map (G.map t ≫ c.inv.app B₀ ≫ H.map o) ≫ γH.app B₁ ≫ H'.map d =
      (γG.app A ≫ G'.map b₀) ≫ G'.map b₁ ≫
        (G'.map t' ≫ c'.inv.app B₀' ≫ H'.map o') := by
  have hci : W.map (c.inv.app B₀) ≫ γH.app B₀ =
      γG.app (F.obj B₀) ≫ G'.map (γF.app B₀) ≫ c'.inv.app (T.obj B₀) := by
    apply (cancel_mono (c'.hom.app (T.obj B₀))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hc]
    simp only [← W.map_comp_assoc, Iso.inv_hom_id_app, W.map_id, Category.id_comp]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
  have hnH := γH.naturality o
  have hnG := γG.naturality t
  have hnC := c'.inv.naturality l
  simp only [Functor.comp_map] at hnH hnG hnC
  calc
    _ = W.map (G.map t) ≫ (W.map (c.inv.app B₀) ≫ γH.app B₀) ≫
        H'.map (T.map o ≫ d) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (W.map (H.map o)), hnH]
      simp only [Category.assoc]
    _ = γG.app A ≫ G'.map (V.map t ≫ γF.app B₀ ≫ F'.map l) ≫
        c'.inv.app B₀' ≫ H'.map o' := by
      rw [hci, ho]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (W.map (G.map t)), hnG]
      simp only [Category.assoc]
      rw [← Category.assoc (c'.inv.app (T.obj B₀)), ← hnC]
      simp only [Category.assoc]
    _ = _ := by rw [hi]; simp only [Functor.map_comp, Category.assoc]


/-- The coefficient comparison commutes with the compositor on these fixed models.
The two normalized natural transformations denote the unique identity-on-Y interchange
arrows of det-sf-comp-composition-interchange, over the two coefficient rings.

Source: blueprint latest, compact-support proof, Composition paragraph
(blueprint: lem-route-scalar-composite-model-pasting).

Proof:
1. Write K's cohomology and Tor intervals from its Dctf membership (sk-def-sfb-constructible)
and apply lem-sfb-open-extension-zero-constructible-finite-tor: A = j_!K lies in Dctf on B.
No proper-image or scalar-CTF stability is needed: the claim is an ambient morphism equality.
2. View the boundary Z of c over Spec k and its open immersion l = c.i as an over morphism;
B is Noetherian (locally of finite type and quasi-compact over k), so l is quasi-compact.
lem-sfb-scalar-open-compositor-coherence at K gives the open-compositor coefficient square.
3. lem-sfb-scalar-proper-open-interchange-square at A gives the interchange square; appending
the boundary open extension of delta_j and naturality of the primed interchange at delta_j
give the inner square.
4. The composition clause of lem-sfb-scalar-direct-image-mate-coherence for c.g then q (with
the primed proper compositor cancelled), naturality of the composite mate, of the q mate and
of the inverse primed compositor paste the open and inner squares (helper modelPasting).
5. Unfolding sfbScalarModelCompositor, sfbScalarCompactComparison and sfbScalarCompactModel,
the two sides are the two paths of the pasted square up to associativity. -/
theorem scalarCompositeModelPasting
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X B Y C S : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (j : X ⟶ B) (p : B ⟶ Y) (i : Y ⟶ C) (q : C ⟶ S)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper p.left]
    [IsOpenImmersion i.left] [QuasiCompact i.left] [IsProper q.left]
    (c : Compactification.BoundaryCompactification (p.left ≫ i.left))
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (ι : RootCoordinateFace.lower Λ.X p.left ⋙
        (openImmersionLowerShriek Λ.X i.left).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X c.obj.obj.g)
    (_hι : ∀ A, compositionInterchangeIsNormalized Λ.X p.left i.left c A (ι.app A))
    (ι' : RootCoordinateFace.lower Λ'.X p.left ⋙
        (openImmersionLowerShriek Λ'.X i.left).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ'.X c.obj.obj.g)
    (_hι' : ∀ A, compositionInterchangeIsNormalized Λ'.X p.left i.left c A (ι'.app A))
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (scalarSixChange a S.left).map
        (sfbScalarModelCompositor Λ j.left p.left i.left q.left c ι K.obj) ≫
      sfbScalarCompactComparison a (j.left ≫ c.obj.obj.i) (c.obj.obj.g ≫ q.left) K.obj =
    sfbScalarCompactComparison a i.left q.left
        ((sfbScalarCompactModel Λ j.left p.left).obj K.obj) ≫
      (sfbScalarCompactModel Λ' i.left q.left).map
        (sfbScalarCompactComparison a j.left p.left K.obj) ≫
      sfbScalarModelCompositor Λ' j.left p.left i.left q.left c ι'
        ((scalarSixChange a X.left).obj K.obj) := by
  classical
  have haMon : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have hcomm : IsCommMonObj Λ.X := Λ.comm
  have hcomm' : IsCommMonObj Λ'.X := Λ'.comm
  obtain ⟨m, n, hcoh⟩ :=
    (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K.obj).mpr K.property.1.1
  obtain ⟨v, w, htor⟩ := K.property.2
  let A : ConstantModelConstructibleFiniteTor Λ.X B.left :=
    ⟨_, (openExtension_constructible_finiteTor ell k Λ.X j K m n v w hcoh htor).1⟩
  let Z : Over (Spec (.of k)) := Over.mk (c.obj.obj.Z ↘ Spec (.of k))
  have : LocallyOfFiniteType Z.hom := inferInstanceAs
    (LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k)))
  have : QuasiCompact Z.hom := inferInstanceAs
    (QuasiCompact (c.obj.obj.Z ↘ Spec (.of k)))
  have : IsSeparated Z.hom := inferInstanceAs
    (IsSeparated (c.obj.obj.Z ↘ Spec (.of k)))
  let l : B ⟶ Z := Over.homMk c.obj.obj.i (by
    exact CategoryTheory.comp_over c.obj.obj.i (Spec (.of k)))
  have : IsOpenImmersion l.left := inferInstanceAs (IsOpenImmersion c.obj.obj.i)
  have : IsLocallyNoetherian B.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : IsNoetherian B.left := ⟨⟩
  have : QuasiCompact l.left := inferInstanceAs (QuasiCompact c.obj.obj.i)
  let d : (scalarSixChange a B.left).obj
      ((openImmersionLowerShriek Λ.X j.left).mapDerivedCategory.obj K.obj) ⟶
      (openImmersionLowerShriek Λ'.X j.left).mapDerivedCategory.obj
        ((scalarSixChange a X.left).obj K.obj) :=
    (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom _ _ j.left _).hom.app K.obj
  let e : (scalarSixChange a Z.left).obj
      ((openImmersionLowerShriek Λ.X l.left).mapDerivedCategory.obj A.obj) ⟶
      (openImmersionLowerShriek Λ'.X l.left).mapDerivedCategory.obj
        ((scalarSixChange a B.left).obj A.obj) :=
    (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom _ _ l.left _).hom.app A.obj
  have hopen := scalarOpenCompositorCoherence ell k a _ha j l K.obj
  change (scalarSixChange a Z.left).map
      ((sfbScalarOpenComp Λ j.left l.left).hom.app K.obj) ≫
      (@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom _ _ (j.left ≫ l.left) _).hom.app K.obj =
    e ≫ (openImmersionLowerShriek Λ'.X l.left).mapDerivedCategory.map d ≫
      (sfbScalarOpenComp Λ' j.left l.left).hom.app
        ((scalarSixChange a X.left).obj K.obj) at hopen
  have hinter := scalarProperOpenInterchangeSquare ell k a _ha p i c ι _hι ι' _hι' A
  have hinner := interchangeNaturality ι' d
    ((scalarSixChange a C.left).map (ι.app A.obj))
    ((scalarDirectImageMate a c.obj.obj.g).app
      ((openImmersionLowerShriek Λ.X c.obj.obj.i).mapDerivedCategory.obj A.obj)) e
    ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom _ _ i.left _).hom.app
        ((RootCoordinateFace.lower Λ.X p.left).obj A.obj))
    ((scalarDirectImageMate a p.left).app A.obj) hinter
  have hp := modelPasting
    (scalarDirectImageMate a c.obj.obj.g) (scalarDirectImageMate a q.left)
    (scalarDirectImageMate a (c.obj.obj.g ≫ q.left))
    (RootCoordinateFace.lowerComp Λ.X c.obj.obj.g q.left)
    (RootCoordinateFace.lowerComp Λ'.X c.obj.obj.g q.left)
    (ι.app A.obj) ((sfbScalarOpenComp Λ j.left c.obj.obj.i).hom.app K.obj)
    ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
          a.hom.hom a.hom.isMonHom_hom _ _
          (j.left ≫ c.obj.obj.i) _).hom.app K.obj)
    ((@derivedOpenImmersionShriekIso _ _ Λ.mon Λ.comm Λ'.mon Λ'.comm
          a.hom.hom a.hom.isMonHom_hom _ _
          i.left _).hom.app ((RootCoordinateFace.lower Λ.X p.left).obj A.obj))
    ((openImmersionLowerShriek Λ'.X i.left).mapDerivedCategory.map
        ((scalarDirectImageMate a p.left).app A.obj ≫
          (RootCoordinateFace.lower Λ'.X p.left).map d))
    (ι'.app ((openImmersionLowerShriek Λ'.X j.left).mapDerivedCategory.obj
      ((scalarSixChange a X.left).obj K.obj)))
    ((sfbScalarOpenComp Λ' j.left c.obj.obj.i).hom.app
      ((scalarSixChange a X.left).obj K.obj))
    (e ≫ (openImmersionLowerShriek Λ'.X c.obj.obj.i).mapDerivedCategory.map d)
    ((scalarDirectImageMateCoherence a c.obj.obj.g q.left).2.1 _)
    (leftAssociateEquality hopen) hinner
  dsimp only [A, d, scalarSixChange, scalarSixAdjunctionLeft,
    sfbScalarModelCompositor, sfbScalarCompactComparison, sfbScalarCompactModel,
    Functor.comp_map, Functor.comp_obj] at hp ⊢
  convert hp using 1 <;> rfl

end AlgebraicGeometry.ProEtale.CondensedRing
