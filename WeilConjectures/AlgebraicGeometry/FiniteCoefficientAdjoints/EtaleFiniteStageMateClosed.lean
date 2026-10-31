/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateProperty
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportTriangle
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalConstantTensor
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportTriangle

/-! # Closed-immersion case of the finite-stage mate

Source: ordinary etale reduction-exceptional argument and the parent mate proof.
(blueprint: lem-pur-etale-finite-stage-mate-closed).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

/-- Lift the first comparison of support triangles through a fully faithful left adjoint.
The first triangle square is exactly the defining equation of the counit transpose. -/
private theorem isIso_closed_mate_of_triangles
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
    [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
    (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D') (G' : D' ⥤ C')
    [F'.Full] [F'.Faithful]
    (adj : F ⊣ G) (adj' : F' ⊣ G') (Q : C ⥤ C') (T : D ⥤ D')
    [T.CommShift ℤ] [T.IsTriangulated]
    (q : F ⋙ T ≅ Q ⋙ F') (K : D)
    {Z : D} {Z' : D'} (v : K ⟶ Z)
    (w : Z ⟶ (F.obj (G.obj K))⟦(1 : ℤ)⟧)
    (v' : T.obj K ⟶ Z') (w' : Z' ⟶ (F'.obj (G'.obj (T.obj K)))⟦(1 : ℤ)⟧)
    (hΔ : Pretriangulated.Triangle.mk (adj.counit.app K) v w ∈ distTriang D)
    (hΔ' : Pretriangulated.Triangle.mk (adj'.counit.app (T.obj K)) v' w' ∈ distTriang D')
    (e : T.obj Z ≅ Z') (hs : T.map v ≫ e.hom = v') :
    IsIso (adj'.homEquiv _ _ (q.inv.app (G.obj K) ≫ T.map (adj.counit.app K))) := by
  let Δ := Pretriangulated.Triangle.mk (adj.counit.app K) v w
  let Δ' := Pretriangulated.Triangle.mk (adj'.counit.app (T.obj K)) v' w'
  have hs' : (T.mapTriangle.obj Δ).mor₂ ≫ e.hom = 𝟙 _ ≫ Δ'.mor₂ := by
    dsimp [Δ, Δ', Functor.mapTriangle, Pretriangulated.Triangle.mk]
    simpa only [Category.id_comp] using hs
  obtain ⟨f, hf₁, hf₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    (T.mapTriangle.obj Δ) Δ' (T.map_distinguished _ hΔ) hΔ' (𝟙 _) e.hom hs'
  let φ : T.mapTriangle.obj Δ ⟶ Δ' :=
    { hom₁ := f, hom₂ := 𝟙 _, hom₃ := e.hom
      comm₁ := hf₁, comm₂ := hs', comm₃ := hf₃ }
  have : IsIso f := Pretriangulated.isIso₁_of_isIso₂₃ φ
    (T.map_distinguished _ hΔ) hΔ' (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  let b := F'.preimage (q.inv.app (G.obj K) ≫ f)
  have hb : F'.map b = q.inv.app (G.obj K) ≫ f := F'.map_preimage _
  have : IsIso (F'.map b) := by rw [hb]; infer_instance
  have : IsIso b := isIso_of_reflects_iso b F'
  have he : b = adj'.homEquiv _ _
      (q.inv.app (G.obj K) ≫ T.map (adj.counit.app K)) := by
    apply (adj'.homEquiv (Q.obj (G.obj K)) (T.obj K)).symm_apply_eq.mp
    rw [Adjunction.homEquiv_counit, hb, Category.assoc]
    have hf := hf₁
    change T.map (adj.counit.app K) ≫ 𝟙 _ =
      f ≫ adj'.counit.app (T.obj K) at hf
    rw [Category.comp_id] at hf
    rw [← hf]
  exact he ▸ this

/-- The mate unit square, transported from left-derived to exact geometric pullback. -/
private theorem scalar_unit_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L LD : C ⥤ D} {R : D ⥤ C} {L' LD' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adjD : LD ⊣ R) (adj' : L' ⊣ R') (adjD' : LD' ⊣ R')
    (e : L ≅ LD) (e' : L' ≅ LD')
    (hu : ∀ K, adjD.unit.app K = adj.unit.app K ≫ R.map (e.hom.app K))
    (hu' : ∀ K, adjD'.unit.app K = adj'.unit.app K ≫ R'.map (e'.hom.app K))
    (T : C ⥤ C') (Q : D ⥤ D') (α : T ⋙ L' ≅ L ⋙ Q) (K : C)
    [IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom)).app (L.obj K))] :
    ∃ e₃ : T.obj (R.obj (LD.obj K)) ≅ R'.obj (LD'.obj (T.obj K)),
      T.map (adjD.unit.app K) ≫ e₃.hom = adjD'.unit.app (T.obj K) := by
  let β := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom)).natTrans
  let e₃ := T.mapIso (R.mapIso (e.app K).symm) ≪≫
    asIso (β.app (L.obj K)) ≪≫ R'.mapIso (α.app K).symm ≪≫
    R'.mapIso (e'.app (T.obj K))
  have hcancel : T.map (adjD.unit.app K) ≫ T.map (R.map (e.inv.app K)) =
      T.map (adj.unit.app K) := by
    rw [← T.map_comp, hu K, Category.assoc, ← R.map_comp,
      e.hom_inv_id_app, R.map_id]
    erw [Category.comp_id]
  have hm : T.map (adj.unit.app K) ≫ β.app (L.obj K) =
      adj'.unit.app (T.obj K) ≫ R'.map (α.hom.app K) :=
    unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ α.hom) K
  refine ⟨e₃, ?_⟩
  dsimp only [e₃, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, asIso_hom]
  simp only [← Category.assoc]
  rw [hcancel, hm]
  simp only [Category.assoc, ← R'.map_comp]
  rw [← Category.assoc, α.hom_inv_id_app]
  erw [Category.id_comp]
  exact (hu' (T.obj K)).symm

/-- Normalize compact support at an arbitrary compactification of a closed immersion. -/
private def closedSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsClosedImmersion f]
    (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor :=
  Etale.rightDerivedLowerShriekOfCompactificationIso A c (Compactification.ofIsProper f) ≪≫
    Functor.isoWhiskerRight
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X)
      (Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor ≪≫
    Functor.leftUnitor _

/-- Finite relative cohomological dimension and the constant projection formula
make the open scalar mate invertible on a finite-Tor input. -/
private theorem open_scalarMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {k : Type u} [Field k]
    {U Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsNoetherian Y]
    (j : U ⟶ Y) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule A U) (a b : ℤ)
    (hTor : Etale.DerivedCategory.hasTorAmplitudeIn A U a b K) :
    IsIso ((Etale.scalarMate φ j).app K) := by
  have : QuasiCompact j := inferInstance
  have hcd := Etale.hasFiniteCohomologicalDimensionMorphism A
    (isAddTorsion_of_finite : IsAddTorsion A) (j ≫ aY) aY j rfl
  have := Etale.preservesCoproducts_rightDerivedLowerStar A j hcd (ULift.{u + 1} ℕ)
  have : PreservesColimitsOfShape (Discrete ℕ)
      (Etale.lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  let M := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)
  have : Finite M := inferInstanceAs (Finite B)
  have hp := Etale.isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts
    A j K M
  let e : Etale.scalarCoefficient φ Y ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) :=
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      (Etale.scalarCoefficientSheafIsoConstant φ Y)
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) j).app K).app (Etale.scalarCoefficient φ Y)) :=
    (NatTrans.isIso_app_iff_of_iso
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K) e).2 hp
  have : K.IsGE a := (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hTor)).1
  have : ((Etale.scalarExtension φ U).obj K).IsGE a :=
    Etale.scalarExtension_lowerBound φ U K a b hTor
  exact Etale.scalarMate_isIso_of_projection φ j K a a

/-- Closed-immersion case of ordinary etale finite-stage exceptional coefficient change.
Source: parent mate-invertibility argument, closed-support steps 2--3
(blueprint: lem-pur-etale-finite-stage-mate-closed).

Proof: take the quasi-compact open complement of the closed immersion. Represent L
by a degreewise-injective K-injective complex and resolve the target coefficient
module by an A-flat K-flat complex. Tensor the support exact sequence after scalar
restriction. The middle comparison is identity. The open comparison is the
finite-constant projection isomorphism; relative finite torsion cohomological
dimension supplies its uniform direct-image bound over k. Two out of three for
the resulting distinguished triangles gives the supported comparison. Hom from
a closed-supported object to the open direct image vanishes in every shift.
The exact Hom sequence therefore identifies this comparison with the specified
counit transpose. Closed direct image and scalar restriction reflect isomorphisms.
Proper coefficient change and open balancing identify comparisonInverse with the
inverse compact-support map. This also handles the empty closed subscheme and
identity coefficient arrows, without a flatness hypothesis. -/
theorem etale_finite_stage_mate_closed
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsClosedImmersion f]
    {s t : Stage l E} (a : Arrow s t)
 :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    EtaleFiniteStageMateProperty a f := by
  have _hp := hp
  have _hlp := hlp
  classical
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  intro c L hL
  let U : Y.Opens :=
    ⟨(Set.range f.base)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range f.base = (Set.range U.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} s.ring) c
  let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} t.ring) c
  let RiA := (Etale.lowerStar (ModuleCat.{u + 1} s.ring) f).rightDerivedFunctor
  let RiB := (Etale.lowerStar (ModuleCat.{u + 1} t.ring) f).rightDerivedFunctor
  let adjA := etaleAdjunction s.ring c
  let adjB := etaleAdjunction t.ring c
  let adjjA := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} s.ring) U.ι
  let adjjB := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} t.ring) U.ι
  let adjDA := Etale.mapDerivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} s.ring) U.ι
  let adjDB := Etale.mapDerivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} t.ring) U.ι
  let eA := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} s.ring) U.ι
  let eB := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} t.ring) U.ι
  let T := Etale.scalarExtension a.ringMap Y
  let Q := Etale.scalarExtension a.ringMap X
  let q := Etale.ExceptionalCoefficients.compactSupportIso a.ringMap c
  have : FB.Full := Functor.Full.of_iso (closedSupportIso t.ring c).symm
  have : FB.Faithful := Functor.Faithful.of_iso (closedSupportIso t.ring c).symm
  obtain ⟨δA, hδA⟩ := Etale.exists_etale_closedSupportTriangle s.ring f U.ι hij
  obtain ⟨δB, hδB⟩ := Etale.exists_etale_closedSupportTriangle t.ring f U.ι hij
  obtain ⟨wA, hwA⟩ := Pretriangulated.exists_distTriang_of_counit_iso
    (Adjunction.ofIsLeftAdjoint RiA) adjA (closedSupportIso s.ring c).symm (hδA L)
  obtain ⟨wB, hwB⟩ := Pretriangulated.exists_distTriang_of_counit_iso
    (Adjunction.ofIsLeftAdjoint RiB) adjB (closedSupportIso t.ring c).symm (hδB (T.obj L))
  obtain ⟨b, d, hTor⟩ := hL.2
  have hTorU := Etale.torAmplitudeIn_leftDerivedUpperStar
    (ModuleCat.{u + 1} s.ring) U.ι b d hTor
  have hopen : IsIso ((Etale.scalarMate a.ringMap U.ι).app
      ((Etale.upperStar (ModuleCat.{u + 1} s.ring) U.ι).leftDerivedFunctor.obj L)) :=
    open_scalarMate_isIso a.ringMap (Y ↘ Spec (.of k)) U.ι _ b d
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hTorU)
  have : IsIso ((mateEquiv adjjA adjjB
      (TwoSquare.mk _ _ _ _ (Etale.scalarPullbackIso a.ringMap U.ι).hom)).app
        ((Etale.upperStar (ModuleCat.{u + 1} s.ring) U.ι).leftDerivedFunctor.obj L)) := by
    change IsIso ((Etale.scalarMate a.ringMap U.ι).app _)
    exact hopen
  obtain ⟨e₃, hsquare⟩ := scalar_unit_square adjjA adjDA adjjB adjDB eA eB
    (fun V ↦ congrArg (fun adj ↦ adj.unit.app V)
      (Etale.mapDerivedUpperStarLowerStarAdjunction_eq (ModuleCat.{u + 1} s.ring) U.ι))
    (fun V ↦ congrArg (fun adj ↦ adj.unit.app V)
      (Etale.mapDerivedUpperStarLowerStarAdjunction_eq (ModuleCat.{u + 1} t.ring) U.ι))
    T (Etale.scalarExtension a.ringMap U)
    (Etale.scalarPullbackIso a.ringMap U.ι) L
  let adjT : T ⊣ Sheaf.derivedRestrictScalars Y.smallEtaleTopology a.ringMap :=
    Adjunction.ofIsRightAdjoint _
  let : T.CommShift ℤ := adjT.leftAdjointCommShift ℤ
  have : adjT.CommShift ℤ := adjT.commShift_of_rightAdjoint ℤ
  have : T.IsTriangulated := adjT.isTriangulated_leftAdjoint
  rw [Etale.ExceptionalCoefficients.comparisonInverse_eq]
  exact isIso_closed_mate_of_triangles FA (etaleUpper s.ring c) FB (etaleUpper t.ring c)
    adjA adjB Q T q L (adjDA.unit.app L) wA (adjDB.unit.app (T.obj L)) wB
    hwA hwB e₃ hsquare

end AlgebraicGeometry.FiniteCoefficientAdjoints
