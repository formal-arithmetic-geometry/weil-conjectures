/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRestrictionGeometricMate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-! # Scalar extension and the normalized model exchange cube -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a]

private theorem restriction_pullback_inv {X S : Scheme.{u}} (f : X ⟶ S) :
    (scalarRestrictionPullbackIso a f).inv =
      (CondensedRing.derivedComapLeftDerivedUpperStarIso a f).hom := by
  simp only [CondensedRing.derivedComapLeftDerivedUpperStarIso,
    scalarRestrictionPullbackIso, CondensedRing.derivedComapUpperStarIso,
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.mapDerivedCategoryNatIso_symm,
    Category.assoc]

private theorem restriction_pullback_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.SquareCompatible
      (T := (Mod.comap (coefficientMap a Z)).mapDerivedCategory)
      (T' := (Mod.comap (coefficientMap a X)).mapDerivedCategory)
      (scalarRestrictionPullbackIso a (f ≫ g))
      (Functor.pasteSquareIso (scalarRestrictionPullbackIso a g)
        (scalarRestrictionPullbackIso a f))
      (CondensedRing.leftDerivedUpperStarComp T f g).hom
      (CondensedRing.leftDerivedUpperStarComp R f g).hom := by
  intro N
  dsimp only [derivedUpper]
  have h := CondensedRing.derivedComapLeftDerivedUpperStarIso_comp_hom_app a f g N
  rw [← restriction_pullback_inv a g, ← restriction_pullback_inv a f,
    ← restriction_pullback_inv a (f ≫ g)] at h
  apply (cancel_mono ((Functor.pasteSquareIso (scalarRestrictionPullbackIso a g)
    (scalarRestrictionPullbackIso a f)).inv.app N)).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simp only [Functor.pasteSquareIso_inv_app]
  dsimp only [derivedUpper]
  rw [h]
  simp only [Iso.hom_inv_id_app_assoc]
  exact Category.comp_id _

private theorem restriction_pullback_congr
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g) :
    NatTrans.SquareCompatible
      (T := (Mod.comap (coefficientMap a S)).mapDerivedCategory)
      (T' := (Mod.comap (coefficientMap a X)).mapDerivedCategory)
      (scalarRestrictionPullbackIso a f) (scalarRestrictionPullbackIso a g)
      (Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr T h)).hom
      (Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr R h)).hom := by
  subst g
  simp only [CondensedRing.upperStarCongr_self, Functor.leftDerivedFunctorNatIso_refl,
    Iso.refl_hom]
  exact NatTrans.SquareCompatible.id _

private theorem restriction_pullback_square
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    NatTrans.SquareCompatible
      (T := (Mod.comap (coefficientMap a S)).mapDerivedCategory)
      (T' := (Mod.comap (coefficientMap a X')).mapDerivedCategory)
      (Functor.pasteSquareIso (scalarRestrictionPullbackIso a hS)
        (scalarRestrictionPullbackIso a f'))
      (Functor.pasteSquareIso (scalarRestrictionPullbackIso a f)
        (scalarRestrictionPullbackIso a hX))
      (((CondensedRing.leftDerivedUpperStarComp T f' hS).symm ≪≫
        Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr T h) ≪≫
        CondensedRing.leftDerivedUpperStarComp T hX f).hom)
      (((CondensedRing.leftDerivedUpperStarComp R f' hS).symm ≪≫
        Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr R h) ≪≫
        CondensedRing.leftDerivedUpperStarComp R hX f).hom) := by
  exact (restriction_pullback_comp a f' hS).inv.comp
    ((restriction_pullback_congr a h).comp (restriction_pullback_comp a hX f))

private theorem square_inverse
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {U : A ⥤ A'} {V : B ⥤ B'}
    {F G : A ⥤ B} {F' G' : A' ⥤ B'}
    (iF : F ⋙ V ≅ U ⋙ F') (iG : G ⋙ V ≅ U ⋙ G')
    (α : F ⟶ G) (α' : F' ⟶ G')
    (h : NatTrans.SquareCompatible iF iG α α') (M : A) :
    α'.app (U.obj M) ≫ iG.inv.app M = iF.inv.app M ≫ V.map (α.app M) := by
  apply (cancel_epi (iF.hom.app M)).1
  rw [← Category.assoc, ← h M]
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  exact Category.comp_id _

private theorem scalar_mate_cube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {S₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {S₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {S₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {S₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : S₀ ⊣ R₀) (a₁ : S₁ ⊣ R₁) (a₂ : S₂ ⊣ R₂) (a₃ : S₃ ⊣ R₃)
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ M, c.app (R₀.obj M) ≫ I.map (qG.app M) ≫ qI.app (G'.obj M) =
      H.map (qJ.app M) ≫ qH.app (J'.obj M) ≫ R₃.map (d.app M))
    (N : C₀) :
    S₃.map (c.app N) ≫
        ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).app (G.obj N) ≫
        I'.map (((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).app N) =
      ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).app (J.obj N) ≫
        H'.map (((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).app N) ≫
        d.app (S₀.obj N) := by
  let lJ := ((mateEquiv a₀ a₁).symm (TwoSquare.mk _ _ _ _ qJ)).natTrans
  let lH := ((mateEquiv a₁ a₃).symm (TwoSquare.mk _ _ _ _ qH)).natTrans
  let lG := ((mateEquiv a₀ a₂).symm (TwoSquare.mk _ _ _ _ qG)).natTrans
  let lI := ((mateEquiv a₂ a₃).symm (TwoSquare.mk _ _ _ _ qI)).natTrans
  have hj (K : C₀) : J.map (a₀.unit.app K) ≫ qJ.app (S₀.obj K) =
      a₁.unit.app (J.obj K) ≫ R₁.map (lJ.app K) :=
    unit_mateEquiv_symm a₀ a₁ (TwoSquare.mk _ _ _ _ qJ) K
  have hh (K : C₁) : H.map (a₁.unit.app K) ≫ qH.app (S₁.obj K) =
      a₃.unit.app (H.obj K) ≫ R₃.map (lH.app K) :=
    unit_mateEquiv_symm a₁ a₃ (TwoSquare.mk _ _ _ _ qH) K
  have hg (K : C₀) : G.map (a₀.unit.app K) ≫ qG.app (S₀.obj K) =
      a₂.unit.app (G.obj K) ≫ R₂.map (lG.app K) :=
    unit_mateEquiv_symm a₀ a₂ (TwoSquare.mk _ _ _ _ qG) K
  have hi (K : C₂) : I.map (a₂.unit.app K) ≫ qI.app (S₂.obj K) =
      a₃.unit.app (I.obj K) ≫ R₃.map (lI.app K) :=
    unit_mateEquiv_symm a₂ a₃ (TwoSquare.mk _ _ _ _ qI) K
  change S₃.map (c.app N) ≫ lI.app (G.obj N) ≫ I'.map (lG.app N) =
    lH.app (J.obj N) ≫ H'.map (lJ.app N) ≫ d.app (S₀.obj N)
  apply (a₃.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := a₃.unit.naturality (c.app N)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ← reassoc_of% (hi (G.obj N))]
  have hq := qI.naturality (lG.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  rw [← hq, ← I.map_comp_assoc, ← hg, I.map_comp]
  have hcn := c.naturality (a₀.unit.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hcn
  simp only [Category.assoc, Functor.id_obj] at hcn ⊢
  rw [← reassoc_of% hcn, hc]
  rw [← reassoc_of% (hh (J.obj N))]
  have hqn := qH.naturality (lJ.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hqn
  rw [← reassoc_of% hqn, ← H.map_comp_assoc, hj]
  simp only [Functor.map_comp, Category.assoc]

/-- Scalar extension commutes with the normalized geometric exchange mate.
This is an equality of comparisons on arbitrary derived objects and contains
no trace, invertibility assertion, or line endpoint.

Source: latest blueprint, diagonal coefficient changes, proof paragraph (3),
interchange of scalar and geometric adjunction mates.
(blueprint: lem-diagonal-scalar-exchange-cube).

Proof: transport each right-derived model to its canonical functor using its
full universal-unit equation. Uniqueness of right derivation identifies the
normalized restriction square with the geometric mate of exact restriction
commuting with inverse image. Scalar extension and inverse image have the
canonical tensor balancing comparison. Its normalization on K-flat complexes
shows compatibility with composition of two geometric inverse images. Paste
these two composition equations around the commutative geometric square.
Apply the interchange identity for adjunction mates in both directions.
This gives the exchange rectangle with inverse scalar/pullback comparisons;
cancel those isomorphisms to obtain the displayed orientation. Transport the
four right-derived models back. The unit equations ensure these transports
are precisely the eqToIso maps in modelExchange. -/
theorem scalar_model_exchange_cube
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D₀ : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D₀' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (D : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar T f'))
    (e₀ : D₀.R = derivedLower R f) (e₀' : D₀'.R = derivedLower R f')
    (e : D.R = derivedLower T f) (e' : D'.R = derivedLower T f')
    (he₀ : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D₀ e₀)
    (he₀' : IsCanonicalRightDerived (CondensedRing.lowerStar R f') D₀' e₀')
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar T f') D' e')
    (r : RestrictionSquare a f D₀ D) (r' : RestrictionSquare a f' D₀' D')
    (K : DerivedCategory (Modules R X)) :
    (scalarPullbackComparison a hS).app (D₀.R.obj K) ≫
        (derivedUpper T hS).map ((r.mate a).app K) ≫
        modelExchange T f f' hX hS h D D' e e' ((derivedScalars a X).obj K) =
      (derivedScalars a S').map (modelExchange R f f' hX hS h D₀ D₀' e₀ e₀' K) ≫
        (r'.mate a).app ((derivedUpper R hX).obj K) ≫
        D'.R.map ((scalarPullbackComparison a hX).app K) := by
  rcases D₀ with @⟨F₀, η₀, hu₀, hc₀, hs₀, ht₀⟩
  rcases D₀' with @⟨F₀', η₀', hu₀', hc₀', hs₀', ht₀'⟩
  rcases D with @⟨F, η, hu, hc, hs, ht⟩
  rcases D' with @⟨F', η', hu', hc', hs', ht'⟩
  dsimp only at e₀ e₀' e e'
  subst F₀ F₀' F F'
  simp only [modelExchange, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  have hr := restriction_geometric_mate a f _ _ rfl rfl he₀ he r r.iso.hom
    (fun N ↦ by simp)
  have hr' := restriction_geometric_mate a f' _ _ rfl rfl he₀' he' r' r'.iso.hom
    (fun N ↦ by simp)
  have hf : (CondensedRing.derivedUpperStarLowerStarAdjunction T f).IsMateSquare
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
      (scalarRestrictionPullbackIso a f) r.iso := by
    rw [Adjunction.isMateSquare_iff]
    exact hr.symm
  have hf' : (CondensedRing.derivedUpperStarLowerStarAdjunction T f').IsMateSquare
      (CondensedRing.derivedUpperStarLowerStarAdjunction R f')
      (scalarRestrictionPullbackIso a f') r'.iso := by
    rw [Adjunction.isMateSquare_iff]
    exact hr'.symm
  have hex := NatTrans.SquareCompatible.exchangeRight hf hf'
    (restriction_pullback_square a f f' hX hS h)
  change NatTrans.SquareCompatible
    (Functor.pasteSquareIso r.iso (scalarRestrictionPullbackIso a hS))
    (Functor.pasteSquareIso (scalarRestrictionPullbackIso a hX) r'.iso)
    (derivedExchange T f f' hX hS h) (derivedExchange R f f' hX hS h) at hex
  have hc := fun M ↦ square_inverse _ _ _ _ hex M
  simp only [Functor.pasteSquareIso_inv_app, Category.assoc] at hc
  have result := scalar_mate_cube
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X'))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S'))
    r.iso.inv (scalarRestrictionPullbackIso a hS).inv
    (scalarRestrictionPullbackIso a hX).inv r'.iso.inv
    (derivedExchange R f f' hX hS h) (derivedExchange T f f' hX hS h) hc K
  have hiT := (derivedUpper T hS).map_id
    ((derivedLower T f).obj ((derivedScalars a X).obj K))
  have hiR := (derivedUpper R hS).map_id ((derivedLower R f).obj K)
  erw [hiT, hiR]
  repeat first
    | erw [Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact result.symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
