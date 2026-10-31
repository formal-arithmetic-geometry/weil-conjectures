/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictEtaleIsomorphicStageProjectionInterfaces
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import all WeilConjectures.SecSmoothPurity.LocalizedExtensionZeroLinearDerived
import all WeilConjectures.AlgebraicGeometry.EtaleBrownLevelRealizationData
import all WeilConjectures.AlgebraicGeometry.FiniteFreeExceptionalMate
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
/-! # Finite-free strict etale scalar comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
@[instance_reducible] private def levelLinear (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :
    Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) (strictEtaleLevel T O ell n) := by
  let R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O ell n
  let sigma := fun V : T.Etaleᵒᵖ ↦
    ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).app V).hom
  exact CategoryTheory.sectionLinear R _ sigma (by
    intro V W f b
    exact congrArg (fun g ↦ g b)
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).naturality f).symm)

private def toPoint (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    M ⟶ (constantSheaf T.smallEtaleTopology (Type (u + 1))).obj PUnit where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun _ ↦
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          PUnit.{u + 2})).app U PUnit.unit)
      naturality := by
        intro V W f
        ext x
        exact congrArg (fun g ↦ g PUnit.unit)
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            PUnit.{u + 2})).naturality f) }

private theorem constantSection_apply (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) (n : ℕ) (r : O ⧸ Ideal.span {ell} ^ (n + 1)) (V : T.Etaleᵒᵖ)
    (x : ((constantSheaf T.smallEtaleTopology (Type (u + 1))).obj PUnit).obj.obj V) :
    (coefficientConstantSection (J := T.smallEtaleTopology) O ell n r).hom.app V x =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).app V r := by
  let J := T.smallEtaleTopology
  let P := (Functor.const T.Etaleᵒᵖ).obj PUnit.{u + 2}
  let R := coefficientQuotientSheaf (J := J) O ell n
  let Rset := (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj R
  have : IsIso (toSheafify J P) :=
    isIso_toSheafify J (Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit)
  obtain ⟨p, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify J P).app V)).2 x
  let t : P ⟶ Rset.obj :=
    (Functor.const T.Etaleᵒᵖ).map (TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ r)) ≫
      whiskerRight (toSheafify J ((Functor.const T.Etaleᵒᵖ).obj
        (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1)))))
          (CategoryTheory.forget CommRingCat.{u + 1})
  have h := ((sheafificationAdjunction J (Type (u + 1))).homEquiv P Rset)
    |>.apply_symm_apply t
  exact congrArg (fun f ↦ f.app V p) h

private theorem ordinaryImage_linear
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T W : Scheme.{u}} {g : T ⟶ W} (S : StrictEtaleOrdinaryImage O ell g) (n : ℕ) :
    let := levelLinear T O ell n
    let := levelLinear W O ell n
    (S.lift n).modules.Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) := by
  let := levelLinear T O ell n
  let := levelLinear W O ell n
  rw [Functor.linear_iff]
  intro M r
  let U := coefficientUnderlying (J := W.smallEtaleTopology) O ell n
  let V := coefficientUnderlying (J := T.smallEtaleTopology) O ell n
  let L := Scheme.etaleSetPullback g
  let z := U.map (r • 𝟙 M)
  let a := toPoint W (U.obj M) ≫
    coefficientConstantSection (J := W.smallEtaleTopology) O ell n r
  have hz : ∀ (Q : W.Etaleᵒᵖ) (x : M.val.obj Q),
      (@id (M.val.obj Q) (z.hom.app Q x)) =
        (@id ((coefficientQuotientSheaf (J := W.smallEtaleTopology) O ell n).obj.obj Q)
          (a.hom.app Q x)) • x := by
    intro Q x
    change _ = (coefficientConstantSection (J := W.smallEtaleTopology)
      O ell n r).hom.app Q _ • x
    rw [constantSection_apply]
    rfl
  have hs := (S.lift n).moduleSMul M (U.obj M) a (𝟙 _) z hz
  have hc : L.map a ≫ (S.lift n).ringUnderlying.hom =
      L.map (toPoint W (U.obj M)) ≫ S.singleton.hom ≫
        coefficientConstantSection (J := T.smallEtaleTopology) O ell n r := by
    dsimp only [a]
    rw [Functor.map_comp, Category.assoc, S.constants n r]
  apply V.map_injective
  apply (cancel_epi ((S.lift n).moduleUnderlying.inv.app M)).1
  have hn := (S.lift n).moduleUnderlying.inv.naturality (r • 𝟙 M)
  change L.map z ≫ (S.lift n).moduleUnderlying.inv.app M =
    (S.lift n).moduleUnderlying.inv.app M ≫ V.map ((S.lift n).modules.map (r • 𝟙 M)) at hn
  rw [← hn]
  apply Sheaf.hom_ext
  ext Q x
  have h := hs Q x
  have hc' := congrArg (fun t ↦ t.hom.app Q x) hc
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply] at hc'
  change ((S.lift n).moduleUnderlying.inv.app M).hom.app Q
      ((L.map z).hom.app Q x) = _
  dsimp only [id] at h
  rw [hc', constantSection_apply] at h
  have hi : (L.map (𝟙 (U.obj M))).hom.app Q x = x := by
    exact congrArg (fun t ↦ t.hom.app Q x) (L.map_id (U.obj M))
  rw [hi] at h
  change _ =
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
      (CommRingCat.of (O ⧸ Ideal.span {ell} ^ (n + 1))))).app Q r •
      (show ((S.lift n).modules.obj M).val.obj Q from
        ((S.lift n).moduleUnderlying.inv.app M).hom.app Q x)
  exact h

private theorem derivedImage_inverse_linear
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {T W : Scheme.{u}} {g : T ⟶ W} (S : StrictEtaleOrdinaryImage O ell g) (n : ℕ)
    (D : CoefficientDerivedImage (S.lift n).modules (S.right n) (S.levelAdj n)) :
    let := levelLinear T O ell n
    let := levelLinear W O ell n
    D.inverse.Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) := by
  let := levelLinear T O ell n
  let := levelLinear W O ell n
  have : (S.lift n).modules.Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) :=
    ordinaryImage_linear S n
  let F := (S.lift n).modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel W O ell n) (.up ℤ))
      F D.inverse := ⟨D.inverseFactors⟩
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso (strictEtaleLevel W O ell n) (.up ℤ))
    (O ⧸ Ideal.span {ell} ^ (n + 1)) F D.inverse).1 inferInstance

private theorem support_linear
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    let := levelLinear X O ell n
    let := levelLinear Y O ell n
    (S.levelFunctor n).Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) := by
  let := levelLinear X O ell n
  let := levelLinear Y O ell n
  let := levelLinear c.Z O ell n
  have : (S.openDerived.level n).inverse.Linear
      (O ⧸ Ideal.span {ell} ^ (n + 1)) :=
    derivedImage_inverse_linear S.openImage n (S.openDerived.level n)
  have : (S.properDerived.level n).inverse.Linear
      (O ⧸ Ideal.span {ell} ^ (n + 1)) :=
    derivedImage_inverse_linear S.properImage n (S.properDerived.level n)
  have : (S.levelDerivedOpen n).Linear (O ⧸ Ideal.span {ell} ^ (n + 1)) :=
    (S.levelDerivedOpenAdjunction n).left_adjoint_linear
  have : (S.properDerived.level n).direct.Linear
      (O ⧸ Ideal.span {ell} ^ (n + 1)) :=
    (S.properDerived.level n).adjunction.right_adjoint_linear
  unfold StrictEtaleCompactSupport.levelFunctor
  infer_instance

private theorem transportBasis
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Preadditive C] [Preadditive D] [Preadditive C'] [Preadditive D']
    [HasFiniteBiproducts C] [HasFiniteBiproducts C']
    {B : Type*} [Ring B] [Linear B D] [Linear B D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (F : C ⥤ C') (G : D ⥤ D') [F.Additive]
    [F.IsEquivalence] [G.IsEquivalence] [G.Linear B]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (beta : R ⋙ F ≅ G ⋙ R')
    (r : ℕ) (coeff : Fin r → B)
    (h : ∀ M, IsIso (biproduct.desc fun i : Fin r ↦
      adj'.unit.app M ≫ R'.map (coeff i • 𝟙 _))) (M : C) :
    IsIso (biproduct.desc fun i : Fin r ↦ adj.unit.app M ≫ R.map (coeff i • 𝟙 _)) := by
  let alpha := ((mateEquiv adj adj').symm beta.hom).natTrans
  have : IsIso alpha := isIso_inverseMate_of_equivalences adj adj' beta
  have hu := unit_mateEquiv_symm adj adj' beta.hom M
  change F.map (adj.unit.app M) ≫ beta.hom.app (L.obj M) =
    adj'.unit.app (F.obj M) ≫ R'.map (alpha.app M) at hu
  have hc (i : Fin r) :
      F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _)) ≫
          beta.hom.app (L.obj M) =
        (adj'.unit.app (F.obj M) ≫ R'.map (coeff i • 𝟙 _)) ≫
          R'.map (alpha.app M) := by
    rw [F.map_comp, Category.assoc]
    have hn := beta.hom.naturality (coeff i • 𝟙 (L.obj M))
    change F.map (R.map _) ≫ beta.hom.app _ =
      beta.hom.app _ ≫ R'.map (G.map _) at hn
    rw [hn, ← Category.assoc, hu, G.map_smul, G.map_id]
    simp only [Category.assoc, ← R'.map_comp]
    congr 2
    rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
    exact congrArg (fun t ↦ coeff i • t) (Category.comp_id (alpha.app M))
  have he : (biproduct.desc fun i : Fin r ↦
      F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _))) ≫ beta.hom.app (L.obj M) =
        (biproduct.desc fun i : Fin r ↦ adj'.unit.app (F.obj M) ≫
          R'.map (coeff i • 𝟙 _)) ≫ R'.map (alpha.app M) := by
    ext i
    simpa only [biproduct.ι_desc_assoc] using hc i
  have : IsIso (biproduct.desc fun i : Fin r ↦
      F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _))) := by
    have := h (F.obj M)
    have : IsIso ((biproduct.desc fun i : Fin r ↦
        F.map (adj.unit.app M ≫ R.map (coeff i • 𝟙 _))) ≫
          beta.hom.app (L.obj M)) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (beta.hom.app (L.obj M))
  have := Functor.isIso_map_biproductDesc F
    (φ := fun i : Fin r ↦ adj.unit.app M ≫ R.map (coeff i • 𝟙 _))
  exact isIso_of_reflects_iso _ F

private theorem scalarRestriction_reflects
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n : ℕ)
    (D : StrictEtaleLevelScalar a T n) : D.restriction.ReflectsIsomorphisms := by
  let R := SheafOfModules.restrictScalars
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  have : R.ReflectsIsomorphisms := by
    have : (R ⋙ SheafOfModules.toSheaf _).ReflectsIsomorphisms := by
      change (SheafOfModules.toSheaf _).ReflectsIsomorphisms
      infer_instance
    exact reflectsIsomorphisms_of_comp R (SheafOfModules.toSheaf _)
  have : R.mapDerivedCategory.ReflectsIsomorphisms := by
    constructor
    intro K L f hf
    rw [DerivedCategory.isIso_iff]
    intro k
    have : IsIso (R.map ((DerivedCategory.homologyFunctor _ k).map f)) :=
      (NatIso.isIso_map_iff (R.mapDerivedCategoryHomologyFunctorIso k) f).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ R
  let e : D.restriction ≅ R.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O' mu n) (.up ℤ))
      (DerivedCategory.Q ⋙ D.restriction) (DerivedCategory.Q ⋙ R.mapDerivedCategory)
      D.restriction R.mapDerivedCategory (D.restrictionFactors ≪≫ R.mapDerivedCategoryFactors.symm)
  exact reflectsIsomorphisms_of_iso e.symm

private theorem scalarBasis
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) (T : Scheme.{u}) (n r : ℕ)
    (basis : Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1)))))
    (D : StrictEtaleLevelScalar a T n) :
    let := levelLinear T O' mu n
    ∀ M, IsIso (biproduct.desc fun i : Fin r ↦
      D.derivedAdj.unit.app M ≫ D.restriction.map
        (ModuleCat.restrictScalarsSelfVal (a.ring n) (basis i) • 𝟙 (D.derived.obj M))) := by
  let := levelLinear T O' mu n
  let A := O ⧸ Ideal.span {ell} ^ (index n + 1)
  let B := O' ⧸ Ideal.span {mu} ^ (n + 1)
  let : Algebra A B := (a.ring n).toAlgebra
  change Module.Basis (Fin r) A B at basis
  let FA : strictEtaleLevel T O ell (index n) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat A) :=
    strictEtaleBrownConstant O ell T (index n)
  let FB : strictEtaleLevel T O' mu n ⥤
      Sheaf T.smallEtaleTopology (ModuleCat B) := strictEtaleBrownConstant O' mu T n
  have : FA.Additive := brownConstantAdditive T A
  have : FB.Additive := brownConstantAdditive T B
  have : FA.IsEquivalence := brownConstantEquivalence T A
  have : FB.IsEquivalence := brownConstantEquivalence T B
  have : FB.Linear B := by
    constructor
    intro M N f b
    ext U x
    rfl
  obtain ⟨SC⟩ := CategoryTheory.exceptionalScalarPresentation.{u + 1, u + 1, u + 1, u}
    T.smallEtaleTopology r basis
  let R := SheafOfModules.restrictScalars
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  let e : D.restriction ≅ R.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O' mu n) (.up ℤ))
      (DerivedCategory.Q ⋙ D.restriction) (DerivedCategory.Q ⋙ R.mapDerivedCategory)
      D.restriction R.mapDerivedCategory (D.restrictionFactors ≪≫ R.mapDerivedCategoryFactors.symm)
  let beta : D.restriction ⋙ FA.mapDerivedCategory ≅ FB.mapDerivedCategory ⋙
      (Sheaf.restrictScalars T.smallEtaleTopology (a.ring n)).mapDerivedCategory :=
    isoWhiskerRight e FA.mapDerivedCategory ≪≫
      Functor.mapDerivedCategorySquareIso
        (A := strictEtaleLevel T O' mu n) (B := strictEtaleLevel T O ell (index n))
        (brownGenericRestriction T (.of A) (.of B) (CommRingCat.ofHom (a.ring n)))
  dsimp only
  intro M
  apply transportBasis FA.mapDerivedCategory FB.mapDerivedCategory D.derivedAdj SC.adj beta
    r (fun i ↦ basis i) (fun K ↦ ?_) M
  have he : (biproduct.desc fun i : Fin r ↦ SC.adj.unit.app K ≫
      (Sheaf.restrictScalars T.smallEtaleTopology (algebraMap A B)).mapDerivedCategory.map
        (basis i • 𝟙 (SC.T.obj K))) = (SC.coordinates K).inv := by
    ext i
    exact (biproduct.ι_desc _ i).trans (SC.column K i).symm
  rw [he]
  infer_instance

/-- The counit-defined exceptional mate for a finite-free strict etale scalar
projection is invertible at each level. No system exceptional adjoint is constructed.
Source: Zheng, Proposition 2.29(2), and Construction 5.15.
(blueprint: lem-pur-etale-finite-free-mate-at-level).

Proof: fix n and write T_W adjoint to U_W for derived scalar extension and
restriction. Compose adjunction Hom bijections and the projection isomorphism to
identify U_X G_B with G_A U_Y. Its counit characterization follows by evaluating
this chain on the identity. Restrict the exceptional mate and compose with this
right-adjoint uniqueness comparison. Its transpose is the extended A-counit
preceded by the inverse projection, by the triangle identities. Choose a finite
basis for B over A. The normalized projection, after restriction, is the finite
biproduct comparison for the compact-support functor: this follows from its
open/proper mate normalizations and the tensor-unit equations. To identify the
supplied level projection, insert complexes supported only at index n into its
evaluation equation. This exact section of evaluation makes that equation determine
the level map on every complex. The columns of the
restricted exceptional mate are consequently G_A of the basis inclusions. Their
inverse has rows G_A of the basis projections; finite additivity and the biproduct
identities give both inverse equations. Restriction detects zero cohomology and
therefore reflects isomorphisms on derived categories, proving the original mate
invertible. Changing the given right adjoints changes this calculation only by the
unique adjunction-compatible isomorphisms, so it holds for the supplied adjunctions.
-/
theorem strictEtaleFiniteFreeMateAtLevel
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (hfree : ∀ n, ∃ r : ℕ, Nonempty (Module.Basis (Fin r)
      (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1))))))
    (P : StrictEtaleTransportProjection a c SA SB TX TY TZ)
    (GA : ∀ n, DerivedCategory (strictEtaleLevel Y O ell (index n)) ⥤
      DerivedCategory (strictEtaleLevel X O ell (index n)))
    (GB : ∀ n, DerivedCategory (strictEtaleLevel Y O' mu n) ⥤
      DerivedCategory (strictEtaleLevel X O' mu n))
    (adjA : ∀ n, SA.levelFunctor (index n) ⊣ GA n)
    (adjB : ∀ n, SB.levelFunctor n ⊣ GB n)
    (n : ℕ) :
    IsIso (mateEquiv (adjA n) (adjB n) (.mk _ _ _ _ (P.level n).inv)).natTrans := by
  classical
  obtain ⟨r, ⟨basis⟩⟩ := hfree n
  let := levelLinear X O' mu n
  let := levelLinear Y O' mu n
  have : (SB.levelFunctor n).Linear (O' ⧸ Ideal.span {mu} ^ (n + 1)) :=
    support_linear SB n
  have : (GB n).Linear (O' ⧸ Ideal.span {mu} ^ (n + 1)) :=
    (adjB n).right_adjoint_linear
  have : (GA n).Additive := by
    have : PreservesLimitsOfSize.{0, 0} (GA n) := (adjA n).rightAdjoint_preservesLimits
    exact Functor.additive_of_preserves_binary_products (GA n)
  have : (TX.level n).restriction.ReflectsIsomorphisms :=
    scalarRestriction_reflects a X n (TX.level n)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦ ?_)
  have := scalarBasis a X n r basis (TX.level n) ((GA n).obj M)
  have := scalarBasis a Y n r basis (TY.level n) M
  apply Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc
    (adjA n) (adjB n) (P.level n).symm
    (TX.level n).derivedAdj (TY.level n).derivedAdj M
    (fun i : Fin r ↦ ModuleCat.restrictScalarsSelfVal (a.ring n) (basis i) •
      𝟙 ((TY.level n).derived.obj M))
    (fun i : Fin r ↦ ModuleCat.restrictScalarsSelfVal (a.ring n) (basis i) •
      𝟙 ((TX.level n).derived.obj ((GA n).obj M)))
  intro i
  rw [(GB n).map_smul, (GB n).map_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp]
  exact congrArg (fun t ↦ ModuleCat.restrictScalarsSelfVal (a.ring n) (basis i) • t)
    (Category.comp_id _).symm
end AlgebraicGeometry
