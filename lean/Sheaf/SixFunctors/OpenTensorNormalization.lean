/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData
import Sheaf.SixFunctors.FiniteComparisonsExistence
import Sheaf.SixFunctors.FiniteCompatibilityTransport
import Sheaf.SixFunctors.OpenOperationModels
import Sheaf.SixFunctors.OpenPullbackSupport
import Sheaf.SixFunctors.OpenTensorSupport
import all Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.ResolvingRepresentativeWhiskering

/-!
# Normalized open extension, tensor and base change

Construct the site square and tensor models explicitly. Open-support results make
the adjunction transposes invertible; their adjunct equations then determine both
restriction formulas. Source: Stacks 03DI, 0F6Z, 0E8I and 0GL1
(blueprint: lem-sf-open-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v h w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

set_option backward.isDefEq.respectTransparency false in
private def normalizedSiteSquare {m : Mode} (d : Input.{u} m) : SiteSquare d := by
  let sq := IsPullback.of_iso_pullback d.square.toCommSq d.square.isoPullback
    d.square.hom_fst d.square.hom_snd
  let c := MorphismProperty.Over.pullbackMapComparison
    (inferInstance : WeaklyEtale d.j) (inferInstance : WeaklyEtale d.j') sq.toCommSq
  have hc : IsIso c :=
    MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
      (inferInstance : WeaklyEtale d.j) (inferInstance : WeaklyEtale d.j') sq
  let e := (asIso c).symm
  cases m with
  | ordinary =>
    refine ⟨e, ?_⟩
    intro W
    apply heq_of_eq
    change (c.app W).left ≫ pullback.fst (W.hom ≫ d.j) d.g =
      pullback.fst W.hom d.gU
    simp only [c, MorphismProperty.Over.pullbackMapComparison_app_left, pullback.lift_fst]
  | systems =>
    let e' := NatIso.prod (Iso.refl (𝟭 ℕ)) e
    refine ⟨e', ?_⟩
    intro W
    apply heq_of_eq
    change (c.app W.2).left ≫ pullback.fst (W.2.hom ≫ d.j) d.g =
      pullback.fst W.2.hom d.gU
    simp only [c, MorphismProperty.Over.pullbackMapComparison_app_left, pullback.lift_fst]

private theorem ordinaryUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Mod (restrictRing m j R)) :
    IsIso (o.adjunction.unit.app M) := by
  have h : o.adjunction.unit.app M = (o.sectionIso M).inv := by
    apply (cancel_mono (o.sectionIso M).hom).1
    rw [o.sectionUnit, Iso.inv_hom_id]
    rfl
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem derivedUnit_isIso {m : Mode} {U X : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {R : Sheaf (topology m X) CommRingCat.{u + 1}}
    (o : OpenExtension m j R) (M : Der (restrictRing m j R)) :
    IsIso ((exactDerivedAdjunction o.adjunction).unit.app M) := by
  let a := exactDerivedAdjunction o.adjunction
  have hQ (P : CochainComplex (Mod (restrictRing m j R)) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ,
          IsIso (((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ ordinaryUnit_isIso o (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((o.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (restrict m j R).mapDerivedCategoryFactors.inv.app _ ≫
            (restrict m j R).mapDerivedCategory.map
              (o.ordinary.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, exactDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

set_option backward.isDefEq.respectTransparency false in
private def normalizedRightSquare {m : Mode} {d : Input.{u} m} (t : SiteSquare d) :
    direct m d.g d.R d.S d.coefficient ⋙ restrict m d.j d.R ≅
      restrict m d.j' d.S ⋙ direct m d.gU _ _ (cornerCoefficient t) := by
  letI : (openInclusion m d.j ⋙ baseChange m d.g).IsContinuous
      (topology m d.U) (topology m d.X') :=
    Functor.isContinuous_comp _ _ _ (topology m d.X) _
  letI : (baseChange m d.gU ⋙ openInclusion m d.j').IsContinuous
      (topology m d.U) (topology m d.X') :=
    Functor.isContinuous_comp _ _ _ (topology m d.U') _
  let a : ((sheafCompose (topology m d.U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (restrictRing m d.j d.R)) ⟶
      ((openInclusion m d.j ⋙ baseChange m d.g).sheafPushforwardContinuous
        RingCat.{u + 1} (topology m d.U) (topology m d.X')).obj
          ((sheafCompose (topology m d.X')
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj d.S) :=
    ⟨Functor.whiskerRight (Functor.whiskerLeft (openInclusion m d.j).op d.coefficient.hom)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  exact SheafOfModules.pushforwardNatIso a t.iso.symm

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedRightSquare_sections {m : Mode} {d : Input.{u} m}
    (t : SiteSquare d) (N : Mod d.S) (W : (Site m d.U)ᵒᵖ)
    (x : N.val.obj ((openInclusion m d.j ⋙ baseChange m d.g).op.obj W)) :
    ((normalizedRightSquare t).hom.app N).val.app W x =
      N.val.map (t.iso.inv.app W.unop).op x := by
  rfl

private def transposeNatural
    {A B E : Type*} [Category A] [Category B] [Category E]
    {F : A ⥤ B} {G : B ⥤ A} (a : F ⊣ G) {P : E ⥤ A} {Q : E ⥤ B}
    (t : P ⟶ Q ⋙ G) : P ⋙ F ⟶ Q where
  app X := (a.homEquiv _ _).symm (t.app X)
  naturality _X _Y f := a.homEquiv_naturality_right_square _ _ _ _ (t.naturality f)

set_option backward.isDefEq.respectTransparency false in
private def betaInverse {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) : o.gUPull.derived ⋙ o.opens.jShriek' ⟶
      o.opens.jShriek ⋙ o.gPull.derived :=
  transposeNatural o.opens.adj'
    (Functor.whiskerRight o.opens.adj.unit o.gUPull.derived ≫
      Functor.whiskerLeft o.opens.jShriek o.theta.inv)

set_option backward.isDefEq.respectTransparency false in
private def gammaInverse {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) :
    (𝟭 _).prod o.opens.jStar ⋙ o.tensorU.functor ⋙ o.opens.jShriek ⟶
      o.opens.jShriek.prod (𝟭 _) ⋙ o.tensorX.functor := by
  let c : o.tensorX.functor ⋙ o.opens.jStar ≅
      (o.opens.jStar.prod o.opens.jStar) ⋙ o.tensorU.functor :=
    o.tensorComparison.comparison
  let tau : (𝟭 _).prod o.opens.jStar ⋙ o.tensorU.functor ⟶
      (o.opens.jShriek.prod (𝟭 _) ⋙ o.tensorX.functor) ⋙ o.opens.jStar :=
    { app X := o.tensorU.functor.map
        (Prod.mkHom (o.opens.adj.unit.app X.1) (𝟙 _)) ≫
          c.inv.app (o.opens.jShriek.obj X.1, X.2)
      naturality X Y f := by
        have hn :
            Prod.mkHom f.1 (o.opens.jStar.map f.2) ≫
                Prod.mkHom (o.opens.adj.unit.app Y.1) (𝟙 _) =
              Prod.mkHom (o.opens.adj.unit.app X.1) (𝟙 _) ≫
                (o.opens.jStar.prod o.opens.jStar).map
                  (Prod.mkHom (o.opens.jShriek.map f.1) f.2) := by
          ext
          · exact o.opens.adj.unit.naturality f.1
          · simp
        change o.tensorU.functor.map _ ≫ (o.tensorU.functor.map _ ≫ c.inv.app _) =
          (o.tensorU.functor.map _ ≫ c.inv.app _) ≫ o.opens.jStar.map _
        dsimp only [Functor.prod_map, Functor.id_map, Functor.comp_map]
        rw [← Category.assoc, ← o.tensorU.functor.map_comp, hn,
          o.tensorU.functor.map_comp, Category.assoc, Category.assoc]
        congr 1
        exact c.inv.naturality (Prod.mkHom (o.opens.jShriek.map f.1) f.2) }
  exact transposeNatural o.opens.adj tau

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_of_adjunct
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) {X : B} {Y : A} (b : X ≅ F.obj Y) (e : Y ≅ G.obj X)
    (h : a.homEquiv _ _ b.inv = e.hom) :
    G.map b.hom = e.inv ≫ a.unit.app Y := by
  have he : e.hom ≫ G.map b.hom = a.unit.app Y := by
    rw [← h, Adjunction.homEquiv_unit, Category.assoc, ← G.map_comp,
      b.inv_hom_id, G.map_id]
    exact Category.comp_id _
  apply (cancel_epi e.hom).1
  rw [he, ← Category.assoc, e.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_of_adjunct
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) [IsIso a.unit] {X : B} {Y : A} (f : F.obj Y ⟶ X)
    (hf : IsIso (a.homEquiv _ _ f)) (hs : F.essImage X) : IsIso f := by
  have : F.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : F.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (a.counit.app X) := a.isIso_counit_app_iff_mem_essImage.mpr hs
  have := hf
  have he : f = F.map (a.homEquiv _ _ f) ≫ a.counit.app X := by
    exact ((a.homEquiv _ _).symm_apply_apply f).symm
  rw [he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private def assertionOfIsIso {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) [IsIso (betaInverse o)] [IsIso (gammaInverse o)] : Assertion o := by
  have hu : ∀ M, IsIso (o.opens.adj.unit.app M) := derivedUnit_isIso o.opens.extension
  have hu' : ∀ M, IsIso (o.opens.adj'.unit.app M) := derivedUnit_isIso o.opens.extension'
  letI : IsIso o.opens.adj.unit := NatIso.isIso_of_isIso_app _
  letI : IsIso o.opens.adj'.unit := NatIso.isIso_of_isIso_app _
  let b := (asIso (betaInverse o)).symm
  let c := (asIso (gammaInverse o)).symm
  have hb (M) : o.opens.adj'.homEquiv _ _ (b.inv.app M) =
      o.gUPull.derived.map (o.opens.adj.unit.app M) ≫
        o.theta.inv.app (o.opens.jShriek.obj M) := by
    exact (o.opens.adj'.homEquiv _ _).apply_symm_apply _
  have hc (M N) : o.opens.adj.homEquiv _ _ (c.inv.app (M, N)) =
      o.tensorU.functor.map (Prod.mkHom (o.opens.adj.unit.app M) (𝟙 _)) ≫
        o.tensorComparison.comparison.inv.app (o.opens.jShriek.obj M, N) := by
    exact (o.opens.adj.homEquiv _ _).apply_symm_apply _
  refine
    { unit := hu
      unit' := hu'
      ordinaryUnit := ordinaryUnit_isIso o.opens.extension
      ordinaryUnit' := ordinaryUnit_isIso o.opens.extension'
      full := o.opens.adj.fullyFaithfulLOfIsIsoUnit.full
      faithful := o.opens.adj.fullyFaithfulLOfIsIsoUnit.faithful
      full' := o.opens.adj'.fullyFaithfulLOfIsIsoUnit.full
      faithful' := o.opens.adj'.fullyFaithfulLOfIsIsoUnit.faithful
      beta := b
      gamma := c
      beta_inverse := hb
      gamma_inverse := hc
      beta_restriction := ?_
      gamma_restriction := ?_ }
  · intro M
    let i : M ≅ o.opens.jStar.obj (o.opens.jShriek.obj M) :=
      asIso (o.opens.adj.unit.app M)
    let e := o.gUPull.derived.mapIso i ≪≫ (o.theta.app (o.opens.jShriek.obj M)).symm
    have hi : i.inv = inv (o.opens.adj.unit.app M) := asIso_inv _
    have he : e.inv = o.theta.hom.app (o.opens.jShriek.obj M) ≫
        o.gUPull.derived.map (inv (o.opens.adj.unit.app M)) := by
      change o.theta.hom.app _ ≫ o.gUPull.derived.map i.inv = _
      rw [hi]
    change (restrict m d.j' d.S).mapDerivedCategory.map (b.app M).hom = _
    rw [restriction_of_adjunct o.opens.adj' (b.app M) e (hb M), he]
    exact Category.assoc _ _ _
  · intro M N
    let c0 : o.tensorX.functor ⋙ o.opens.jStar ≅
        (o.opens.jStar.prod o.opens.jStar) ⋙ o.tensorU.functor :=
      o.tensorComparison.comparison
    let i : M ≅ o.opens.jStar.obj (o.opens.jShriek.obj M) :=
      asIso (o.opens.adj.unit.app M)
    let e := o.tensorU.functor.mapIso (i.prod (Iso.refl (o.opens.jStar.obj N))) ≪≫
      (c0.app (o.opens.jShriek.obj M, N)).symm
    have hi : i.inv = inv (o.opens.adj.unit.app M) := asIso_inv _
    let q : (o.opens.jStar.obj (o.opens.jShriek.obj M), o.opens.jStar.obj N) ⟶
        (M, o.opens.jStar.obj N) :=
      Prod.mkHom (inv (o.opens.adj.unit.app M)) (𝟙 (o.opens.jStar.obj N))
    have hq : (i.prod (Iso.refl (o.opens.jStar.obj N))).inv = q := by
      apply Prod.hom_ext
      · exact hi
      · rfl
    have he : e.inv = c0.hom.app (o.opens.jShriek.obj M, N) ≫
        o.tensorU.functor.map q := by
      change c0.hom.app _ ≫ o.tensorU.functor.map _ = _
      rw [hq]
    change (restrict m d.j d.R).mapDerivedCategory.map (c.app (M, N)).hom = _
    rw [restriction_of_adjunct o.opens.adj (c.app (M, N)) e (hc M N), he]
    exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
private def assertionOfSupported {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t)
    (hb : ∀ M, o.opens.jShriek'.essImage (o.gPull.derived.obj (o.opens.jShriek.obj M)))
    (hc : ∀ M N, o.opens.jShriek.essImage
      (o.tensorX.functor.obj (o.opens.jShriek.obj M, N))) : Assertion o := by
  have hu : ∀ M, IsIso (o.opens.adj.unit.app M) := derivedUnit_isIso o.opens.extension
  have hu' : ∀ M, IsIso (o.opens.adj'.unit.app M) := derivedUnit_isIso o.opens.extension'
  letI : IsIso o.opens.adj.unit := NatIso.isIso_of_isIso_app _
  letI : IsIso o.opens.adj'.unit := NatIso.isIso_of_isIso_app _
  have hbeta (M) : IsIso ((betaInverse o).app M) := by
    apply isIso_of_adjunct o.opens.adj' ((betaInverse o).app M) _ (hb M)
    change IsIso ((o.opens.adj'.homEquiv _ _)
      ((o.opens.adj'.homEquiv _ _).symm
        (o.gUPull.derived.map (o.opens.adj.unit.app M) ≫
          o.theta.inv.app (o.opens.jShriek.obj M))))
    rw [Equiv.apply_symm_apply]
    infer_instance
  have hgamma (X : Der (restrictRing m d.j d.R) × Der d.R) :
      IsIso ((gammaInverse o).app X) := by
    rcases X with ⟨M, N⟩
    apply isIso_of_adjunct o.opens.adj ((gammaInverse o).app (M, N)) _ (hc M N)
    change IsIso ((o.opens.adj.homEquiv _ _)
      ((o.opens.adj.homEquiv _ _).symm
        (o.tensorU.functor.map (Prod.mkHom (o.opens.adj.unit.app M) (𝟙 _)) ≫
          o.tensorComparison.comparison.inv.app (o.opens.jShriek.obj M, N))))
    rw [Equiv.apply_symm_apply]
    let c0 : o.tensorX.functor ⋙ o.opens.jStar ≅
        (o.opens.jStar.prod o.opens.jStar) ⋙ o.tensorU.functor :=
      o.tensorComparison.comparison
    let q : (M, o.opens.jStar.obj N) ⟶
        (o.opens.jStar.obj (o.opens.jShriek.obj M), o.opens.jStar.obj N) :=
      Prod.mkHom (o.opens.adj.unit.app M) (𝟙 _)
    have hq : IsIso q := (isIso_prod_iff _ _).2 ⟨hu M, inferInstance⟩
    change IsIso (o.tensorU.functor.map q ≫ c0.inv.app (o.opens.jShriek.obj M, N))
    infer_instance
  letI : IsIso (betaInverse o) := NatIso.isIso_of_isIso_app _
  letI : IsIso (gammaInverse o) := NatIso.isIso_of_isIso_app _
  exact assertionOfIsIso o

private theorem tensorModel_exists {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u + 1}) :
    Nonempty (TensorModel R) := by
  let A := Mod R
  let H := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨P, hp, hloc, ⟨B, ⟨hB⟩, T, ⟨hT⟩⟩, hd⟩ :=
    site_derived_tensor_descent_independentCoefficients.{u + 1, u, u + 1, u + 2, 0, 0} J R
  let f : (resolving R).FullSubcategory ⥤ P.FullSubcategory :=
    P.lift ((resolving R).ι ⋙ H) (fun X ↦ (hp _).2 X.property)
  let e : (resolving R).ι ⋙ H ⋙ DerivedCategory.Qh ≅
      (resolving R).ι ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (resolving R).ι (DerivedCategory.quotientCompQhIso A)
  let rep : ((resolving R).ι.prod (resolving R).ι) ⋙ total R ⋙ DerivedCategory.Q ≅
      (((resolving R).ι ⋙ DerivedCategory.Q).prod
        ((resolving R).ι ⋙ DerivedCategory.Q)) ⋙ T :=
    Functor.isoWhiskerLeft (((resolving R).ι.prod (resolving R).ι) ⋙ total R)
        (DerivedCategory.quotientCompQhIso A).symm ≪≫
      Functor.isoWhiskerLeft ((resolving R).ι.prod (resolving R).ι)
        (Functor.isoWhiskerRight hB.symm DerivedCategory.Qh) ≪≫
      Functor.isoWhiskerLeft (f.prod f) hT ≪≫
      Functor.isoWhiskerRight (NatIso.prod e e) T
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X),
        HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨K, q, hK, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hs : ∀ n, IsFlatOnSite (J := J) (R := R) (K.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (K.X n)).symm (hf n)
    refine ⟨⟨H.obj K, (hp _).2 ⟨hK, hs⟩⟩, H.map q, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering (Der R) H
    (HomotopyCategory.quotient_obj_surjective) (HomotopyCategory.quasiIso A (.up ℤ))
    DerivedCategory.Qh (resolving R) P (fun X ↦ (hp _).symm) hres
  exact ⟨{ preadditive := tensorPreadditive R
           functor := T
           representative := rep
           descent := fun F G ↦ ff.map_bijective F G }⟩

/-- The open-factor normalization, in the original pro-etale topos and in the
ringed diagram topos of every strict inverse coefficient system.
Proof: identify open restriction with localization of the site. The Kan
extension indexing category over an open object has its unique factorization
as terminal object, so the presheaf unit inserts the original section.
Slice sheafification preserves this insertion. This gives exact extension,
invertible units and full faithfulness, and localizes the same adjunction.
The fibre-product projections define the right-adjoint square on sections;
its mate gives the ordinary pullback square. Resolve by flat-term K-flat
complexes and totalize its termwise maps to obtain the normalized theta.
On simple tensors restriction keeps both sections. Total tensor on K-flat
representatives gives the recorded tensor comparison, including its signs.
Transpose the two displayed maps to construct beta inverse and gamma inverse.
They are isomorphisms by localized-site base change and the extension/tensor
formula. The adjunct equations give the two restriction identities.
For systems do the entire construction on the vertical diagram site: sections
and their coefficient transitions are part of the same presheaf, so the
formulas already commute with all transitions, including nonflat ones.
This argument uses ordinary derived categories of diagram-site modules; no
enhancement, section-model equivalence or levelwise detection of equality is
used. Source: Stacks 03DI, 0F6Z, 04J0, 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-open-tensor-normalization). -/
theorem exists_normalized (m : Mode) (d : Input.{u} m) :
    ∃ (t : SiteSquare d) (o : Operations d t), Nonempty (Assertion o) := by
  let t := normalizedSiteSquare d
  obtain ⟨tx⟩ := tensorModel_exists d.R
  obtain ⟨tu⟩ := tensorModel_exists (restrictRing m d.j d.R)
  obtain ⟨tx'⟩ := tensorModel_exists d.S
  obtain ⟨tu'⟩ := tensorModel_exists (restrictRing m d.j' d.S)
  obtain ⟨o, _⟩ := normalizedOperations_exists d t tx tu tx' tu'
    (normalizedRightSquare t) (normalizedRightSquare_sections t)
  exact ⟨t, o, ⟨assertionOfSupported o
    (derivedPullback_openSupported o) (derivedTensor_openSupported o)⟩⟩

/-- Finite specialization of the normalized theorem.
Proof: extend each fixed-scalar action along the constant-presheaf sheafification
unit; locally constant sections define the ring-sheaf action uniquely. This gives
the four section-preserving equivalences. The direct-image comparison keeps
sections, so its adjunction mate gives the ordinary pullback comparisons.
Open restriction keeps the same sections and its mate gives the extension
comparisons. Apply these exact comparisons degreewise; the pullback universal
property fixes their derived factorizations. Tensor comparison sends each pure
summand to the same two sections; signed totalization and K-flat descent give
its derived comparison. Finally the published beta is the mate of the same
right-adjoint square, and the published inverse projection map has the same
open-unit transpose as gamma inverse. Uniqueness in these adjunction Hom
bijections proves the two finite route equalities. Source: Stacks 03S6 and 0GL1
(blueprint: lem-sf-open-tensor-normalization). -/
theorem finite_compatibility (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g) :
    ∃ (t : SiteSquare (finiteInput A gU j' j g sq))
      (o : Operations (finiteInput A gU j' j g sq) t) (a : Assertion o)
      (e : FiniteComparisons A o), FiniteCompatibility A o a e := by
  obtain ⟨t, o, ⟨a⟩⟩ := exists_normalized .ordinary (finiteInput A gU j' j g sq)
  obtain ⟨e⟩ := finite_comparisons_exists A gU j' j g sq o
  exact ⟨t, o, a, e, finite_compatibility_of_comparisons A gU j' j g sq o a e⟩

end SheafOfModules.OpenTensorNormalization

namespace SheafOfModules
open OpenTensorNormalization

/-- Open-unit, base-change and tensor normalization, including arbitrary strict
ring systems and equality with both recorded finite maps.
Proof: `exists_normalized` carries out the same localized-site, section-unit,
K-flat totalization and adjunct construction in the ordinary and vertical
diagram sites; `finite_compatibility` identifies the constant finite
specialization by the uniqueness of those adjuncts. See the full proof plans
above. Source: Stacks 0F6Z, 0E8I, 0GL1, 03S6, 07A4
(blueprint: lem-sf-open-tensor-normalization). -/
theorem openTensorNormalization :
    (∀ (d : Input.{u} .ordinary),
      ∃ (t : SiteSquare d) (o : Operations d t), Nonempty (Assertion o)) ∧
    (∀ (d : Input.{u} .systems),
      ∃ (t : SiteSquare d) (o : Operations d t), Nonempty (Assertion o)) ∧
    (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
      {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
      (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g),
      ∃ (t : SiteSquare (finiteInput A gU j' j g sq))
        (o : Operations (finiteInput A gU j' j g sq) t) (a : Assertion o)
        (e : FiniteComparisons A o), FiniteCompatibility A o a e) := by
  refine ⟨exists_normalized .ordinary, exists_normalized .systems, ?_⟩
  intro A _ _ U' U X' X gU j' j g sq
  exact finite_compatibility A gU j' j g sq

end SheafOfModules
