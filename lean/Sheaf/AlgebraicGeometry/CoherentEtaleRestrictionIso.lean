module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Canonical restriction of coherent tensor-section sheaves

Source: Stacks Project, Tags 03DR and 03DU; Tag 03Q8 coefficient restriction.
(blueprint: def-weil-pbc-coherent-etale-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TopologicalSpace

private def restrictionCompOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    L b ⋙ L a ≅ L (a ≫ b) :=
  (conjugateIsoEquiv (adj (a ≫ b)) ((adj b).comp (adj a))).symm
    (pushforwardComp a b).symm

private theorem compOfAdjunction_assoc
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    ((restrictionCompOfAdjunction L adj a b).hom.app ((L c).obj F)) ≫
      (restrictionCompOfAdjunction L adj (a ≫ b) c).hom.app F ≫
      eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c)) =
    (L a).map ((restrictionCompOfAdjunction L adj b c).hom.app F) ≫
      (restrictionCompOfAdjunction L adj a (b ≫ c)).hom.app F := by
  have he : Functor.isoWhiskerLeft (pushforward a) (pushforwardComp b c) ≪≫
      pushforwardComp a (b ≫ c) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComp a b) (pushforward c) ≪≫
        pushforwardComp (a ≫ b) c := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (adj c) (adj b) (adj a)
    (adj (b ≫ c)) (adj (a ≫ b)) (adj (a ≫ (b ≫ c)))
    (pushforwardComp b c) (pushforwardComp a b)
    (pushforwardComp (a ≫ b) c) (pushforwardComp a (b ≫ c)) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app] at hc
  erw [Category.id_comp] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

private theorem restrictionUnit_naturality {A B : Scheme.{u}} (a : A ⟶ B)
    {F G : B.Modules} (φ : F ⟶ G) :
    tensorSectionsUnit a F ≫ ((tensorPullback a).map φ).app ⊤ =
      φ.app ⊤ ≫ tensorSectionsUnit a G := by
  have hn := congrArg (fun ψ ↦ ψ.app ⊤)
    ((Classical.choose (exists_tensorPullbackAdjunction a)).unit.naturality φ)
  have hi : (homOfLE a.preimage_top.ge).op =
      𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) := rfl
  unfold tensorSectionsUnit
  erw [hi, ((tensorPullback a).obj F).presheaf.map_id,
    ((tensorPullback a).obj G).presheaf.map_id, Category.comp_id, Category.comp_id]
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app] at hn
  exact hn.symm

private theorem restrictionComparison_naturality
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (h : a ≫ b = d) (j : C ⟶ D) (F : D.Modules) :
    (tensorSectionsUnit a ((tensorPullback b).obj ((tensorPullback j).obj F)) ≫
      ((tensorSectionsComp a b).hom.app ((tensorPullback j).obj F)).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj
        ((tensorPullback j).obj F)) h)).app ⊤) ≫
        ((tensorSectionsComp d j).hom.app F).app ⊤ =
      ((tensorSectionsComp b j).hom.app F).app ⊤ ≫
        (tensorSectionsUnit a ((tensorPullback (b ≫ j)).obj F) ≫
          ((tensorSectionsComp a (b ≫ j)).hom.app F).app ⊤ ≫
          (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F)
            (show a ≫ (b ≫ j) = d ≫ j by rw [← Category.assoc, h]))).app ⊤) := by
  subst d
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  have hc := congrArg (fun φ ↦ φ.app ⊤)
    (compOfAdjunction_assoc (fun f ↦ tensorPullback f)
      (fun f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b j F)
  change ((tensorSectionsComp a b).hom.app ((tensorPullback j).obj F)).app ⊤ ≫
      ((tensorSectionsComp (a ≫ b) j).hom.app F).app ⊤ ≫ 𝟙 _ =
    ((tensorPullback a).map ((tensorSectionsComp b j).hom.app F)).app ⊤ ≫
      ((tensorSectionsComp a (b ≫ j)).hom.app F).app ⊤ at hc
  rw [Category.comp_id] at hc
  let η := tensorSectionsUnit a ((tensorPullback b).obj ((tensorPullback j).obj F))
  let p := ((tensorSectionsComp a b).hom.app ((tensorPullback j).obj F)).app ⊤
  let q := ((tensorSectionsComp (a ≫ b) j).hom.app F).app ⊤
  let r := ((tensorPullback a).map ((tensorSectionsComp b j).hom.app F)).app ⊤
  let t := ((tensorSectionsComp a (b ≫ j)).hom.app F).app ⊤
  let c := ((tensorSectionsComp b j).hom.app F).app ⊤
  let ν := tensorSectionsUnit a ((tensorPullback (b ≫ j)).obj F)
  calc
    (η ≫ p) ≫ q = η ≫ (p ≫ q) := Category.assoc _ _ _
    _ = η ≫ (r ≫ t) := congrArg (fun z ↦ η ≫ z) hc
    _ = (η ≫ r) ≫ t := (Category.assoc _ _ _).symm
    _ = (c ≫ ν) ≫ t := congrArg (fun z ↦ z ≫ t)
      (restrictionUnit_naturality a ((tensorSectionsComp b j).hom.app F))
    _ = c ≫ ν ≫ t := Category.assoc _ _ _

private def tensorGlobalCompIso {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (F : C.Modules) :
    Γ((tensorPullback a).obj ((tensorPullback b).obj F), ⊤) ≅
      Γ((tensorPullback (a ≫ b)).obj F, ⊤) where
  hom := ((tensorSectionsComp a b).hom.app F).app ⊤
  inv := ((tensorSectionsComp a b).inv.app F).app ⊤
  hom_inv_id := congrArg (fun φ ↦ φ.app ⊤) (Iso.hom_inv_id_app (tensorSectionsComp a b) F)
  inv_hom_id := congrArg (fun φ ↦ φ.app ⊤) (Iso.inv_hom_id_app (tensorSectionsComp a b) F)

/-- The section formula uniquely determines the restriction isomorphism.
Source: Stacks Project, Tags 03DR, 03DU and 03Q8
(blueprint: def-weil-pbc-coherent-etale-restriction).

Proof: inverse image along an etale map is restriction along postcomposition.
At an etale object W the tensor-pullback composition isomorphism gives the
inverse of the displayed component. Its naturality follows from associativity
of the unit-normalized composition comparisons and naturality of section units.
These components therefore define inverse natural transformations. They are
isomorphisms of sheaves since both underlying presheaves are sheaves. Lift every
component and restriction by the same additive ULift functor. Every section is
ULift.up of a section, so the displayed formula also proves uniqueness. -/
theorem existsUnique_coherentEtaleRestrictionIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent]
    [(tensorPullback j).obj F |>.IsQuasicoherent] :
    ∃! e : (Etale.upperStar AddCommGrpCat.{u + 1} j).obj
        (liftedCoherentEtaleSheaf F) ≅
        liftedCoherentEtaleSheaf ((tensorPullback j).obj F),
      ∀ (W : Y.Etale)
        (s : Γ((tensorPullback (W.hom ≫ j)).obj F, ⊤)),
        e.hom.hom.app (op W)
          (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
            inferInstance).inv.app (liftedCoherentEtaleSheaf F)).hom.app (op W)
              (ULift.up s)) =
          ULift.up (((tensorSectionsComp W.hom j).inv.app F).app ⊤ s) := by
  classical
  let ρ := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
    inferInstance).app (liftedCoherentEtaleSheaf F)
  let c : liftedCoherentEtaleSheaf ((tensorPullback j).obj F) ≅
      (Etale.localizationRestriction AddCommGrpCat.{u + 1} j inferInstance).obj
        (liftedCoherentEtaleSheaf F) :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun W ↦
        AddCommGrpCat.uliftFunctor.mapIso (tensorGlobalCompIso W.unop.hom j F)) (by
        intro U V g
        change AddCommGrpCat.uliftFunctor.map
            (etaleTensorSectionsRestriction ((tensorPullback j).obj F) g.unop) ≫
            AddCommGrpCat.uliftFunctor.map
              (((tensorSectionsComp V.unop.hom j).hom.app F).app ⊤) = _
        let h := restrictionComparison_naturality g.unop.left U.unop.hom V.unop.hom
          g.unop.w j F
        exact (AddCommGrpCat.uliftFunctor.map_comp _ _).symm.trans
          ((congrArg AddCommGrpCat.uliftFunctor.map h).trans
            (AddCommGrpCat.uliftFunctor.map_comp _ _))))
  have hn (W : Y.Etale) (s : Γ((tensorPullback (W.hom ≫ j)).obj F, ⊤)) :
      (ρ ≪≫ c.symm).hom.hom.app (op W)
        (ρ.inv.hom.app (op W) (ULift.up s)) =
        ULift.up (((tensorSectionsComp W.hom j).inv.app F).app ⊤ s) := by
    have h := congrArg (fun φ ↦ φ.hom.app (op W) (ULift.up s)) ρ.inv_hom_id
    change ρ.hom.hom.app (op W) (ρ.inv.hom.app (op W) (ULift.up s)) = ULift.up s at h
    change c.inv.hom.app (op W)
      (ρ.hom.hom.app (op W) (ρ.inv.hom.app (op W) (ULift.up s))) = _
    rw [h]
    rfl
  refine ⟨ρ ≪≫ c.symm, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_epi ρ.inv).mp
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨s⟩ := s
  exact (he W.unop s).trans (hn W.unop s).symm

/-- Restriction with its actual tensor-composition section normalization.
Only a uniquely specified isomorphism is selected.
Source: Stacks Project, Tags 03DR, 03DU and 03Q8
(blueprint: def-weil-pbc-coherent-etale-restriction). -/
def coherentEtaleRestrictionIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent]
    [(tensorPullback j).obj F |>.IsQuasicoherent] :
    (Etale.upperStar AddCommGrpCat.{u + 1} j).obj (liftedCoherentEtaleSheaf F) ≅
      liftedCoherentEtaleSheaf ((tensorPullback j).obj F) :=
  Classical.choose (existsUnique_coherentEtaleRestrictionIso j F)

end
end AlgebraicGeometry.Scheme.Modules
