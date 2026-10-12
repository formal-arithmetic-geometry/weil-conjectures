/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTransport
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# Restriction of `𝔾ₘ`, `μₙ`, the Kummer sequence and line bundles along an étale monomorphism

Let `f : X ⟶ Y` be an étale monomorphism, for instance an isomorphism, and `R` the restriction
of étale sheaves along `f` (`AlgebraicGeometry.Scheme.etaleRestriction`). Then `R 𝔾ₘ = 𝔾ₘ`
(definitionally), `R μₙ ≅ μₙ` (`AlgebraicGeometry.Scheme.rootsOfUnityRestrictionIso`), and the
induced maps on cohomology `H^q(Y, -) ⟶ H^q(X, -)` commute with the Kummer maps
(`AlgebraicGeometry.Scheme.kummerδ₁_etaleRestrictionH`) and with the identification
`Pic = H¹(-, 𝔾ₘ)`, under which they are the pullback of line bundles
(`AlgebraicGeometry.Scheme.etaleRestrictionH_toCohomologicalPicardGroup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

lemma etaleRestriction_obj_gmSheaf : (etaleRestriction f).obj Y.gmSheaf = X.gmSheaf :=
  rfl

variable [Mono f]

/-- The restriction of `μₙ` is `μₙ`. -/
noncomputable def rootsOfUnityRestrictionIso (n : ℕ) :
    (etaleRestriction f).obj (Y.rootsOfUnitySheaf n) ≅ X.rootsOfUnitySheaf n :=
  PreservesKernel.iso (etaleRestriction f) (n • 𝟙 Y.gmSheaf) ≪≫
    kernelIsoOfEq (by rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]; rfl)

@[reassoc (attr := simp)]
lemma rootsOfUnityRestrictionIso_hom_ι (n : ℕ) :
    (rootsOfUnityRestrictionIso f n).hom ≫ kernel.ι (n • 𝟙 X.gmSheaf) =
      (etaleRestriction f).map (kernel.ι (n • 𝟙 Y.gmSheaf)) := by
  rw [rootsOfUnityRestrictionIso, Iso.trans_hom, Category.assoc, kernelIsoOfEq_hom_comp_ι,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The morphism from the restriction of the Kummer sequence of `Y` to that of `X`. -/
noncomputable def kummerSequenceRestriction (n : ℕ) :
    (Y.kummerSequence n).map (etaleRestriction f) ⟶ X.kummerSequence n where
  τ₁ := (rootsOfUnityRestrictionIso f n).hom
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by
    change _ ≫ kernel.ι _ = (etaleRestriction f).map (kernel.ι _) ≫ 𝟙 _
    rw [Category.comp_id, rootsOfUnityRestrictionIso_hom_ι]
  comm₂₃ := by
    change 𝟙 _ ≫ (n • 𝟙 _) = (etaleRestriction f).map (n • 𝟙 _) ≫ 𝟙 _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme

/-! ### Restriction of the torsor `Isom(𝒪, L)` -/

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The identification `f^* 𝒪_Y ≅ 𝒪_X`, in `modulesPseudofunctor`. -/
noncomputable def unitRestrictIso :
    (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj (unitObj Y) ≅ unitObj X :=
  pullbackObjUnitIso f

/-- For `T` over `X`, a morphism `(T ⟶ X ⟶ Y)^* 𝒪_Y ⟶ (T ⟶ X ⟶ Y)^* M` gives a morphism
`T^* 𝒪_X ⟶ T^* (f^* M)`, through the identification `f^* 𝒪_Y ≅ 𝒪_X`. -/
noncomputable def presheafHomRestrict (M : modulesPseudofunctor.obj (.mk (op Y))) (T : Over X)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj (op ((Over.map f).obj T))) :
    (modulesPseudofunctor.presheafHom (unitObj X)
      ((modulesPseudofunctor.map f.op.toLoc).toFunctor.obj M)).obj (op T) :=
  (modulesPseudofunctor.map T.hom.op.toLoc).toFunctor.map (unitRestrictIso f).inv ≫
    (Pseudofunctor.overMapCompPresheafHomIso modulesPseudofunctor (unitObj Y) M f).hom.app
      (op T) x

lemma presheafHomRestrict_eq (M : modulesPseudofunctor.obj (.mk (op Y))) (T : Over X)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj (op ((Over.map f).obj T))) :
    presheafHomRestrict f M T x =
      (modulesPseudofunctor.map T.hom.op.toLoc).toFunctor.map (unitRestrictIso f).inv ≫
      (modulesPseudofunctor.mapComp' f.op.toLoc T.hom.op.toLoc
        (T.hom ≫ f).op.toLoc (by simp)).inv.toNatTrans.app (unitObj Y) ≫ x ≫
      (modulesPseudofunctor.mapComp' f.op.toLoc T.hom.op.toLoc
        (T.hom ≫ f).op.toLoc (by simp)).hom.toNatTrans.app M :=
  rfl

instance isIso_presheafHomRestrict (M : modulesPseudofunctor.obj (.mk (op Y))) (T : Over X)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj (op ((Over.map f).obj T)))
    [IsIso x] : IsIso (presheafHomRestrict f M T x) := by
  rw [presheafHomRestrict_eq]
  infer_instance

set_option maxHeartbeats 1000000 in
-- the defeq checks through the pseudofunctor of modules are slow
lemma presheafHomRestrict_naturality (M : modulesPseudofunctor.obj (.mk (op Y))) {T T' : Over X}
    (g : T' ⟶ T)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj (op ((Over.map f).obj T))) :
    presheafHomRestrict f M T'
        ((modulesPseudofunctor.presheafHom (unitObj Y) M).map ((Over.map f).map g).op x) =
      (modulesPseudofunctor.presheafHom (unitObj X) _).map g.op (presheafHomRestrict f M T x) := by
  have h := ConcreteCategory.congr_hom
    ((Pseudofunctor.overMapCompPresheafHomIso modulesPseudofunctor (unitObj Y) M
      f).hom.naturality g.op) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Functor.comp_map, Functor.op_map,
    Quiver.Hom.unop_op] at h
  rw [presheafHomRestrict, presheafHomRestrict, Pseudofunctor.presheafHom_map_comp]
  refine congrArg₂ (fun a b ↦ a ≫ b) ?_ ?_
  · exact (pullHom_map _ _ _ _ (Over.w g)).symm
  · exact h

lemma presheafHomRestrict_smulMor (M : modulesPseudofunctor.obj (.mk (op Y))) (T : Over X)
    (x : (modulesPseudofunctor.presheafHom (unitObj Y) M).obj (op ((Over.map f).obj T)))
    (a : Γ(T.left, ⊤)) :
    presheafHomRestrict f M T (smulMor _ a ≫ x) = smulMor _ a ≫ presheafHomRestrict f M T x := by
  rw [presheafHomRestrict_eq, presheafHomRestrict_eq]
  conv_rhs => rw [← Category.assoc, smulMor_naturality, Category.assoc,
    ← Category.assoc (smulMor _ a), smulMor_naturality, Category.assoc]
  simp only [Category.assoc]
  rfl

variable [Etale f]

set_option maxHeartbeats 1000000 in
-- the defeq checks through the small étale and pro-étale sites are slow
/-- **Restriction of `Isom(𝒪, M)`.** The restriction along an étale `f : X ⟶ Y` of the
`𝔾ₘ`-torsor `Isom(𝒪_Y, M)` is the torsor `Isom(𝒪_X, f^* M)`. -/
lemma etaleIsoTorsor_restrict_equiv (M : modulesPseudofunctor.obj (.mk (op Y)))
    [SheafOfModules.IsInvertible.{u, u, u} (M : Y.Modules)]
    [SheafOfModules.IsInvertible.{u, u, u}
      ((modulesPseudofunctor.map f.op.toLoc).toFunctor.obj M : X.Modules)] :
    (etaleIsoTorsor M).restrict f ≈
      etaleIsoTorsor ((modulesPseudofunctor.map f.op.toLoc).toFunctor.obj M) := by
  let G := toProEt X ⋙ ProEt.forget X
  let ψ (U : X.Etaleᵒᵖ) (x : ((etaleIsoTorsor M).restrict f).sheaf.obj.obj U) :
      (etaleIsoTorsor ((modulesPseudofunctor.map f.op.toLoc).toFunctor.obj M)).sheaf.obj.obj U :=
    haveI : IsIso x.down.1 := x.down.2
    etaleIsoTorsorMk _ (presheafHomRestrict f M (G.obj U.unop) x.down.1) inferInstance
  refine ⟨Sheaf.Torsor.Iso.ofHom ⟨{
      app U := TypeCat.ofHom (ψ U)
      naturality U V g := ?_ }⟩ fun U a x ↦ ?_⟩
  · ext x
    apply ULift.ext
    apply Subtype.ext
    change presheafHomRestrict f M (G.obj V.unop)
        ((modulesPseudofunctor.presheafHom (unitObj Y) M).map ((Over.map f).map
          (G.map g.unop)).op x.down.1) =
      (modulesPseudofunctor.presheafHom (unitObj X) _).map (G.map g.unop).op
        (presheafHomRestrict f M (G.obj U.unop) x.down.1)
    exact presheafHomRestrict_naturality f M (G.map g.unop) _
  · apply ULift.ext
    apply Subtype.ext
    change presheafHomRestrict f M (G.obj U.unop) (smulMor _ _ ≫ x.down.1) =
      smulMor _ _ ≫ presheafHomRestrict f M (G.obj U.unop) x.down.1
    exact presheafHomRestrict_smulMor f M _ _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [Mono f]

/-- **Restriction of line bundles.** Under the identification `Pic = H¹(-, 𝔾ₘ)`, the restriction
map `H¹(Y, 𝔾ₘ) ⟶ H¹(X, R 𝔾ₘ) = H¹(X, 𝔾ₘ)` along an étale monomorphism `f` is the pullback of
line bundles along `f`. -/
theorem etaleRestrictionH_toCohomologicalPicardGroup (L : Y.Pic) :
    etaleRestrictionH f Y.gmSheaf 1 (Pic.toCohomologicalPicardGroup Y L) =
      Pic.toCohomologicalPicardGroup X (Pic.map f L) := by
  have := Pic.isInvertible L
  have : SheafOfModules.IsInvertible.{u, u, u}
      ((Modules.pullback f).obj ((fromSkeleton Y.Modules).obj L.val)) :=
    SheafOfModules.IsInvertible.pullback this
  have hL : Pic.map f L =
      Pic.mk ((Modules.pullback f).obj ((fromSkeleton Y.Modules).obj L.val)) :=
    Pic.ext rfl
  rw [Pic.toCohomologicalPicardGroup_apply, Pic.toCohomologicalPicardGroup_apply, hL,
    Pic.etaleTorsorClass_mk]
  exact (classH1_etaleRestriction f _).symm.trans
    (congrArg _ (Quotient.sound (Modules.etaleIsoTorsor_restrict_equiv f _)))

end AlgebraicGeometry.Scheme
