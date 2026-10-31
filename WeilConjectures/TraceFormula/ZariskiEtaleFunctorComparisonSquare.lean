/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ZariskiEtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import WeilConjectures.AlgebraicGeometry.EtaleExtensionFreePresentationsHom
import WeilConjectures.TraceFormula.ZariskiEtaleRightAdjointSquare
import WeilConjectures.TraceFormula.ZariskiEtalePushforwardSectionFormula
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsLift
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionDegreeZero
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionIso

/-!
# Zariski and small étale functor comparison square

Source: Stacks Project, `descent.tex`, Tags 03FH and 03LC
(blueprint: lem-trf-zariski-etale-functor-comparison-square).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem etale_moduleBaseChangeMap_isIso
    {U T : Scheme.{u}} (a : U ⟶ T) [QuasiCompact a] [IsSeparated a]
    (H : U.Modules) [H.IsQuasicoherent] (V : T.Etale) :
    IsIso (moduleBaseChangeMap a (pullback.fst V.hom a) V.hom
      (pullback.snd V.hom a) pullback.condition.symm H) := by
  classical
  have := enoughInjectives (X := U)
  have := enoughInjectives (X := Limits.pullback V.hom a)
  let I := injectiveResolution H
  let J := injectiveResolution ((tensorPullback (pullback.snd V.hom a)).obj H)
  obtain ⟨t, ht⟩ := flatBaseChangeResolutionLift a V.hom I J
  have hi := flatBaseChangeResolutionBeta_isIso a V.hom H I J t ht 0
  have he := flatBaseChangeResolutionBeta_degree_zero a V.hom H I J t ht
  have hcomp : IsIso
      (moduleBaseChangeMap a (pullback.fst V.hom a) V.hom (pullback.snd V.hom a)
          pullback.condition.symm H ≫
        (pushforward (pullback.fst V.hom a)).toRightDerivedZero.app
          ((tensorPullback (pullback.snd V.hom a)).obj H)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((pushforward (pullback.fst V.hom a)).toRightDerivedZero.app
      ((tensorPullback (pullback.snd V.hom a)).obj H))

private theorem pushforwardComparison_naturality
    {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅ cU.restriction ⋙ pushforward a)
    {H K : U.Modules} (h : H ⟶ K) :
    cT.extension.map ((pushforward a).map h) ≫
        zariskiEtalePushforwardComparison a cU cT hp r K =
      zariskiEtalePushforwardComparison a cU cT hp r H ≫
        (smallEtaleModulePushforward a).map (cU.extension.map h) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction a)
  let p := zariskiEtalePullbackComparison a cU cT hp r
  let t : pushforward a ⋙ cT.extension ⟶
      pushforward a ⋙ cT.extension ⋙ smallEtaleModulePullback a hp ⋙
        smallEtaleModulePushforward a :=
    Functor.whiskerLeft (pushforward a ⋙ cT.extension)
      (smallEtaleModuleAdjunction a hp).unit
  let q : pushforward a ⋙ cT.extension ⋙ smallEtaleModulePullback a hp ⟶
      cU.extension :=
    Functor.whiskerLeft (pushforward a) p.inv ≫ Functor.whiskerRight adj.counit cU.extension
  exact (t ≫ Functor.whiskerRight q (smallEtaleModulePushforward a)).naturality h

private theorem pushforwardComparison_unit
    {U T : Scheme.{u}} (a : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
    (r : smallEtaleModulePushforward a ⋙ cT.restriction ≅ cU.restriction ⋙ pushforward a)
    (H : U.Modules) :
    cT.adjunction.unit.app ((pushforward a).obj H) ≫
        cT.restriction.map (zariskiEtalePushforwardComparison a cU cT hp r H) ≫
        r.hom.app (cU.extension.obj H) =
      (pushforward a).map (cU.adjunction.unit.app H) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction a)
  let p := zariskiEtalePullbackComparison a cU cT hp r
  have key := unit_conjugateEquiv_symm (adj.comp cU.adjunction)
    (cT.adjunction.comp (smallEtaleModuleAdjunction a hp)) r.inv
    ((pushforward a).obj H)
  change (adj.comp cU.adjunction).unit.app _ ≫ r.inv.app _ =
    (cT.adjunction.comp (smallEtaleModuleAdjunction a hp)).unit.app _ ≫
      (smallEtaleModulePushforward a ⋙ cT.restriction).map (p.inv.app _) at key
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Functor.comp_map] at key
  unfold zariskiEtalePushforwardComparison
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% key]
  have hn := r.inv.naturality (cU.extension.map (adj.counit.app H))
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have hη := cU.adjunction.unit_naturality (adj.counit.app H)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hη
  rw [← (pushforward a).map_comp, hη, (pushforward a).map_comp]
  rw [← Category.assoc, adj.right_triangle_components, Category.id_comp]

/-- The Zariski-to-small-étale tensor/direct-image square is canonically normalized.

Source: Stacks Project, `descent.tex`, Tags 03FH and 03LC
(blueprint: lem-trf-zariski-etale-functor-comparison-square).

The section coordinates `e` are linear, natural in the module, and normalized by
the tensor-extension unit on opens. The isomorphism `r` is the direct-image square;
its component on an open is restriction along the canonical preimage-open
identification, hence identity in the prescribed coordinates. The pullback
comparison is its adjoint mate, with no quasi-coherence hypothesis. Under the
stated quasi-compactness and separatedness assumptions, `hqc` records
quasi-coherence of the Zariski direct image. The base-change map is the existing
canonical `moduleBaseChangeMap`. The displayed section equation identifies its
components with those of the canonical small-etale comparison. As these are
sheaf morphisms, the equation includes naturality in every test-object map.
The last two equations record module naturality and identity on open sections.

Proof, following the seven DAG steps:
1. Compute the chart limit of def-trf-space-etale-module-functors: the fibre
   product scheme is terminal among charts over an etale test scheme. The
   limit projection identifies compatible families with their section on that
   fibre product, including scalars and restrictions. On opens this gives `r`.
2. Compose the tensor-extension and scheme-pullback adjunctions and the etale
   module adjunctions. The conjugate-iso unit equation gives their normalized
   left-adjoint comparison. This uses all modules, without quasi-coherence.
3. The quasi-compact atlas condition implies scheme quasi-compactness; the closed
   diagonal implies quasi-separatedness. Apply pqf-lem-pushforward-qcoh. Etale
   flatness and flat base change in degree zero make `moduleBaseChangeMap`
   invertible. One can work locally on affine opens of the etale test scheme.
4. The degree-zero adjoint section formula of
   lem-weil-pbc-flat-base-change-map-sections sends a local tensor b tensor s
   to a_V-sharp(b) times v'-pullback(s). This proves naturality in the module.
5. For a map of etale test schemes, both restriction composites have this same
   formula on tensor generators, using the normalized pullback composition.
   Sheafification extends the equality to all sections; the test-object map
   itself needs no flatness or separatedness assumption.
6. Apply lem-trf-etale-extension-free-presentations-hom to H and its direct
   image to obtain `e`. The chart computation of step 1 identifies the target
   sections. Steps 4 and 5 assemble the section maps into the displayed sheaf
   comparison. Its components are invertible by step 3.
7. For an open test scheme, tensor pullback is restriction with the specified
   unit by lem-weil-pbc-open-immersion-module-pullback-restriction. Thus the map
   is 1 tensor s mapped to s, exactly the identity in open-section coordinates.
   The unit normalization of `e` gives the final equation. -/
theorem zariski_etale_functor_comparison_square :
    ∃ c : ∀ T : Scheme.{u}, ZariskiEtaleModuleContext T,
      ∃ e : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
          (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj ((c T).extension.obj F) ≅
            etaleTensorSectionsSheaf F,
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent]
            (V : T.Etale) (b : Γ(V.left, ⊤))
            (s : ((c T).extension.obj F).val.obj (op V)),
          (e T F).hom.hom.app (op V) (b • s) =
            b • (@id (Γ((tensorPullback V.hom).obj F, ⊤))
              ((e T F).hom.hom.app (op V) s))) ∧
        (∀ (T : Scheme.{u}) (F K : T.Modules) [F.IsQuasicoherent] [K.IsQuasicoherent]
            (h : F ⟶ K) (V : T.Etale),
          ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
            ((c T).extension.map h)).hom.app (op V) ≫ (e T K).hom.hom.app (op V) =
              (e T F).hom.hom.app (op V) ≫ ((tensorPullback V.hom).map h).app ⊤) ∧
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent] (W : T.Opens),
          ((c T).adjunction.unit.app F).app W ≫
              (e T F).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
                (tensorOpenSectionIso T F W).hom = 𝟙 _) ∧
        ∀ (U T : Scheme.{u}) (a : U ⟶ T),
          ∃ (hp : (smallEtaleModulePushforward a).IsRightAdjoint)
            (r : smallEtaleModulePushforward a ⋙ (c T).restriction ≅
              (c U).restriction ⋙ pushforward a),
            (∀ (G : SmallEtaleModules U) (W : T.Opens),
              (r.hom.app G).app W =
                G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso a W).hom.op) ∧
            (∀ (M : T.Modules),
              IsIso ((zariskiEtalePullbackComparison a (c U) (c T) hp r).hom.app M)) ∧
            ∀ (_ : QuasiCompact a) (_ : IsSeparated a),
              (∀ (H : U.Modules) [H.IsQuasicoherent],
                ∃ hqc : ((pushforward a).obj H).IsQuasicoherent,
                  IsIso (zariskiEtalePushforwardComparison a (c U) (c T) hp r H) ∧
                  ∀ V : T.Etale,
                    IsIso (moduleBaseChangeMap a (pullback.fst V.hom a) V.hom
                      (pullback.snd V.hom a) pullback.condition.symm H) ∧
                    (@e T ((pushforward a).obj H) hqc).inv.hom.app (op V) ≫
                        ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
                          (zariskiEtalePushforwardComparison a (c U) (c T) hp r H)).hom.app
                            (op V) ≫
                        (e U H).hom.hom.app (op (a.Etale.obj V)) =
                      (moduleBaseChangeMap a (pullback.fst V.hom a) V.hom
                        (pullback.snd V.hom a) pullback.condition.symm H).app ⊤) ∧
              (∀ (H K : U.Modules) [H.IsQuasicoherent] [K.IsQuasicoherent] (h : H ⟶ K),
                (c T).extension.map ((pushforward a).map h) ≫
                    zariskiEtalePushforwardComparison a (c U) (c T) hp r K =
                  zariskiEtalePushforwardComparison a (c U) (c T) hp r H ≫
                    (smallEtaleModulePushforward a).map ((c U).extension.map h)) ∧
              ∀ (H : U.Modules) [H.IsQuasicoherent],
                (c T).adjunction.unit.app ((pushforward a).obj H) ≫
                    (c T).restriction.map
                      (zariskiEtalePushforwardComparison a (c U) (c T) hp r H) ≫
                    r.hom.app ((c U).extension.obj H) =
                  (pushforward a).map ((c U).adjunction.unit.app H) := by
  classical
  obtain ⟨c, _, _, _, _, e, hlinear, hnatural, hopen, _⟩ :=
    etaleExtension_free_presentations_hom.{u, u, u}
  refine ⟨c, e, hlinear, hnatural, hopen, ?_⟩
  intro U T a
  obtain ⟨hp, r, hr⟩ := zariskiEtale_rightAdjoint_square a (c U) (c T)
  refine ⟨hp, r, hr, fun M ↦ inferInstance, ?_⟩
  intro hqc hsep
  refine ⟨?_, fun H K _ _ h ↦ pushforwardComparison_naturality a (c U) (c T) hp r h,
    fun H _ ↦ pushforwardComparison_unit a (c U) (c T) hp r H⟩
  intro H hH
  have hpush := isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated a H
  have hformula := zariskiEtale_pushforward_section_formula c e hlinear hnatural hopen
    a hp r hr H
  refine ⟨hpush, ?_, fun V ↦ ⟨etale_moduleBaseChangeMap_isIso a H V, hformula V⟩⟩
  let f := zariskiEtalePushforwardComparison a (c U) (c T) hp r H
  have hcomponents : ∀ V : T.Etale,
      IsIso (((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map f).hom.app (op V)) := by
    intro V
    have := etale_moduleBaseChangeMap_isIso a H V
    have : IsIso ((moduleBaseChangeMap a (pullback.fst V.hom a) V.hom
        (pullback.snd V.hom a) pullback.condition.symm H).app ⊤) := inferInstance
    have hcomp : IsIso ((e T ((pushforward a).obj H)).inv.hom.app (op V) ≫
        ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map f).hom.app (op V) ≫
          (e U H).hom.hom.app (op (a.Etale.obj V))) := by
      rw [hformula V]
      infer_instance
    have : IsIso
        (((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map f).hom.app (op V) ≫
          (e U H).hom.hom.app (op (a.Etale.obj V))) :=
      IsIso.of_isIso_comp_left
        ((e T ((pushforward a).obj H)).inv.hom.app (op V)) _
    exact IsIso.of_isIso_comp_right _ ((e U H).hom.hom.app (op (a.Etale.obj V)))
  have : ∀ V, IsIso
      ((((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map f).hom).app V) :=
    fun V ↦ hcomponents V.unop
  have hpresheaf : IsIso (((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map f).hom) :=
    NatIso.isIso_of_isIso_app _
  have hsheaf : IsIso ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map f) :=
    (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).mp hpresheaf
  exact (isIso_iff_of_reflects_iso f (SheafOfModules.toSheaf _)).mp hsheaf

end AlgebraicGeometry.Scheme.Modules
