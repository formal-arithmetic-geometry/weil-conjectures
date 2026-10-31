/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineChartDerivation

/-!
# Normalized affine transitivity comparisons and stalk right exactness

Source: Stacks Project, Morphisms, Tag 01UX (`lemma-triangle-differentials`),
affine description Tag 01UT and functoriality Tag 01UV; localized exactness Tag 00CS.
(blueprint: lem-a1-differential-transitivity-affine-stalk)

The proof first identifies the supplied quotient map as a cokernel using universal
relative derivations and the tensor-pullback adjunction. Exactness of the module
stalk functor gives stalk exactness and surjectivity. Independently, uniqueness of
left adjoints, the affine-chart unit formula and `tildePullbackIso` construct the
normalized affine comparison. The algebraic Kähler first exact sequence gives the
affine maps, exactness and surjectivity. The tilde and extension-of-scalars
adjunctions identify both sheaf arrows on differential generators. No sheaf
transitivity theorem is used.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry
private theorem tilde_differential_ext {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {F : (Spec A).Modules} {a b : tilde (CommRingCat.KaehlerDifferential φ) ⟶ F}
    (hab : ∀ x : A, a.app ⊤ (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
        (CommRingCat.KaehlerDifferential.d x)) =
      b.app ⊤ (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
        (CommRingCat.KaehlerDifferential.d x))) : a = b := by
  apply (tilde.adjunction.homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  simp only [Adjunction.homEquiv_unit]
  exact hab x

private theorem tilde_extend_differential_ext {R B A : CommRingCat.{u}}
    (φ : R ⟶ B) (ψ : B ⟶ A) {F : (Spec A).Modules}
    {a b : tilde ((ModuleCat.extendScalars ψ.hom).obj
      (CommRingCat.KaehlerDifferential φ)) ⟶ F}
    (hab : ∀ x : B, a.app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars ψ.hom).obj
        (CommRingCat.KaehlerDifferential φ)) ⊤
          ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
            (CommRingCat.KaehlerDifferential φ) (CommRingCat.KaehlerDifferential.d x))) =
      b.app ⊤ (tilde.toOpen ((ModuleCat.extendScalars ψ.hom).obj
        (CommRingCat.KaehlerDifferential φ)) ⊤
          ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
            (CommRingCat.KaehlerDifferential φ) (CommRingCat.KaehlerDifferential.d x)))) :
    a = b := by
  apply (tilde.adjunction.homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj ψ.hom).homEquiv _ _).injective
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  simp only [Adjunction.homEquiv_unit]
  exact hab x

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

private theorem tensorDifferentials_hom_ext {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S) {F : X.Modules}
    {a b : (Modules.tensorPullback h).obj g.relativeDifferentials ⟶ F}
    (hab : ∀ V s, a.app (h ⁻¹ᵁ V) (g.relativeDifferentialsPullbackGenerator h V s) =
      b.app (h ⁻¹ᵁ V) (g.relativeDifferentialsPullbackGenerator h V s)) : a = b := by
  obtain ⟨adj, hadj⟩ := Modules.exists_tensorPullbackAdjunction h
  apply (adj.homEquiv g.relativeDifferentials F).injective
  apply (g.relativeDifferentialsHomEquiv _).injective
  ext V s
  simp only [relativeDifferentialsHomEquiv_apply, PresheafOfModules.Derivation.postcomp_d_apply]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.app (h ⁻¹ᵁ V.unop)
      ((adj.unit.app g.relativeDifferentials).val.app V
        (g.relativeDifferentialsDerivation.d s)) =
    b.app (h ⁻¹ᵁ V.unop)
      ((adj.unit.app g.relativeDifferentials).val.app V
        (g.relativeDifferentialsDerivation.d s))
  rw [hadj]
  exact hab V.unop s

private theorem quotient_epi {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ O a, q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
      h.relativeDifferentialsDerivation.d (X := op O) a) : Epi q := by
  constructor
  intro F a b hab
  apply (h.relativeDifferentialsHomEquiv _).injective
  ext O s
  change a.app O.unop (h.relativeDifferentialsDerivation.d s) =
    b.app O.unop (h.relativeDifferentialsDerivation.d s)
  have hh := congrArg (fun t ↦ t.app O.unop
    ((h ≫ g).relativeDifferentialsDerivation.d s)) hab
  change a.app O.unop (q.app O.unop _) = b.app O.unop (q.app O.unop _) at hh
  rwa [hq] at hh

private theorem quotient_zero {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ O a, q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
      h.relativeDifferentialsDerivation.d (X := op O) a) :
    g.relativeDifferentialsPullbackMap h ≫ q = 0 := by
  apply tensorDifferentials_hom_ext h g
  intro V a
  change q.app (h ⁻¹ᵁ V) ((g.relativeDifferentialsPullbackMap h).app (h ⁻¹ᵁ V)
    (g.relativeDifferentialsPullbackGenerator h V a)) = 0
  erw [(Classical.choose_spec (existsUnique_relativeDifferentialsPullbackMap g h)).1 V a]
  rw [hq]
  exact h.relativeDifferentialsDerivation.d_app_app V a

private theorem quotient_desc {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ O a, q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
      h.relativeDifferentialsDerivation.d (X := op O) a)
    {F : X.Modules} (a : (h ≫ g).relativeDifferentials ⟶ F)
    (ha : g.relativeDifferentialsPullbackMap h ≫ a = 0) :
    ∃ b : h.relativeDifferentials ⟶ F, q ≫ b = a := by
  let D₀ := (h ≫ g).relativeDifferentialsDerivation.postcomp a.val
  let D : F.val.Derivation' h.pullbackPresheafToPresheaf :=
    h.derivationMk D₀.d D₀.d_mul D₀.d_map (by
      intro V s
      change a.app (h ⁻¹ᵁ V) ((h ≫ g).relativeDifferentialsDerivation.d (h.app V s)) = 0
      have hh := congrArg (fun t ↦ t.app (h ⁻¹ᵁ V)
        (g.relativeDifferentialsPullbackGenerator h V s)) ha
      change a.app (h ⁻¹ᵁ V) ((g.relativeDifferentialsPullbackMap h).app (h ⁻¹ᵁ V)
        (g.relativeDifferentialsPullbackGenerator h V s)) = 0 at hh
      erw [(Classical.choose_spec
        (existsUnique_relativeDifferentialsPullbackMap g h)).1 V s] at hh
      exact hh)
  refine ⟨(h.relativeDifferentialsHomEquiv F).symm D, ?_⟩
  apply ((h ≫ g).relativeDifferentialsHomEquiv F).injective
  ext O s
  change ((h.relativeDifferentialsHomEquiv F).symm D).app O.unop
    (q.app O.unop ((h ≫ g).relativeDifferentialsDerivation.d s)) = a.app O.unop _
  rw [hq]
  exact h.relativeDifferentialsHomEquiv_symm_app_d D s

private noncomputable def quotient_isCokernel {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ O a, q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
      h.relativeDifferentialsDerivation.d (X := op O) a) :
    IsColimit (CokernelCofork.ofπ q (quotient_zero h g q hq)) := by
  have := quotient_epi h g q hq
  apply CokernelCofork.IsColimit.ofπ'
  intro F a ha
  exact ⟨Classical.choose (quotient_desc h g q hq a ha),
    Classical.choose_spec (quotient_desc h g q hq a ha)⟩

private theorem quotient_stalk_exact {X Y S : Scheme.{u}}
    (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ O a, q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
      h.relativeDifferentialsDerivation.d (X := op O) a) (x : X) :
    Function.Exact
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (g.relativeDifferentialsPullbackMap h))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q) ∧
    Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q) := by
  let u := g.relativeDifferentialsPullbackMap h
  let hc := quotient_isCokernel h g q hq
  let e := CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel u) hc (Iso.refl _)
  have he : cokernel.π u ≫ e.hom = q := by
    change cokernel.π u ≫ CokernelCofork.mapOfIsColimit
      (cokernelIsCokernel u) (CokernelCofork.ofπ q _) (𝟙 _) = q
    exact (CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel u)
      (CokernelCofork.ofπ q _) (𝟙 _)).trans (Category.id_comp q)
  let F := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  obtain ⟨hSurj, hExact⟩ :=
    (RingedSpace.module_stalk_exact X.toRingedSpace u).2.2.1 x
  have hFun := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hExact
  have hBij := ConcreteCategory.bijective_of_isIso (F.map e.hom)
  have hq' : F.map q = F.map (cokernel.π u) ≫ F.map e.hom := by
    rw [← F.map_comp, he]
  constructor
  · intro m
    change F.map q m = 0 ↔ ∃ a, F.map u a = m
    rw [hq', ConcreteCategory.comp_apply, ← (F.map e.hom).hom.map_zero]
    exact hBij.1.eq_iff.trans (hFun m)
  · have hs := (ModuleCat.epi_iff_surjective _).mp hSurj
    intro n
    obtain ⟨z, hz⟩ := hBij.2 n
    obtain ⟨m, hm⟩ := hs z
    refine ⟨m, ?_⟩
    rw [hq', ConcreteCategory.comp_apply, hm]
    exact hz

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules
private theorem restrict_sections_naturality {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (U : X.affineOpens)
    (s : moduleSpecΓFunctor.obj (M.restrict U.2.fromSpec)) :
    sectionsRestrictFromSpecLinearEquiv N U.2
      (((restrictFunctor U.2.fromSpec).map a).app ⊤ s) =
      a.app U.1 (sectionsRestrictFromSpecLinearEquiv M U.2 s) := by
  have hU : U.1 ≤ U.2.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  change N.presheaf.map _ (a.app (U.2.fromSpec ''ᵁ ⊤) s) =
    a.app U.1 (M.presheaf.map _ s)
  exact (congrArg (fun t ↦ t (s : M.val.obj (op (U.2.fromSpec ''ᵁ ⊤))))
    (a.val.naturality (homOfLE hU).op)).symm

private theorem restrict_sections_naturality_symm {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (U : X.affineOpens) (s : Γ(M, U.1)) :
    ((restrictFunctor U.2.fromSpec).map a).app ⊤
      ((sectionsRestrictFromSpecLinearEquiv M U.2).symm s) =
      (sectionsRestrictFromSpecLinearEquiv N U.2).symm (a.app U.1 s) := by
  apply (sectionsRestrictFromSpecLinearEquiv N U.2).injective
  rw [restrict_sections_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

private lemma chart_transport_eq {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (O : X.Opens) (hUO : U.1 ≤ O) (N : ModuleCat Γ(X, U.1))
    (θ : M.restrict U.2.fromSpec ≅ tilde N)
    {s t : M.val.obj (op O)} (hst : s = t) :
    θ.hom.app ⊤ ((sectionsRestrictFromSpecLinearEquiv M U.2).symm
      (M.presheaf.map (homOfLE hUO).op s)) =
    θ.hom.app ⊤ ((sectionsRestrictFromSpecLinearEquiv M U.2).symm
      (M.presheaf.map (homOfLE hUO).op t)) :=
  congrArg (fun z : M.val.obj (op O) ↦ θ.hom.app ⊤
    ((sectionsRestrictFromSpecLinearEquiv M U.2).symm
      (M.presheaf.map (homOfLE hUO).op z))) hst

private noncomputable def tensor_unit_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Y.Modules) (V : Y.Opens) (s : G.val.obj (op V)) :
    ((tensorPullback f).obj G).val.obj (op (f ⁻¹ᵁ V)) :=
  ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app (op V) s

private theorem normalized_affine_tensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (G : Y.Modules) (M : ModuleCat Γ(Y, V.1))
    (E : G.restrict V.2.fromSpec ≅ tilde M) :
    ∃ θ : ((tensorPullback f).obj G).restrict U.2.fromSpec ≅
        tilde ((ModuleCat.extendScalars (f.appLE V.1 U.1 hUV).hom).obj M),
      ∀ (s : Γ(G, V.1)) (m : M),
        E.hom.app ⊤ ((sectionsRestrictFromSpecLinearEquiv G V.2).symm s) =
          tilde.toOpen M ⊤ m →
        θ.hom.app ⊤
          ((sectionsRestrictFromSpecLinearEquiv ((tensorPullback f).obj G) U.2).symm
            (((tensorPullback f).obj G).presheaf.map (homOfLE hUV).op
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
                (op V.1) s))) =
          tilde.toOpen ((ModuleCat.extendScalars (f.appLE V.1 U.1 hUV).hom).obj M) ⊤
            ((ModuleCat.extendRestrictScalarsAdj (f.appLE V.1 U.1 hUV).hom).unit.app M m) := by
  let jV := V.2.fromSpec
  let jU := U.2.fromSpec
  let ρ := f.appLE V.1 U.1 hUV
  let ψ := Spec.map ρ
  have hsq : ψ ≫ jV = jU ≫ f := V.2.SpecMap_appLE_fromSpec f U.2 hUV
  let adj₁ := (restrictAdjunction jV).comp (pullbackPushforwardAdjunction ψ)
  let adj₂ := (pullbackPushforwardAdjunction f).comp (restrictAdjunction jU)
  let rightIso : pushforward ψ ⋙ pushforward jV ≅ pushforward jU ⋙ pushforward f :=
    pushforwardComp ψ jV ≪≫ pushforwardCongr hsq ≪≫ (pushforwardComp jU f).symm
  let k : restrictFunctor jV ⋙ pullback ψ ≅ pullback f ⋙ restrictFunctor jU :=
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)
  let c := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  let eT := (restrictFunctor jU).mapIso (c.app G)
  let eE := (pullback ψ).mapIso E
  let eP := (tildePullbackIso ρ).app M
  refine ⟨eT ≪≫ (k.app G).symm ≪≫ eE ≪≫ eP, ?_⟩
  intro s m hsm
  let eU := sectionsRestrictFromSpecLinearEquiv ((pullback f).obj G) U.2
  let eV := sectionsRestrictFromSpecLinearEquiv G V.2
  have ht : eT.hom.app ⊤
      ((sectionsRestrictFromSpecLinearEquiv ((tensorPullback f).obj G) U.2).symm
        (((tensorPullback f).obj G).presheaf.map (homOfLE hUV).op
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
            (op V.1) s))) =
      eU.symm (((pullback f).obj G).presheaf.map (homOfLE hUV).op
        ((pullbackUnit f G).app V.1 s)) := by
    apply eU.injective
    rw [eU.apply_symm_apply]
    rw [show eU (eT.hom.app ⊤ _) = _ from restrict_sections_naturality (c.hom.app G) U _]
    rw [LinearEquiv.apply_symm_apply]
    have hn := (c.hom.app G).val.naturality (homOfLE hUV).op
    have hv := Adjunction.unit_leftAdjointUniq_hom_app
      (Classical.choose (exists_tensorPullbackAdjunction f))
      (pullbackPushforwardAdjunction f) G
    exact (congrArg (fun q ↦ q
      (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
        (op V.1) s)) hn).trans
      (congrArg (fun z ↦ ((pullback f).obj G).presheaf.map (homOfLE hUV).op z)
        (congrArg (fun q ↦ q.val.app (op V.1) s) hv))
  have hk : (k.inv.app G).app ⊤
      (eU.symm (((pullback f).obj G).presheaf.map (homOfLE hUV).op
        ((pullbackUnit f G).app V.1 s))) =
      (pullbackUnit ψ (G.restrict jV)).app ⊤ (eV.symm s) := by
    have hh := affineChart_pullback_unit f V U hUV G s
    change eU ((k.hom.app G).app ⊤
      ((pullbackUnit ψ (G.restrict jV)).app ⊤ (eV.symm s))) = _ at hh
    have hh' := congrArg (fun z ↦ (k.inv.app G).app ⊤ (eU.symm z)) hh
    simpa only [LinearEquiv.symm_apply_apply, ← ConcreteCategory.comp_apply,
      ← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app, ConcreteCategory.id_apply] using hh'.symm
  change eP.hom.app ⊤ (eE.hom.app ⊤ ((k.inv.app G).app ⊤ (eT.hom.app ⊤ _))) = _
  rw [ht, hk]
  have hn := congrArg (fun t ↦ t.app ⊤ (eV.symm s))
    ((pullbackPushforwardAdjunction ψ).unit.naturality E.hom).symm
  change eE.hom.app ⊤ ((pullbackUnit ψ (G.restrict jV)).app ⊤ (eV.symm s)) =
    (pullbackUnit ψ (tilde M)).app ⊤ (E.hom.app ⊤ (eV.symm s)) at hn
  rw [hn, hsm]
  exact tildePullbackIso_hom_app_pullbackUnit ρ M m
private theorem normalized_affine_generators {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (G : Y.Modules) (M : ModuleCat Γ(Y, V.1))
    (E : G.restrict V.2.fromSpec ≅ tilde M) (I : Type u)
    (s : I → G.val.obj (op V.1)) (m : I → M)
    (gen : I → ((tensorPullback f).obj G).val.obj (op (f ⁻¹ᵁ V.1)))
    (hgen : ∀ i, tensor_unit_section f G V.1 (s i) = gen i)
    (hE : ∀ i, E.hom.app ⊤ ((sectionsRestrictFromSpecLinearEquiv G V.2).symm (s i)) =
      tilde.toOpen M ⊤ (m i)) :
    ∃ θ : ((tensorPullback f).obj G).restrict U.2.fromSpec ≅
        tilde ((ModuleCat.extendScalars (f.appLE V.1 U.1 hUV).hom).obj M),
      ∀ i, θ.hom.app ⊤
        ((sectionsRestrictFromSpecLinearEquiv ((tensorPullback f).obj G) U.2).symm
          (((tensorPullback f).obj G).presheaf.map (homOfLE hUV).op (gen i))) =
        tilde.toOpen ((ModuleCat.extendScalars (f.appLE V.1 U.1 hUV).hom).obj M) ⊤
          ((ModuleCat.extendRestrictScalarsAdj (f.appLE V.1 U.1 hUV).hom).unit.app M (m i)) := by
  obtain ⟨θ, hθ⟩ := normalized_affine_tensor f U V hUV G M E
  refine ⟨θ, fun i ↦ ?_⟩
  exact (chart_transport_eq ((tensorPullback f).obj G) U (f ⁻¹ᵁ V.1) hUV _ θ
    (hgen i)).symm.trans (hθ (s i) (m i) (hE i))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom
private theorem sections_restrict_symm_apply {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (s : Γ(M, U.1)) :
    (Modules.sectionsRestrictFromSpecLinearEquiv M U.2).symm s =
      M.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op s := rfl

private lemma iso_hom_inv_apply {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (O : X.Opens) (x : Γ(N, O)) :
    e.hom.app O (e.inv.app O x) = x :=
  congr($(e.inv_hom_id).val.app (op O) x)

private lemma spec_iso_inv_d {R A : CommRingCat.{u}} (φ : R ⟶ A) (a : A) :
    (relativeDifferentialsSpecIso φ).inv.val.app (op ⊤)
      (tilde.toOpen (CommRingCat.KaehlerDifferential φ) ⊤
        (CommRingCat.KaehlerDifferential.d a)) =
      (Spec.map φ).relativeDifferentialsDerivation.d ((Scheme.ΓSpecIso A).inv a) :=
  (ConcreteCategory.congr_hom
    (unit_app_comp_map_relativeDifferentialsSpecTildeHom φ)
    (CommRingCat.KaehlerDifferential.d a)).trans (relativeDifferentialsSpecΓHom_d φ a)

private lemma chart_ring_inv {X : Scheme.{u}} (U : X.affineOpens) (a : Γ(X, U.1)) :
    (U.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U.1)).inv a) =
      X.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op a := by
  have ht : (TopologicalSpace.Opens.leTop
      (⊤ : (Spec Γ(X, U.1)).Opens)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  simpa only [ConcreteCategory.comp_apply, ht, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (U.2.ΓSpecIso_inv_map_appIso_inv ⊤) a

private lemma iso_trans_inv_val_app {X : Scheme.{u}} {M N P : X.Modules}
    (e : M ≅ N) (d : N ≅ P) (O : X.Opensᵒᵖ) (x : P.val.obj O) :
    (e ≪≫ d).inv.val.app O x = e.inv.val.app O (d.inv.val.app O x) := rfl

private theorem normalized_affine_transport {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ T : f.relativeDifferentials.restrict U.2.fromSpec ≅
        (Spec.map (f.appLE V.1 U.1 hUV)).relativeDifferentials,
      f.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV =
        T ≪≫ relativeDifferentialsSpecIso (f.appLE V.1 U.1 hUV) ∧
      ∀ b : Γ(Spec Γ(X, U.1), ⊤),
        T.inv.val.app (op ⊤)
          ((Spec.map (f.appLE V.1 U.1 hUV)).relativeDifferentialsDerivation.d b) =
          f.relativeDifferentialsDerivation.d ((U.2.fromSpec.appIso ⊤).inv b) := by
  obtain ⟨T, hT, hd⟩ := relativeDifferentials_affine_chart_derivation f U V hUV
  refine ⟨T, ?_, hd⟩
  rw [hT]
  simp only [relativeDifferentialsRestrictFromSpecIso, Iso.trans_assoc]

private theorem affine_comparison_inv_d {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (a : Γ(X, U.1)) :
    (f.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).inv.val.app (op ⊤)
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV)) ⊤
        (CommRingCat.KaehlerDifferential.d a)) =
      f.relativeDifferentialsDerivation.d
        (X.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op a) := by
  obtain ⟨T, hE, hd⟩ := normalized_affine_transport f U V hUV
  rw [hE, iso_trans_inv_val_app, spec_iso_inv_d, hd, chart_ring_inv]

private lemma derivation_presheaf_map {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (D : M.val.Derivation' f.pullbackPresheafToPresheaf)
    {O P : X.Opensᵒᵖ} (i : O ⟶ P) (a : X.presheaf.obj O) :
    D.d (X.presheaf.map i a) = M.presheaf.map i (D.d a) := D.d_map i a

private lemma iso_apply_of_inv_apply {X : Scheme.{u}} {M N : X.Modules}
    (E : M ≅ N) (O : X.Opens) (x : M.val.obj (op O)) (y : N.val.obj (op O))
    (h : E.inv.val.app (op O) y = x) : E.hom.app O x = y :=
  (congrArg (E.hom.app O) h).symm.trans (iso_hom_inv_apply E O y)

private lemma sections_restrict_derivation {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (D : M.val.Derivation' f.pullbackPresheafToPresheaf)
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    D.d (X.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op a) =
      (Modules.sectionsRestrictFromSpecLinearEquiv M U.2).symm (D.d a) :=
  (derivation_presheaf_map f M D (homOfLE (U.2.fromSpec_image_le ⊤)).op a).trans
    (sections_restrict_symm_apply M U (D.d a)).symm

private theorem affine_comparison_inv_section {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (a : Γ(X, U.1)) :
    (f.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).inv.val.app (op ⊤)
      (tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV)) ⊤
        (CommRingCat.KaehlerDifferential.d a)) =
      (Modules.sectionsRestrictFromSpecLinearEquiv f.relativeDifferentials U.2).symm
        (f.relativeDifferentialsDerivation.d a) := by
  exact (affine_comparison_inv_d f U V hUV a).trans
    (sections_restrict_derivation f f.relativeDifferentials f.relativeDifferentialsDerivation U a)

private lemma affine_iso_apply {A : CommRingCat.{u}} (M : (Spec A).Modules)
    (N : ModuleCat A) (E : M ≅ tilde N) (x : M.val.obj (op ⊤)) (n : N)
    (h : E.inv.val.app (op ⊤) (tilde.toOpen N ⊤ n) = x) :
    E.hom.app ⊤ x = tilde.toOpen N ⊤ n :=
  iso_apply_of_inv_apply E ⊤ x (tilde.toOpen N ⊤ n) h

private theorem affine_comparison_d {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (a : Γ(X, U.1)) :
    (f.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).hom.app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv f.relativeDifferentials U.2).symm
        (f.relativeDifferentialsDerivation.d a)) =
      tilde.toOpen (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV)) ⊤
        (CommRingCat.KaehlerDifferential.d a) := by
  exact affine_iso_apply _ _
    (f.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV) _
    (CommRingCat.KaehlerDifferential.d a) (affine_comparison_inv_section f U V hUV a)

end AlgebraicGeometry.Scheme.Hom


open scoped ChangeOfRings
private theorem algebra_transitivity {R B A : CommRingCat.{u}} (φ : R ⟶ B) (ψ : B ⟶ A) :
    ∃ (u : (ModuleCat.extendScalars ψ.hom).obj (CommRingCat.KaehlerDifferential φ) ⟶
        CommRingCat.KaehlerDifferential (φ ≫ ψ))
      (v : CommRingCat.KaehlerDifferential (φ ≫ ψ) ⟶
        CommRingCat.KaehlerDifferential ψ),
      (∀ (a : A) (b : B), u (a • @id
        ((ModuleCat.extendScalars ψ.hom).obj (CommRingCat.KaehlerDifferential φ))
        ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
          (CommRingCat.KaehlerDifferential φ) (CommRingCat.KaehlerDifferential.d b))) =
          a • CommRingCat.KaehlerDifferential.d (ψ b)) ∧
      (∀ a : A, v (CommRingCat.KaehlerDifferential.d a) =
        CommRingCat.KaehlerDifferential.d a) ∧
      Function.Exact u v ∧ Function.Surjective v := by
  algebraize [φ.hom, ψ.hom, (φ ≫ ψ).hom]
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' rfl
  let u := ModuleCat.ofHom (KaehlerDifferential.mapBaseChange R B A)
  let v := ModuleCat.ofHom (KaehlerDifferential.map R B A A)
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a b
    change KaehlerDifferential.mapBaseChange R B A
      (a • ((1 : A) ⊗ₜ[B] KaehlerDifferential.D R B b)) =
        a • KaehlerDifferential.D R A (algebraMap B A b)
    simp only [map_smul, KaehlerDifferential.mapBaseChange_tmul,
      KaehlerDifferential.map_D, one_smul]
  · intro a
    exact KaehlerDifferential.map_D R B A A a
  · exact KaehlerDifferential.exact_mapBaseChange_map R B A
  · exact KaehlerDifferential.map_surjective R B A

private theorem algebra_transitivity_of_eq {R B A : CommRingCat.{u}} (φ : R ⟶ B) (ψ : B ⟶ A)
    (χ : R ⟶ A) (hχ : φ ≫ ψ = χ) :
    ∃ (u : (ModuleCat.extendScalars ψ.hom).obj (CommRingCat.KaehlerDifferential φ) ⟶
        CommRingCat.KaehlerDifferential χ)
      (v : CommRingCat.KaehlerDifferential χ ⟶
        CommRingCat.KaehlerDifferential ψ),
      (∀ (a : A) (b : B), u (a • @id
        ((ModuleCat.extendScalars ψ.hom).obj (CommRingCat.KaehlerDifferential φ))
        ((ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
          (CommRingCat.KaehlerDifferential φ) (CommRingCat.KaehlerDifferential.d b))) =
          a • CommRingCat.KaehlerDifferential.d (ψ b)) ∧
      (∀ a : A, v (CommRingCat.KaehlerDifferential.d a) =
        CommRingCat.KaehlerDifferential.d a) ∧
      Function.Exact u v ∧ Function.Surjective v := by
  subst χ
  exact algebra_transitivity φ ψ

namespace AlgebraicGeometry.Scheme.Hom

private lemma module_hom_naturality {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (s : Γ(M, V)) :
    a.app U (M.presheaf.map i.op s) = N.presheaf.map i.op (a.app V s) :=
  congrArg (fun t ↦ t s) (a.val.naturality i.op)

private lemma module_hom_app_of_val {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (U : X.Opens) {s : M.val.obj (op U)} {t : N.val.obj (op U)}
    (h : a.val.app (op U) s = t) : a.app U s = t := h

private lemma pulledback_generator_restrict {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (b : Γ(Y, V.1)) :
    (g.relativeDifferentialsPullbackMap h).app U.1
      (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
        (homOfLE hUV).op (g.relativeDifferentialsPullbackGenerator h V.1 b)) =
      (h ≫ g).relativeDifferentialsDerivation.d (h.appLE V.1 U.1 hUV b) := by
  have hn := module_hom_naturality (g.relativeDifferentialsPullbackMap h)
    (homOfLE hUV) (g.relativeDifferentialsPullbackGenerator h V.1 b)
  have hd := module_hom_app_of_val (g.relativeDifferentialsPullbackMap h) (h ⁻¹ᵁ V.1)
    ((Classical.choose_spec (existsUnique_relativeDifferentialsPullbackMap g h)).1 V.1 b)
  rw [hd] at hn
  exact hn.trans (derivation_presheaf_map (h ≫ g) (h ≫ g).relativeDifferentials
    (h ≫ g).relativeDifferentialsDerivation (homOfLE hUV).op (h.app V.1 b)).symm

private lemma tensor_unit_val {X Y : Scheme.{u}} (h : X ⟶ Y) (G : Y.Modules)
    (W : Y.Opens) (s : G.val.obj (op W)) :
    Modules.tensor_unit_section h G W s =
  (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (Modules.tensorPullbackRingMap h)
      (TopCat.Sheaf.inverseImageModule h.base Y.sheaf G)).presheaf).app
    (op (h ⁻¹ᵁ W))
    ((1 : X.sheaf.obj.obj (op (h ⁻¹ᵁ W))) ⊗ₜ[
      (TopCat.Sheaf.inverseImageRing h.base Y.sheaf).obj.obj (op (h ⁻¹ᵁ W)),
      ((Modules.tensorPullbackRingMap h).hom.app (op (h ⁻¹ᵁ W))).hom]
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map h.base) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app
            ((SheafOfModules.toSheaf _).obj G)).hom.app (op W)
              (s))) := by
  change ((Classical.choose (Modules.exists_tensorPullbackAdjunction h)).unit.app G).val.app
    (op W) s = _
  rw [Classical.choose_spec (Modules.exists_tensorPullbackAdjunction h)]
  rfl

private theorem tilde_arrow_compatibility {A : CommRingCat.{u}}
    {P Q : ModuleCat A} {M N : (Spec A).Modules} {I : Type u}
    (θ : M ≅ tilde P) (ε : N ≅ tilde Q) (a : M ⟶ N) (v : P ⟶ Q)
    (p : I → P) (q : I → Q)
    (hext : ∀ {F : (Spec A).Modules} {f g : tilde P ⟶ F},
      (∀ i, f.app ⊤ (tilde.toOpen P ⊤ (p i)) =
        g.app ⊤ (tilde.toOpen P ⊤ (p i))) → f = g)
    (s : I → moduleSpecΓFunctor.obj M)
    (hθ : ∀ i, θ.hom.app ⊤ (s i) = tilde.toOpen P ⊤ (p i))
    (hεa : ∀ i, ε.hom.app ⊤ (a.app ⊤ (s i)) = tilde.toOpen Q ⊤ (q i))
    (hv : ∀ i, v (p i) = q i) : a ≫ ε.hom = θ.hom ≫ (tilde.functor A).map v := by
  have hθi (i : I) : θ.inv.app ⊤ (tilde.toOpen P ⊤ (p i)) = s i :=
    (congrArg (θ.inv.app ⊤) (hθ i)).symm.trans
      (congr($(θ.hom_inv_id).val.app (op ⊤) (s i)))
  apply (cancel_epi θ.inv).mp
  rw [θ.inv_hom_id_assoc]
  apply hext
  intro i
  rw [Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Modules.Hom.comp_app, ConcreteCategory.comp_apply, hθi, hεa]
  exact ((ConcreteCategory.congr_hom (tilde.toOpen_map_app v ⊤) (p i)).trans
    (congrArg (tilde.toOpen Q ⊤) (hv i))).symm

private theorem restricted_arrow_value {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) (U : X.affineOpens) (Q : ModuleCat Γ(X, U.1))
    (ε : N.restrict U.2.fromSpec ≅ tilde Q)
    (s : Γ(M, U.1)) (t : Γ(N, U.1)) (n : Q)
    (hst : a.app U.1 s = t)
    (ht : ε.hom.app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv N U.2).symm t) =
      tilde.toOpen Q ⊤ n) :
    ε.hom.app ⊤ (((Modules.restrictFunctor U.2.fromSpec).map a).app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv M U.2).symm s)) =
      tilde.toOpen Q ⊤ n := by
  rw [Modules.restrict_sections_naturality_symm, hst]
  exact ht

private theorem restricted_tilde_arrow_compatibility {X : Scheme.{u}} {M N : X.Modules}
    (U : X.affineOpens) {P Q : ModuleCat Γ(X, U.1)} {I : Type u}
    (θ : M.restrict U.2.fromSpec ≅ tilde P) (ε : N.restrict U.2.fromSpec ≅ tilde Q)
    (a : M ⟶ N) (v : P ⟶ Q) (p : I → P) (q : I → Q)
    (hext : ∀ {F : (Spec Γ(X, U.1)).Modules} {f g : tilde P ⟶ F},
      (∀ i, f.app ⊤ (tilde.toOpen P ⊤ (p i)) =
        g.app ⊤ (tilde.toOpen P ⊤ (p i))) → f = g)
    (s : I → Γ(M, U.1)) (t : I → Γ(N, U.1))
    (hθ : ∀ i, θ.hom.app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv M U.2).symm (s i)) =
      tilde.toOpen P ⊤ (p i))
    (hε : ∀ i, ε.hom.app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv N U.2).symm (t i)) =
      tilde.toOpen Q ⊤ (q i))
    (ha : ∀ i, a.app U.1 (s i) = t i) (hv : ∀ i, v (p i) = q i) :
    (Modules.restrictFunctor U.2.fromSpec).map a ≫ ε.hom =
      θ.hom ≫ (tilde.functor Γ(X, U.1)).map v := by
  refine tilde_arrow_compatibility θ ε ((Modules.restrictFunctor U.2.fromSpec).map a)
    v p q hext (fun i ↦ (Modules.sectionsRestrictFromSpecLinearEquiv M U.2).symm (s i))
    hθ ?_ hv
  intro i
  exact restricted_arrow_value a U Q ε (s i) (t i) (q i) (ha i) (hε i)

private noncomputable def derivation_section {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (D : M.val.Derivation' f.pullbackPresheafToPresheaf)
    (O : X.Opens) (a : Γ(X, O)) : Γ(M, O) := D.d (X := op O) a

private theorem derivation_section_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (D : M.val.Derivation' f.pullbackPresheafToPresheaf)
    (O : X.Opens) (a : Γ(X, O)) : derivation_section f M D O a = D.d (X := op O) a := rfl

private noncomputable def derivation_raw_section {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (D : M.val.Derivation' f.pullbackPresheafToPresheaf)
    (O : X.Opens) (a : Γ(X, O)) : M.val.obj (op O) := D.d (X := op O) a

private theorem derivation_raw_section_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (M : X.Modules) (D : M.val.Derivation' f.pullbackPresheafToPresheaf)
    (O : X.Opens) (a : Γ(X, O)) :
    derivation_raw_section f M D O a = D.d (X := op O) a := rfl

private noncomputable def restricted_section {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (hUV : U ≤ V) (s : M.val.obj (op V)) : Γ(M, U) :=
  M.presheaf.map (homOfLE hUV).op s

private theorem restricted_section_eq {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (hUV : U ≤ V) (s : M.val.obj (op V)) :
    restricted_section M U V hUV s = M.presheaf.map (homOfLE hUV).op s := rfl

private noncomputable def extended_generator {R B A : CommRingCat.{u}}
    (φ : R ⟶ B) (ψ : B ⟶ A) (b : B) :
    (ModuleCat.extendScalars ψ.hom).obj (CommRingCat.KaehlerDifferential φ) :=
  (ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
    (CommRingCat.KaehlerDifferential φ) (CommRingCat.KaehlerDifferential.d b)

private theorem extended_generator_eq {R B A : CommRingCat.{u}}
    (φ : R ⟶ B) (ψ : B ⟶ A) (b : B) :
    extended_generator φ ψ b = (ModuleCat.extendRestrictScalarsAdj ψ.hom).unit.app
      (CommRingCat.KaehlerDifferential φ) (CommRingCat.KaehlerDifferential.d b) := rfl

private noncomputable def algebra_differential {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (a : A) : CommRingCat.KaehlerDifferential φ := CommRingCat.KaehlerDifferential.d a

private theorem algebra_differential_eq {R A : CommRingCat.{u}} (φ : R ⟶ A) (a : A) :
    algebra_differential φ a = CommRingCat.KaehlerDifferential.d a := rfl

private theorem map_one_generator {A : CommRingCat.{u}} {P Q : ModuleCat A}
    (v : P ⟶ Q) (p : P) (q : Q)
    (h : v ((1 : A) • @id P p) = (1 : A) • q) : v p = q := by
  simpa only [one_smul, id_eq] using h

private theorem affine_u_compatibility
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (U : X.affineOpens) (V : Y.affineOpens) (W : S.affineOpens)
    (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ g ⁻¹ᵁ W.1)
    (θ : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict U.2.fromSpec ≅
      tilde ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
        (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))))
    (hθ' : ∀ b : Γ(Y, V.1), θ.hom.app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv
        ((Modules.tensorPullback h).obj g.relativeDifferentials) U.2).symm
        (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
          (homOfLE hUV).op (g.relativeDifferentialsPullbackGenerator h V.1 b))) =
      tilde.toOpen ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
        (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))) ⊤
        ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
          (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
            (CommRingCat.KaehlerDifferential.d b)))
    (uA : (ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
        (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)) ⟶
      CommRingCat.KaehlerDifferential
        ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
    (hu : ∀ (a : Γ(X, U.1)) (b : Γ(Y, V.1)),
      uA (a • @id
        ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
          (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)))
        ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
          (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
            (CommRingCat.KaehlerDifferential.d b))) =
        a • CommRingCat.KaehlerDifferential.d (h.appLE V.1 U.1 hUV b))
    (w : (Modules.tensorPullback h).obj g.relativeDifferentials ⟶
      (h ≫ g).relativeDifferentials)
    (hw : ∀ b : Γ(Y, V.1), w.app U.1
      (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
        (homOfLE hUV).op (g.relativeDifferentialsPullbackGenerator h V.1 b)) =
      (h ≫ g).relativeDifferentialsDerivation.d (h.appLE V.1 U.1 hUV b))
    (ε : (h ≫ g).relativeDifferentials.restrict U.2.fromSpec ≅
      tilde (CommRingCat.KaehlerDifferential
        ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx)))))
    (hε : ∀ a : Γ(X, U.1), ε.hom.app ⊤
      ((Modules.sectionsRestrictFromSpecLinearEquiv (h ≫ g).relativeDifferentials U.2).symm
        ((h ≫ g).relativeDifferentialsDerivation.d a)) =
      tilde.toOpen (CommRingCat.KaehlerDifferential
        ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx)))) ⊤
        (CommRingCat.KaehlerDifferential.d a)) :
    (Modules.restrictFunctor U.2.fromSpec).map w ≫ ε.hom =
      θ.hom ≫ (tilde.functor Γ(X, U.1)).map uA := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      refine restricted_tilde_arrow_compatibility (X := X)
        (M := (Modules.tensorPullback h).obj g.relativeDifferentials)
        (N := (h ≫ g).relativeDifferentials)
        (P := (ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
          (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)))
        (Q := CommRingCat.KaehlerDifferential
          ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
        (I := Γ(Y, V.1)) U θ ε w uA
        (extended_generator (g.appLE W.1 V.1 hVW) (h.appLE V.1 U.1 hUV))
        (fun b ↦ algebra_differential
          ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))) (h.appLE V.1 U.1 hUV b)) ?_
        (fun b ↦ restricted_section ((Modules.tensorPullback h).obj g.relativeDifferentials)
          U.1 (h ⁻¹ᵁ V.1) hUV (g.relativeDifferentialsPullbackGenerator h V.1 b))
        (fun b ↦ derivation_section (h ≫ g) (h ≫ g).relativeDifferentials
          (h ≫ g).relativeDifferentialsDerivation U.1 (h.appLE V.1 U.1 hUV b))
        (by
          as_aux_lemma =>
            intro b
            rw [restricted_section_eq, extended_generator_eq]
            exact hθ' b)
        (by
          as_aux_lemma =>
            intro b
            rw [derivation_section_eq, algebra_differential_eq]
            exact hε (h.appLE V.1 U.1 hUV b))
        (by
          as_aux_lemma =>
            intro b
            rw [derivation_section_eq, restricted_section_eq]
            exact hw b) ?_
      · as_aux_lemma =>
          intro F a b hab
          apply tilde_extend_differential_ext
            (R := Γ(S, W.1)) (B := Γ(Y, V.1)) (A := Γ(X, U.1))
            (g.appLE W.1 V.1 hVW) (h.appLE V.1 U.1 hUV)
          intro c
          have hc := hab c
          rw [extended_generator_eq] at hc
          exact hc
      · as_aux_lemma =>
          intro b
          rw [extended_generator_eq, algebra_differential_eq]
          exact map_one_generator uA _ _ (hu (1 : Γ(X, U.1)) b)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem affine_v_compatibility
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a)
    (U : X.affineOpens) (V : Y.affineOpens) (W : S.affineOpens)
    [IsOpenImmersion U.2.fromSpec]
    (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ g ⁻¹ᵁ W.1)
    (vA : CommRingCat.KaehlerDifferential
        ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))) ⟶
      CommRingCat.KaehlerDifferential (h.appLE V.1 U.1 hUV))
    (hv : ∀ a : Γ(X, U.1), vA (CommRingCat.KaehlerDifferential.d a) =
      CommRingCat.KaehlerDifferential.d a) :
    (Modules.restrictFunctor U.2.fromSpec).map q ≫
        (h.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).hom =
      ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
        (fun _ hx ↦ hVW (hUV hx))).hom ≫ (tilde.functor Γ(X, U.1)).map vA := by
  refine restricted_tilde_arrow_compatibility (X := X)
    (M := (h ≫ g).relativeDifferentials) (N := h.relativeDifferentials)
    (P := CommRingCat.KaehlerDifferential
      ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
    (Q := CommRingCat.KaehlerDifferential (h.appLE V.1 U.1 hUV))
    (I := Γ(X, U.1)) U
    ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
      (fun _ hx ↦ hVW (hUV hx)))
    (h.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV) q vA
    (CommRingCat.KaehlerDifferential.d
      (f := (h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
    (CommRingCat.KaehlerDifferential.d (f := h.appLE V.1 U.1 hUV)) ?_
    (derivation_section (h ≫ g) (h ≫ g).relativeDifferentials
      (h ≫ g).relativeDifferentialsDerivation U.1)
    (derivation_section h h.relativeDifferentials h.relativeDifferentialsDerivation U.1)
    (by
      as_aux_lemma =>
        intro a
        rw [derivation_section_eq]
        exact affine_comparison_d (h ≫ g) U W (fun _ hx ↦ hVW (hUV hx)) a)
    (by
      as_aux_lemma =>
        intro a
        rw [derivation_section_eq]
        exact affine_comparison_d h U V hUV a)
    (by
      as_aux_lemma =>
        intro a
        rw [derivation_section_eq, derivation_section_eq]
        exact hq U.1 a) hv
  intro F a b hab
  exact tilde_differential_ext (R := Γ(S, W.1)) (A := Γ(X, U.1))
    ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))) hab

/-- The normalized affine and stalk form of the transitivity sequence for relative
Kähler differential sheaves.

Source: Stacks Project, Morphisms, Tag 01UX (`lemma-triangle-differentials`),
affine description Tag 01UT, functoriality Tag 01UV and localized exactness Tag 00CS.
The stalk clause follows from the universal-cokernel property and exactness of
module stalks. For the affine clause, adjunction-unit formulas normalize the
comparison, and the algebraic Kähler first exact sequence supplies the maps.
The two equalities of sheaf arrows are checked on differential generators via
the tilde and extension-of-scalars adjunctions. -/
theorem relativeDifferentials_transitivity_affine_stalk
    {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    (q : (h ≫ g).relativeDifferentials ⟶ h.relativeDifferentials)
    (hq : ∀ (O : X.Opens) (a : Γ(X, O)),
      q.app O ((h ≫ g).relativeDifferentialsDerivation.d (X := op O) a) =
        h.relativeDifferentialsDerivation.d (X := op O) a) :
      (∀ x : X,
        Function.Exact
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
            (g.relativeDifferentialsPullbackMap h))
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q) ∧
        Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map q)) ∧
      (∀ (U : X.affineOpens) (V : Y.affineOpens) (W : S.affineOpens)
          (hUV : U.1 ≤ h ⁻¹ᵁ V.1) (hVW : V.1 ≤ g ⁻¹ᵁ W.1),
        ∃ θ : ((Modules.tensorPullback h).obj g.relativeDifferentials).restrict U.2.fromSpec ≅
            tilde ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
              (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))),
          (∀ b : Γ(Y, V.1),
            θ.hom.app ⊤
              ((Modules.sectionsRestrictFromSpecLinearEquiv
                ((Modules.tensorPullback h).obj g.relativeDifferentials) U.2).symm
                (((Modules.tensorPullback h).obj g.relativeDifferentials).presheaf.map
                  (homOfLE hUV).op (g.relativeDifferentialsPullbackGenerator h V.1 b))) =
              tilde.toOpen ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))) ⊤
                  ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
                    (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
                      (CommRingCat.KaehlerDifferential.d b))) ∧
          ∃ (uA : (ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)) ⟶
              CommRingCat.KaehlerDifferential
                ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))))
            (vA : CommRingCat.KaehlerDifferential
                ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx))) ⟶
              CommRingCat.KaehlerDifferential (h.appLE V.1 U.1 hUV)),
            (∀ (a : Γ(X, U.1)) (b : Γ(Y, V.1)),
              uA (a • @id
                ((ModuleCat.extendScalars (h.appLE V.1 U.1 hUV).hom).obj
                  (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW)))
                ((ModuleCat.extendRestrictScalarsAdj (h.appLE V.1 U.1 hUV).hom).unit.app
                  (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
                    (CommRingCat.KaehlerDifferential.d b))) =
                a • CommRingCat.KaehlerDifferential.d (h.appLE V.1 U.1 hUV b)) ∧
            (∀ a : Γ(X, U.1), vA (CommRingCat.KaehlerDifferential.d a) =
              CommRingCat.KaehlerDifferential.d a) ∧
            Function.Exact uA vA ∧ Function.Surjective vA ∧
            (Modules.restrictFunctor U.2.fromSpec).map
                (g.relativeDifferentialsPullbackMap h) ≫
              ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
                (fun _ hx ↦ hVW (hUV hx))).hom =
              θ.hom ≫ (tilde.functor Γ(X, U.1)).map uA ∧
            (Modules.restrictFunctor U.2.fromSpec).map q ≫
                (h.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV).hom =
              ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
                (fun _ hx ↦ hVW (hUV hx))).hom ≫ (tilde.functor Γ(X, U.1)).map vA) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      constructor
      · exact quotient_stalk_exact h g q hq
      · intro U V W hUV hVW
        have hUOpen := IsAffineOpen.isOpenImmersion_fromSpec U.2
        have hVOpen := IsAffineOpen.isOpenImmersion_fromSpec V.2
        obtain ⟨θ, hθ'⟩ := Modules.normalized_affine_generators (X := X) (Y := Y)
          h U V hUV g.relativeDifferentials
          (CommRingCat.KaehlerDifferential (g.appLE W.1 V.1 hVW))
          (g.relativeDifferentialsRestrictFromSpecIso W.2 V.2 hVW) Γ(Y, V.1)
          (derivation_raw_section g g.relativeDifferentials
            g.relativeDifferentialsDerivation V.1)
          (CommRingCat.KaehlerDifferential.d (f := g.appLE W.1 V.1 hVW))
          (g.relativeDifferentialsPullbackGenerator h V.1)
          (by
            as_aux_lemma =>
              intro b
              rw [derivation_raw_section_eq]
              exact tensor_unit_val (X := X) (Y := Y) h g.relativeDifferentials V.1
                (g.relativeDifferentialsDerivation.d (X := op V.1) b))
          (by
            as_aux_lemma =>
              intro b
              rw [derivation_raw_section_eq]
              exact affine_comparison_d g V W hVW b)
        have H := algebra_transitivity_of_eq
          (R := Γ(S, W.1)) (B := Γ(Y, V.1)) (A := Γ(X, U.1))
          (g.appLE W.1 V.1 hVW) (h.appLE V.1 U.1 hUV)
          ((h ≫ g).appLE W.1 U.1 (fun _ hx ↦ hVW (hUV hx)))
          (appLE_comp_appLE h g W.1 V.1 U.1 hVW hUV)
        obtain ⟨uA, vA, hu, hv, hex, hsurj⟩ := H
        refine ⟨θ, hθ', uA, vA, hu, hv, hex, hsurj, ?_, ?_⟩
        · exact affine_u_compatibility h g U V W hUV hVW θ hθ' uA hu
            (g.relativeDifferentialsPullbackMap h) (pulledback_generator_restrict h g U V hUV)
            ((h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2
              (fun _ hx ↦ hVW (hUV hx)))
            (affine_comparison_d (h ≫ g) U W (fun _ hx ↦ hVW (hUV hx)))
        · exact affine_v_compatibility h g q hq U V W hUV hVW vA hv

end AlgebraicGeometry.Scheme.Hom
