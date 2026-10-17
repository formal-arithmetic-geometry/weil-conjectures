/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.StageCover
public import WeilConjectures.AlgebraicGeometry.EtaleLimitCompatibleExactSystems
public import WeilConjectures.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta

/-!
# Continuity of étale cohomology for systems of sheaves

Let `D : Iᵒᵖ ⥤ Scheme` be a directed inverse system of quasi-compact quasi-separated schemes
with affine transition maps and limit `X`, and `(Fᵢ, φ)` a system of abelian étale sheaves with
colimit `L` on `X` of the pullbacks of the `Fᵢ`. This file proves, by dimension shifting from
degree `n` to degree `n + 1`, that `Hⁿ(X, L) = colimᵢ Hⁿ(Dᵢ, Fᵢ)`
(`AlgebraicGeometry.Etale.SystemData.isContinuousAt_succ`): the system embeds into a system of
injective sheaves (`AlgebraicGeometry.Etale.etale_limit_compatible_exact_systems`), whose colimit
has no higher cohomology (`AlgebraicGeometry.Etale.SystemData.subsingleton_H_succ_of_injective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale.SystemData

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (S : SystemData D c)

/-- The identity and composition laws of the transition maps of a system. -/
structure Laws : Prop where
  hidentity : ∀ i : I, S.φ (𝟙 i) =
    (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
      (S.F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (S.F i)
  hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
    S.φ (f ≫ g) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
        (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (S.F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (S.φ f) ≫ S.φ g

/-- The map `Hⁿ(Dᵢ, Fᵢ) ⟶ Hⁿ(X, L)`. -/
noncomputable def toLimitH (i : I) (n : ℕ) : Sheaf.H (S.F i) n →+ Sheaf.H S.L.pt n :=
  (Sheaf.H.map ((S.eG i).inv ≫ S.L.ι.app i) n).comp (cohomologyMap (c.π.app (op i)) (S.F i) n)

/-- The transition map `Hⁿ(Dᵢ, Fᵢ) ⟶ Hⁿ(Dⱼ, Fⱼ)`. -/
noncomputable def transitionH {i j : I} (f : i ⟶ j) (n : ℕ) :
    Sheaf.H (S.F i) n →+ Sheaf.H (S.F j) n :=
  (Sheaf.H.map (S.φ f) n).comp (cohomologyMap (D.map f.op) (S.F i) n)

/-- *Continuity in degree `n`*: `Hⁿ(X, L)` is the filtered colimit of the `Hⁿ(Dᵢ, Fᵢ)`. -/
def IsContinuousAt (n : ℕ) : Prop :=
  (∀ x : Sheaf.H S.L.pt n, ∃ (i : I) (y : Sheaf.H (S.F i) n), S.toLimitH i n y = x) ∧
    ∀ (i : I) (y : Sheaf.H (S.F i) n), S.toLimitH i n y = 0 →
      ∃ (j : I) (f : i ⟶ j), S.transitionH f n y = 0

variable {S}

lemma Laws.transitionH_comp (hS : S.Laws) {i j k : I} (f : i ⟶ j) (g : j ⟶ k) (n : ℕ)
    (y : Sheaf.H (S.F i) n) :
    S.transitionH (f ≫ g) n y = S.transitionH g n (S.transitionH f n y) := by
  obtain ⟨H, eH, hH, -, -, -⟩ := etale_limit_canonical_cohomology_diagram D c S.F S.φ
    hS.hidentity hS.hcomposition S.G S.eG S.hG S.L n
  have h := H.map_comp f g
  rw [hH, hH, hH] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  have h' := (cancel_mono (eH k).inv).1 ((cancel_epi (eH i).hom).1 h)
  exact congrArg (fun φ ↦ φ.hom y) h'

lemma Laws.toLimitH_transitionH (hS : S.Laws) {i j : I} (f : i ⟶ j) (n : ℕ)
    (y : Sheaf.H (S.F i) n) : S.toLimitH j n (S.transitionH f n y) = S.toLimitH i n y := by
  obtain ⟨H, eH, hH, B, eB, hB⟩ := etale_limit_canonical_cohomology_diagram D c S.F S.φ
    hS.hidentity hS.hcomposition S.G S.eG S.hG S.L n
  have hcat : H.map f ≫ B.ι.app j ≫ eB.hom = B.ι.app i ≫ eB.hom := by
    rw [← Category.assoc, B.w f]
  rw [hB j, hB i, hH i j f] at hcat
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hcat
  have hh := (cancel_epi (eH i).hom).1 hcat
  exact congrArg (fun φ ↦ φ.hom y) hh

section Step

variable [IsDirected I (· ≤ ·)] [Nonempty I] (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
  in
private lemma boundary_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (hS : S.ShortExact)
    (S' : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) (hS' : S'.ShortExact)
    (t : S.map (upperStar AddCommGrpCat.{u + 1} f) ⟶ S') (n : ℕ) (z : Sheaf.H S.X₃ n) :
    Sheaf.H.map t.τ₁ (n + 1) (cohomologyMap f S.X₁ (n + 1) (Sheaf.H.δSucc hS n z)) =
      Sheaf.H.δSucc hS' n (Sheaf.H.map t.τ₃ n (cohomologyMap f S.X₃ n z)) :=
  (congrArg (Sheaf.H.map t.τ₁ (n + 1)) (cohomologyMap_δSucc f hS n z)).trans
    (Sheaf.H.map_δSucc (hS.map_of_exact (upperStar AddCommGrpCat.{u + 1} f)) hS' t n _)

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
  in
private lemma middle_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (S' : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (t : S.map (upperStar AddCommGrpCat.{u + 1} f) ⟶ S') (n : ℕ) (z : Sheaf.H S.X₂ n) :
    Sheaf.H.map t.τ₃ n (cohomologyMap f S.X₃ n (Sheaf.H.map S.g n z)) =
      Sheaf.H.map S'.g n (Sheaf.H.map t.τ₂ n (cohomologyMap f S.X₂ n z)) := by
  rw [cohomologyMap_map f n S.g z]
  exact (Sheaf.H.map_comp_apply
    ((upperStar AddCommGrpCat.{u + 1} f).map S.g) t.τ₃ _).symm.trans
      ((congrArg (fun h ↦ Sheaf.H.map h n (cohomologyMap f S.X₂ n z))
        t.comm₂₃.symm).trans (Sheaf.H.map_comp_apply t.τ₂ S'.g _))

include hc in
/-- **Dimension shifting for continuity.** If continuity holds in degree `n` for all systems,
it holds in degree `n + 1` for all systems. -/
theorem isContinuousAt_succ {n : ℕ}
    (ih : ∀ S : SystemData D c, S.Laws → S.IsContinuousAt n) (S : SystemData D c)
    (hS : S.Laws) : S.IsContinuousAt (n + 1) := by
  apply etale_limit_compatible_exact_systems D c S.F S.φ hS.hidentity hS.hcomposition S.G S.eG
    S.hG S.L S.hL
  intro FR φR hidR hcompR GR eGR hGR LR hLR FI ψ hidI hcompI GI eGI hGI LI hLI a b w hE
    ai bi wi hi t r ⟨hr₁, hr₂, hr₃, ht₂, hinj, ht₁, ht₃⟩
  let SR : SystemData D c := ⟨FR, φR, GR, eGR, hGR, LR, hLR⟩
  let SI : SystemData D c := ⟨FI, ψ, GI, eGI, hGI, LI, hLI⟩
  have hSR : SR.Laws := ⟨hidR, hcompR⟩
  have hSI : SI.Laws := ⟨hidI, hcompI⟩
  obtain ⟨sR, iR⟩ := ih SR hSR
  obtain ⟨sI, -⟩ := ih SI hSI
  have hLI0 : Subsingleton (Sheaf.H LI.pt (n + 1)) := subsingleton_H_succ_of_injective hc SI hinj n
  let δ (k : I) : Sheaf.H (FR k) n →+ Sheaf.H (S.F k) (n + 1) := Sheaf.H.δSucc (hi k) n
  let β : Sheaf.H LR.pt n →+ Sheaf.H S.L.pt (n + 1) := Sheaf.H.δSucc hE n
  -- compatibilities
  have h₄ (k : I) (z : Sheaf.H (FR k) n) : S.toLimitH k (n + 1) (δ k z) = β (SR.toLimitH k n z) := by
    have h := boundary_naturality (c.π.app (op k)) _ (hi k) _ hE (t k) n z
    rw [ht₁ k, ht₃ k] at h
    exact h
  have h₅ (k : I) (v : Sheaf.H (FI k) n) :
      SR.toLimitH k n (Sheaf.H.map (bi k) n v) = Sheaf.H.map b n (SI.toLimitH k n v) := by
    have h := middle_naturality (c.π.app (op k)) _ _ (t k) n v
    rw [ht₃ k, ht₂ k] at h
    exact h
  have h₃ {j k : I} (f : j ⟶ k) (z : Sheaf.H (FR j) n) :
      S.transitionH f (n + 1) (δ j z) = δ k (SR.transitionH f n z) := by
    have h := boundary_naturality (D.map f.op) _ (hi j) _ (hi k) (r j k f) n z
    rw [hr₁ j k f, hr₃ j k f] at h
    exact h
  have h₃' {j k : I} (f : j ⟶ k) (v : Sheaf.H (FI j) n) :
      SR.transitionH f n (Sheaf.H.map (bi j) n v) =
        Sheaf.H.map (bi k) n (SI.transitionH f n v) := by
    have h := middle_naturality (D.map f.op) _ _ (r j k f) n v
    rw [hr₃ j k f, hr₂ j k f] at h
    exact h
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · -- surjectivity
    obtain ⟨y, rfl⟩ := (Sheaf.H.exact_δSucc_map hE n x).1 (Subsingleton.elim _ _)
    obtain ⟨k, z, rfl⟩ := sR y
    exact ⟨k, δ k z, h₄ k z⟩
  · -- injectivity
    have : Injective (FI i) := hinj i
    obtain ⟨z, rfl⟩ := Sheaf.H.δSucc_surjective (hi i) n y
    obtain ⟨w', hw'⟩ := (Sheaf.H.exact_map_δSucc hE n (SR.toLimitH i n z)).1
      (by rw [← h₄]; exact hy)
    obtain ⟨m, v, rfl⟩ := sI w'
    obtain ⟨k, hik, hmk⟩ := directed_of (· ≤ ·) i m
    have hz : SR.toLimitH k n (SR.transitionH (homOfLE hik) n z -
        Sheaf.H.map (bi k) n (SI.transitionH (homOfLE hmk) n v)) = 0 := by
      rw [map_sub, h₅, hSR.toLimitH_transitionH, hSI.toLimitH_transitionH, hw', sub_self]
    obtain ⟨l, g, hg⟩ := iR k _ hz
    refine ⟨l, homOfLE hik ≫ g, ?_⟩
    rw [map_sub, sub_eq_zero, h₃'] at hg
    rw [hS.transitionH_comp, h₃, h₃, hg]
    exact (Sheaf.H.exact_map_δSucc (hi l) n _).2 ⟨_, rfl⟩

end Step

section Zero

omit [Preorder I] in
/-- The degree zero pullback of a global section, on sections over the terminal objects. -/
lemma equiv₀_cohomologyMap_zero {X Y : Scheme.{u}} (u : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (s : G.obj.obj (op (⊤_ X.Etale))) :
    Sheaf.H.equiv₀ _ terminalIsTerminal
        (cohomologyMap u G 0 ((Sheaf.H.equiv₀ G terminalIsTerminal).symm s)) =
      ((upperStar AddCommGrpCat.{u + 1} u).obj G).obj.map (PreservesTerminal.iso u.Etale).inv.op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit.app G).hom.app
          (op (⊤_ X.Etale)) s) := by
  let e := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  let e' := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  have hs : e.hom.app G (e.inv.app G s) = s := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
    rfl
  have h := cohomologyMap_zero_eq_globalSectionsUpperStarMap u G (e.inv.app G s)
  rw [hs] at h
  rw [h, AddEquiv.apply_symm_apply]
  simp only [globalSectionsUpperStarMap, ConcreteCategory.comp_apply, hs]
  rw [← ConcreteCategory.comp_apply (e'.inv.app _) (e'.hom.app _), Iso.inv_hom_id_app]
  rfl

variable [IsDirected I (· ≤ ·)] [Nonempty I] (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]

variable (S) in
omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
  in
lemma equiv₀_toLimitH (i : I) (y : Sheaf.H (S.F i) 0) :
    Sheaf.H.equiv₀ _ terminalIsTerminal (S.toLimitH i 0 y) =
      (S.L.ι.app i).hom.app _ ((S.eG i).inv.hom.app _
        (((upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (S.F i)).obj.map
          (PreservesTerminal.iso (c.π.app (op i)).Etale).inv.op
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app (op i))).unit.app
            (S.F i)).hom.app (op (⊤_ _)) (Sheaf.H.equiv₀ _ terminalIsTerminal y)))) := by
  rw [← (Sheaf.H.equiv₀ _ terminalIsTerminal).symm_apply_apply y]
  change Sheaf.H.equiv₀ _ _ (Sheaf.H.map _ 0 (cohomologyMap _ _ 0 _)) = _
  rw [← Sheaf.H.equiv₀_naturality, equiv₀_cohomologyMap_zero, AddEquiv.apply_symm_apply]
  rfl

variable (S) in
omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
  in
lemma equiv₀_transitionH {i j : I} (f : i ⟶ j) (y : Sheaf.H (S.F i) 0) :
    Sheaf.H.equiv₀ _ terminalIsTerminal (S.transitionH f 0 y) =
      (S.φ f).hom.app _
        (((upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (S.F i)).obj.map
          (PreservesTerminal.iso (D.map f.op).Etale).inv.op
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (D.map f.op)).unit.app
            (S.F i)).hom.app (op (⊤_ _)) (Sheaf.H.equiv₀ _ terminalIsTerminal y))) := by
  rw [← (Sheaf.H.equiv₀ _ terminalIsTerminal).symm_apply_apply y]
  change Sheaf.H.equiv₀ _ _ (Sheaf.H.map _ 0 (cohomologyMap _ _ 0 _)) = _
  rw [← Sheaf.H.equiv₀_naturality, equiv₀_cohomologyMap_zero, AddEquiv.apply_symm_apply]

include hc in
/-- **Continuity in degree zero**: `H⁰(X, L) = colimᵢ H⁰(Dᵢ, Fᵢ)`. -/
theorem isContinuousAt_zero (S : SystemData D c) (hS : S.Laws) : S.IsContinuousAt 0 := by
  have hterm (Z : Scheme.{u}) : IsTerminal
      (MorphismProperty.Over.mk ⊤ (𝟙 Z) (MorphismProperty.id_mem _ _) : Z.Etale) :=
    MorphismProperty.Over.mkIdTerminal _ _
  -- the section of `Fⱼ` over the terminal object `Wf` of `Dⱼ` over `D_{i₀}` given by a class
  let sec {i₀ j : I} (f : i₀ ⟶ j) (z : Sheaf.H (S.F j) 0) :
      (S.F j).obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map f.op)).obj
        (MorphismProperty.Over.mk ⊤ (𝟙 _) (MorphismProperty.id_mem _ _)))) :=
    (S.F j).obj.map (terminal.from _).op (Sheaf.H.equiv₀ _ terminalIsTerminal z)
  have hsec_inj {i₀ j : I} (f : i₀ ⟶ j) : Function.Injective (sec f) := by
    have hW : IsTerminal ((MorphismProperty.Over.pullback @Etale ⊤ (D.map f.op)).obj
        (MorphismProperty.Over.mk ⊤ (𝟙 _) (MorphismProperty.id_mem _ _))) :=
      IsTerminal.isTerminalObj (D.map f.op).Etale _ (hterm _)
    intro z z' h
    apply (Sheaf.H.equiv₀ _ terminalIsTerminal).injective
    have h' := congrArg ((S.F j).obj.map (hW.from (⊤_ _)).op) h
    simp only [sec, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h'
    rwa [terminal.hom_ext (hW.from (⊤_ _) ≫ terminal.from _) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id] at h'
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨k⟩ := ‹Nonempty I›
    let T₀ : (D.obj (op k)).Etale :=
      MorphismProperty.Over.mk ⊤ (𝟙 _) (MorphismProperty.id_mem _ _)
    have : CompactSpace T₀.left := inferInstanceAs (CompactSpace (D.obj (op k)))
    have : QuasiSeparatedSpace T₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj (op k)))
    have hW : IsTerminal ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op k))).obj T₀) :=
      IsTerminal.isTerminalObj (c.π.app (op k)).Etale T₀ (hterm _)
    obtain ⟨j, f, t, ht⟩ := S.exists_stageMap_app_eq hc T₀
      (S.L.pt.obj.map (terminal.from _).op (Sheaf.H.equiv₀ _ terminalIsTerminal x))
    have hWf : IsTerminal ((MorphismProperty.Over.pullback @Etale ⊤ (D.map f.op)).obj T₀) :=
      IsTerminal.isTerminalObj (D.map f.op).Etale T₀ (hterm _)
    refine ⟨j, (Sheaf.H.equiv₀ _ terminalIsTerminal).symm
      ((S.F j).obj.map (hWf.from (⊤_ _)).op t), (Sheaf.H.equiv₀ _ terminalIsTerminal).injective ?_⟩
    have hx : Sheaf.H.equiv₀ _ terminalIsTerminal x =
        S.L.pt.obj.map (hW.from (⊤_ _)).op ((S.stageMap f).hom.app (op T₀) t) := by
      rw [ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        terminal.hom_ext (hW.from (⊤_ _) ≫ terminal.from _) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]
      rfl
    rw [equiv₀_toLimitH, AddEquiv.apply_symm_apply, hx]
    simp only [stageMap, limitComparison, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply, lowerStar_map_hom_app,
      lowerStarComp_hom_app_hom_app]
    rfl
  · sorry

end Zero

end AlgebraicGeometry.Etale.SystemData
