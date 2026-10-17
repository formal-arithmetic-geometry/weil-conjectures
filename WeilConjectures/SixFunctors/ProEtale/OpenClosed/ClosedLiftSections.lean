/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence

/-!
# Sections over henselian lifts of weakly contractible objects

Let `X = Spec A`, `i : Z = Spec (A ⧸ I) ⟶ X` and `j : U ⟶ X` a quasi-compact open immersion onto
the complement. Let `C̄` be an ind-étale `A ⧸ I`-algebra all of whose faithfully flat ind-étale
covers split (e.g. a w-contractible one), and `W = Spec H_A(C̄)` its henselian lift
(`Algebra.ClosedLift`). Then:

* every faithfully flat ind-étale cover of `H_A(C̄)` splits
  (`Algebra.ClosedLift.exists_retraction`), so `W` is weakly contractible
  (`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction`);
* every nonempty clopen subset of `W` meets the closed fibre, so `j_! N` has no sections over
  `W` (`AlgebraicGeometry.ProEtale.subsingleton_openImmersionLowerShriek_closedLiftSpec`);
* consequently the unit `F(W) ⟶ (i^* F)(W ×_X Z)` is bijective
  (`AlgebraicGeometry.ProEtale.bijective_unit_app_closedLiftSpec`), part (1) of blueprint
  `det-sf-open-closed-pullback-limits`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A surjective weakly étale morphism from an affine scheme to `Spec R` has a section, if every
faithfully flat ind-étale `R`-algebra has a retraction. -/
lemma exists_comp_eq_id_of_forall_exists_retraction {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ Spec R) [WeaklyEtale p] [Surjective p] :
    ∃ s : Spec R ⟶ Y, s ≫ p = 𝟙 _ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ Γ(Y, ⊤), Spec.map φ = Y.isoSpec.inv ≫ p :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have : WeaklyEtale (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Surjective (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, ‹_›⟩
  obtain ⟨T, _, g, hg, hgff, hgφ⟩ := ((WeaklyEtale.Spec_iff φ).1 ‹_›).exists_indEtale_comp
  algebraize [g.comp φ.hom]
  have : Algebra.IndEtale R T := by
    rwa [← RingHom.IndEtale.algebraMap_iff]
  have : Module.FaithfullyFlat R T := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hff hgff
  obtain ⟨r, hr⟩ := hR T
  refine ⟨Spec.map (CommRingCat.ofHom (r.comp g)) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact RingHom.congr_fun hr x

namespace Scheme.ProEt

variable {T : Scheme.{u}}

/-- Let `W ≅ Spec R` be an object of the small pro-étale site, where every faithfully flat
ind-étale `R`-algebra has a retraction. Every covering sieve of `W` contains the inclusions of a
cover of `W` by pairwise disjoint open subschemes. -/
lemma exists_disjoint_opens_of_forall_exists_retraction {W : T.ProEt} {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) {S : Sieve W} (hS : S ∈ topology T W) :
    ∃ (κ : Type u) (O : κ → W.left.Opens), (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧
      (∀ x, ∃ i, x ∈ O i) ∧ ∀ i, S (ofOpenImmersionHom W (O i).ι) := by
  obtain ⟨P, hP, hPS⟩ := mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (mem_precoverage_iff.1 hP)
  have : IsAffine W.left := .of_isIso e.hom
  obtain ⟨𝒱, g, _, _⟩ := Cover.QuasiCompact.exists_hom.{u + 1, u} 𝒰
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget T ⋙ CategoryTheory.Over.forget T) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  let ε : ULift.{u} (Fin (Nat.card 𝒱.I₀)) ≃ 𝒱.I₀ := Equiv.ulift.trans (Finite.equivFin _).symm
  let v (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) := 𝒱.f (ε k)
  have : WeaklyEtale (Sigma.desc v) := IsZariskiLocalAtSource.sigmaDesc fun k ↦ 𝒱.map_prop _
  have : Surjective (Sigma.desc v) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, hk⟩ := ε.surjective (𝒱.idx x)
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [v]
    rw [hk]
    exact 𝒱.covers x
  obtain ⟨s', hs'⟩ := exists_comp_eq_id_of_forall_exists_retraction hR (Sigma.desc v ≫ e.hom)
  let s := e.hom ≫ s'
  have hs : s ≫ Sigma.desc v = 𝟙 _ := by
    rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hs']
    simp
  let V (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) : Scheme.{u} := Spec (𝒱.X (ε k))
  let O (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) : W.left.Opens := s ⁻¹ᵁ (Sigma.ι V k).opensRange
  have hO (k) : Set.range ((O k).ι ≫ s).base ⊆ Set.range (Sigma.ι V k).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨_, O, fun k l hkl ↦ ?_, fun x ↦ ?_, fun k ↦ ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hk, hl⟩
    exact (disjoint_opensRange_sigmaι V k l hkl).le_bot ⟨hk, hl⟩
  · obtain ⟨k, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    exact ⟨k, ⟨y, hy⟩⟩
  · -- the inclusion of `O k` factors through `v k`, hence lies in `S`
    let c := IsOpenImmersion.lift (Sigma.ι V k) ((O k).ι ≫ s) (hO k)
    have hc : c ≫ v k = (O k).ι := by
      have : c ≫ Sigma.ι V k = (O k).ι ≫ s := IsOpenImmersion.lift_fac _ _ _
      rw [← Sigma.ι_desc v k, ← Category.assoc, this, Category.assoc, hs, Category.comp_id]
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : (ofOpenImmersion W (O k).ι).left ⟶ (Z (g.s₀ (ε k))).left :=
      c ≫ g.h₀ (ε k) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (ε k))).left = (ofOpenImmersionHom W (O k).ι).left := by
      rw [ha', Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, g.w₀]
      exact hc
    have hb : ofOpenImmersionHom W (O k).ι = MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (g.s₀ (ε k))), ← Category.assoc, hd]
        exact MorphismProperty.Over.w (ofOpenImmersionHom W (O k).ι)) ≫ a (g.s₀ (ε k)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hb]
    exact S.downward_closed (hPS _ _ (ha _)) _

/-- **Stacks 0990**, variant: an object of the small pro-étale site whose underlying scheme is
`Spec R`, where every faithfully flat ind-étale `R`-algebra has a retraction, is weakly
contractible. -/
theorem isWeaklyContractible_of_forall_exists_retraction {W : T.ProEt} {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) : (topology T).IsWeaklyContractible.{w} W := by
  refine GrothendieckTopology.isWeaklyContractible_of_forall_mem.{w, u} fun S hS ↦ ?_
  obtain ⟨κ, O, hdisj, hcov, hO⟩ := exists_disjoint_opens_of_forall_exists_retraction hR e hS
  refine ⟨κ, fun k ↦ ofOpenImmersion W (O k).ι, fun k ↦ ofOpenImmersionHom W (O k).ι,
    mem_topology_of_openImmersion _ (fun k ↦ (O k).ι) (fun x ↦ ?_)
      (fun k ↦ Sieve.ofArrows_mk _ _ k), hO, fun k ↦ ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hcov x
    exact ⟨k, by rw [Opens.range_ι]; exact hk⟩
  · refine (ProEt.forget T ⋙ CategoryTheory.Over.forget T).mono_of_mono_map ?_
    exact inferInstanceAs (Mono (O k).ι)
  · intro k l hkl Y a b hab
    have : IsEmpty Y.left := by
      refine ⟨fun z ↦ ?_⟩
      have hab' : a.left ≫ (O k).ι = b.left ≫ (O l).ι := congrArg (fun g ↦ g.left) hab
      have hk : (a.left ≫ (O k).ι).base z ∈ O k :=
        (Opens.range_ι (O k)).subset ⟨a.left z, rfl⟩
      have hl : (a.left ≫ (O k).ι).base z ∈ O l := by
        rw [hab']
        exact (Opens.range_ι (O l)).subset ⟨b.left z, rfl⟩
      exact (disjoint_iff.1 (hdisj k l hkl)).le ⟨hk, hl⟩
    exact bot_mem_topology Y

end Scheme.ProEt

open Scheme

namespace ProEtale

variable {A : CommRingCat.{u}} (I : Ideal A) (C : Type u) [CommRing C] [Algebra (A ⧸ I) C]
  [Algebra A C] [IsScalarTower A (A ⧸ I) C]

/-- The henselian lift `W = Spec H_A(C̄)` of `Algebra.ClosedLift`, as an object of the small
pro-étale site of `Spec A` (blueprint `def-exc-closed-site-lift`). -/
noncomputable def closedLiftSpec (A : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra A C] :
    (Spec A).ProEt :=
  Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Algebra.ClosedLift A C))))

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec A`. -/
noncomputable abbrev closedSpecι : Spec (.of (A ⧸ I)) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

variable {I C}

/-- Every nonempty open and closed subscheme of the henselian lift `Spec H_A(C̄)` contains a point
lying over the closed subscheme `Spec (A ⧸ I)`. -/
lemma exists_mem_range_closedSpecι_of_isClopen [Algebra.IndEtale (A ⧸ I) C]
    {s : Set (closedLiftSpec A C).left} (hs : IsClopen s) (hne : s.Nonempty) :
    ∃ x ∈ s, (closedLiftSpec A C).hom.base x ∈ Set.range (closedSpecι I).base := by
  obtain ⟨q, hq⟩ := Algebra.ClosedLift.exists_comap_mem_of_isClopen (A := A) (C := C) hs hne
  refine ⟨_, hq, PrimeSpectrum.comap (algebraMap (A ⧸ I) C) q, ?_⟩
  change PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap (algebraMap (A ⧸ I) C) q) =
    PrimeSpectrum.comap (algebraMap A (Algebra.ClosedLift A C))
      (PrimeSpectrum.comap (Algebra.ClosedLift.toAlgHom A C : Algebra.ClosedLift A C →+* C) q)
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext a
  simp [IsScalarTower.algebraMap_apply A (A ⧸ I) C, Ideal.Quotient.algebraMap_eq]

variable {R : Type (u + 1)} [Ring R] {U : Scheme.{u}} (j : U ⟶ Spec A) [IsOpenImmersion j]

/-- **Extension by zero has no sections over henselian lifts.** If every faithfully flat
ind-étale `C̄`-algebra has a retraction, the extension by zero `j_! N` along an open immersion
`j` missing `Spec (A ⧸ I)` has no nonzero sections over `W = Spec H_A(C̄)`. Every covering of
`W` is refined by a decomposition of `W` into disjoint open and closed pieces; each nonempty
piece meets `Spec (A ⧸ I)`, so it does not map to `U` and the presheaf extension by zero
vanishes on it. -/
theorem subsingleton_openImmersionLowerShriek_closedLiftSpec [Algebra.IndEtale (A ⧸ I) C]
    (hC : ∀ (T : Type u) [CommRing T] [Algebra C T] [Algebra.IndEtale C T]
      [Module.FaithfullyFlat C T], ∃ f : T →+* C, f.comp (algebraMap C T) = RingHom.id C)
    (hj : Disjoint (Set.range j.base) (Set.range (closedSpecι I).base))
    (N : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) :
    Subsingleton (((j)_!open[ModuleCat.{u + 1} R].obj N).obj.obj (op (closedLiftSpec A C))) := by
  set W := closedLiftSpec A C
  let G := MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ (inferInstance : WeaklyEtale j)
  let P := G.op.lan.obj N.obj
  let F : Sheaf (ProEt.topology (Spec A)) (ModuleCat.{u + 1} R) :=
    (presheafToSheaf (ProEt.topology (Spec A)) _).obj P
  change Subsingleton (F.obj.obj (op W))
  have hH := Algebra.ClosedLift.exists_retraction (A := A) (C := C) I hC
  suffices h0 : ∀ x : F.obj.obj (op W), x = 0 from
    ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  intro x
  obtain ⟨κ, O, hdisj, hcov, hO⟩ :=
    Scheme.ProEt.exists_disjoint_opens_of_forall_exists_retraction
      (R := CommRingCat.of (Algebra.ClosedLift A C)) hH (Iso.refl W.left)
      (Presheaf.imageSieve_mem (ProEt.topology (Spec A))
        (toSheafify (ProEt.topology (Spec A)) P) x)
  have hloc : ∀ k, F.obj.map (Scheme.ProEt.ofOpenImmersionHom W (O k).ι).op x = 0 := by
    intro k
    obtain ⟨t, ht⟩ := hO k
    by_cases hk : (O k : Set W.left).Nonempty
    · -- the presheaf extension by zero vanishes on a piece meeting the closed fibre
      have hclopen : IsClopen (O k : Set W.left) := by
        refine ⟨⟨?_⟩, (O k).isOpen⟩
        have : (O k : Set W.left)ᶜ = ⋃ l ∈ {l | l ≠ k}, (O l : Set W.left) := by
          ext x
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
          refine ⟨fun hx ↦ ?_, fun ⟨l, hl, hx⟩ hx' ↦
            (disjoint_iff.1 (hdisj l k hl)).le ⟨hx, hx'⟩⟩
          obtain ⟨l, hl⟩ := hcov x
          exact ⟨l, fun h ↦ hx (h ▸ hl), hl⟩
        rw [this]
        exact isOpen_biUnion fun l _ ↦ (O l).isOpen
      obtain ⟨z, hz, hzZ⟩ := exists_mem_range_closedSpecι_of_isClopen (I := I) hclopen hk
      have : IsEmpty (CostructuredArrow G.op
          (op (Scheme.ProEt.ofOpenImmersion W (O k).ι))) := by
        refine ⟨fun g ↦ ?_⟩
        obtain ⟨y, rfl⟩ : z ∈ Set.range (O k).ι.base := by rw [Opens.range_ι]; exact hz
        have hw := MorphismProperty.Over.w g.hom.unop
        have hy : W.hom.base ((O k).ι.base y) ∈ Set.range j.base := by
          have := congrArg (fun φ ↦ φ.base y) hw
          simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
          refine ⟨(g.left.unop.hom.base (g.hom.unop.left.base y)), ?_⟩
          exact this
        exact (Set.disjoint_iff.1 hj) ⟨hy, hzZ⟩
      have hc := G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit N.obj
        (op (Scheme.ProEt.ofOpenImmersion W (O k).ι))
      have hz0 : IsZero (P.obj (op (Scheme.ProEt.ofOpenImmersion W (O k).ι))) := by
        rw [IsZero.iff_id_eq_zero]
        exact hc.hom_ext fun g ↦ isEmptyElim g
      rw [← ht, ModuleCat.subsingleton_of_isZero hz0 |>.elim t 0, map_zero]
    · -- sections over the empty scheme vanish
      have : IsEmpty (Scheme.ProEt.ofOpenImmersion W (O k).ι).left := by
        refine ⟨fun y ↦ hk ⟨(O k).ι.base y, ?_⟩⟩
        rw [← Opens.range_ι (O k)]
        exact ⟨y, rfl⟩
      have := Scheme.ProEt.isTerminalSectionsOfIsEmpty F
        (Scheme.ProEt.ofOpenImmersion W (O k).ι)
      exact (ModuleCat.subsingleton_of_isZero this.isZero).elim _ _
  have hS : Sieve.ofArrows _ (fun k ↦ Scheme.ProEt.ofOpenImmersionHom W (O k).ι) ∈
      ProEt.topology (Spec A) W :=
    Scheme.ProEt.mem_topology_of_openImmersion _ (fun k ↦ (O k).ι)
      (fun x ↦ by obtain ⟨k, hk⟩ := hcov x; exact ⟨k, by rw [Opens.range_ι]; exact hk⟩)
      (fun k ↦ Sieve.ofArrows_mk _ _ k)
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (forget (ModuleCat.{u + 1} R)) F.property) _ hS
  rw [← Presieve.isSheafFor_iff_generate] at hsh
  refine hsh.isSeparatedFor.ext fun _ _ ⟨k⟩ ↦ ?_
  change F.obj.map _ x = F.obj.map _ 0
  rw [hloc k, map_zero]

/-- Sections over a weakly contractible object are exact: an epimorphism of sheaves of modules is
surjective on sections over it. -/
lemma surjective_app_of_isWeaklyContractible {T : Scheme.{u}} {W : T.ProEt}
    (hW : (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    {F G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op W)) :=
  hW ((sheafCompose _ (forget _)).map φ)
    ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).1
      ((Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance))

variable [QuasiCompact j]

/-- Blueprint `det-sf-open-closed-pullback-limits`, part (1): let `i : Spec (A ⧸ I) ⟶ Spec A` have
quasi-compact open complement `j`, and let `C̄` be an ind-étale `A ⧸ I`-algebra all of whose
faithfully flat ind-étale covers split (e.g. a w-contractible one). For every pro-étale sheaf
of modules `F` on `Spec A`, the unit of `i^* ⊣ i_*` gives a bijection
`F(v(V)) ≅ (i^* F)(v(V) ×_X Z)` for the henselian lift `v(V) = Spec H_A(C̄)` of `V = Spec C̄`
(and `v(V) ×_X Z ≅ V` by `Algebra.ClosedLift.bijective_reduction`).

The open–closed sequence `0 ⟶ j_! j^* F ⟶ F ⟶ i_* i^* F ⟶ 0` stays exact on sections over the
weakly contractible `v(V)`, and `j_! j^* F` has no sections there
(`AlgebraicGeometry.ProEtale.subsingleton_openImmersionLowerShriek_closedLiftSpec`). -/
theorem bijective_unit_app_closedLiftSpec [Algebra.IndEtale (A ⧸ I) C]
    (hC : ∀ (T : Type u) [CommRing T] [Algebra C T] [Algebra.IndEtale C T]
      [Module.FaithfullyFlat C T], ∃ f : T →+* C, f.comp (algebraMap C T) = RingHom.id C)
    (hij : IsCompl (Set.range (closedSpecι I).base) (Set.range j.base))
    (F : Sheaf (Scheme.ProEt.topology (Spec A)) (ModuleCat.{u + 1} R)) :
    Function.Bijective
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (closedSpecι I)).unit.app F).hom.app
        (op (closedLiftSpec A C))) := by
  have hS := shortExact_openClosedShortComplex (closedSpecι I) j hij F
  set S := openClosedShortComplex R (closedSpecι I) j hij F
  let E := sheafToPresheaf (Scheme.ProEt.topology (Spec A)) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op (closedLiftSpec A C))
  have hH := Algebra.ClosedLift.exists_retraction (A := A) (C := C) I hC
  refine ⟨?_, ?_⟩
  · have hE : (S.map E).Exact := hS.exact.map_of_mono_of_preservesKernel E hS.mono_f
      inferInstance
    have hsub := subsingleton_openImmersionLowerShriek_closedLiftSpec (C := C) j
      hC hij.disjoint.symm ((j)^*[ModuleCat.{u + 1} R].obj F)
    rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨t, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1 hE s hs
    rw [@Subsingleton.elim _ hsub t 0, map_zero]
  · have := hS.epi_g
    exact surjective_app_of_isWeaklyContractible
      (Scheme.ProEt.isWeaklyContractible_of_forall_exists_retraction
        (R := CommRingCat.of (Algebra.ClosedLift A C)) hH (Iso.refl _)) S.g

end ProEtale

end AlgebraicGeometry
