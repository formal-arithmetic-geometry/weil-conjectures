/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.Paper.WeilTensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteFiniteProjectiveLift
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Local shortening of finite-projective complexes -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

private theorem map_cycles_retract_of_section
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (P : CochainComplex A ℤ) (n : ℤ)
    (s : F.obj (P.cycles (n + 1)) ⟶ F.obj (P.X n))
    (hs : s ≫ F.map (P.toCycles n (n + 1)) = 𝟙 _) :
    Nonempty (Retract (F.obj (P.cycles n)) (F.obj (P.X n))) := by
  let k := F.map (P.iCycles n)
  let f := F.map (P.toCycles n (n + 1))
  have hif : k ≫ f = 0 := by
    rw [← F.map_comp]
    have h : P.iCycles n ≫ P.toCycles n (n + 1) = 0 := by
      rw [← cancel_mono (P.iCycles (n + 1)), Category.assoc]
      simp
    rw [h, F.map_zero]
  have hd : (𝟙 _ - f ≫ s) ≫ F.map (P.d n (n + 1)) = 0 := by
    rw [← P.toCycles_i n (n + 1), F.map_comp]
    change (𝟙 _ - f ≫ s) ≫ (f ≫ F.map (P.iCycles (n + 1))) = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      ← Category.assoc s f, hs]
    simp
  let hc := KernelFork.mapIsLimit _ (P.cyclesIsKernel n (n + 1) (by simp)) F
  let r := hc.lift (KernelFork.ofι (𝟙 _ - f ≫ s) hd)
  have hr : r ≫ k = 𝟙 _ - f ≫ s := hc.fac _ WalkingParallelPair.zero
  have : Mono k := inferInstanceAs (Mono (F.map (P.iCycles n)))
  refine ⟨⟨k, r, ?_⟩⟩
  rw [← cancel_mono k, Category.assoc, hr]
  simp [Preadditive.comp_sub, ← Category.assoc, hif]

private theorem locally_finiteFree_retract_cycles
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (P : CochainComplex (SheafOfModules.{max u v} (R.over U)) ℤ)
    (p : StrictPerfectCoefficientPackageOnSite (R.over U) P)
    (b : ℤ) (hexact : ∀ j : ℤ, b < j → IsZero (P.homology j))
    (n : ℕ) (j : ℤ) (hj : b ≤ j)
    (hb : ∀ k : ℤ, j + n < k → IsZero (P.X k)) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
      ∃ m : ℕ, Nonempty (Retract ((overMap.{max u v} R f).obj (P.cycles j))
        (∏ᶜ fun _ : Fin m ↦ unit (R.over V))) := by
  classical
  induction n generalizing j with
  | zero =>
    have hd : P.d j (j + 1) = 0 := (hb (j + 1) (by omega)).eq_of_tgt _ _
    let h := Retract.ofIso (P.iCyclesIso j (j + 1) (by simp) hd)
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V f _
    let F := overMap.{max u v} R f
    have : PreservesFiniteLimits F := (overMap_exact_ofUniverses R f).1
    let q := p.map F (overMapUnitIso f)
    exact ⟨p.N j, ⟨(h.map F).trans ⟨q.i j, q.p j, q.splitting j⟩⟩⟩
  | succ n ih =>
    obtain ⟨S, hS, h⟩ := ih (j + 1) (by omega) (fun k hk ↦ hb k (by omega))
    have hs : (P.sc' j (j + 1) (j + 2)).Exact :=
      (P.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp; omega)).mp
        ((P.exactAt_iff_isZero_homology (j + 1)).mpr (hexact _ (by omega)))
    have : Epi (P.sc' j (j + 1) (j + 2)).toCycles := hs.epi_toCycles
    let e := P.cyclesIsoSc' j (j + 1) (j + 2) (by simp) (by simp; omega)
    have he : Epi (P.toCycles j (j + 1) ≫ e.hom) := by
      rw [P.toCycles_cyclesIsoSc'_hom j (j + 1) (j + 2) (by simp) (by simp; omega)]
      infer_instance
    have : Epi (P.toCycles j (j + 1)) := by
      have : Epi ((P.toCycles j (j + 1) ≫ e.hom) ≫ e.inv) := inferInstance
      simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using this
    have hlocal (V : C) (f : V ⟶ U) (hf : S f) :
        ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g →
          ∃ m : ℕ, Nonempty (Retract ((overMap.{max u v} R (g ≫ f)).obj (P.cycles j))
            (∏ᶜ fun _ : Fin m ↦ unit (R.over W))) := by
      obtain ⟨m, ⟨r⟩⟩ := h V f hf
      let F := overMap.{max u v} R f
      have : PreservesFiniteLimits F := (overMap_exact_ofUniverses R f).1
      have : PreservesFiniteColimits F := (overMap_exact_ofUniverses R f).2
      obtain ⟨T, hT, ht⟩ := exists_local_section_overMap_of_finiteFree_retract
        R V (F.map (P.toCycles j (j + 1))) m r.i r.r r.retract
      refine ⟨T, hT, ?_⟩
      intro W g hg
      obtain ⟨s, hs⟩ := ht W g hg
      let G := overMap.{max u v} R g
      have : PreservesFiniteLimits G := (overMap_exact_ofUniverses R g).1
      obtain ⟨r'⟩ := map_cycles_retract_of_section (F ⋙ G) P j s hs
      let q := p.map (F ⋙ G) (G.mapIso (overMapUnitIso f) ≪≫ overMapUnitIso g)
      let c := (sitePerfectOverMapComp R f g).app (P.cycles j)
      exact ⟨p.N j, ⟨(Retract.ofIso c.symm).trans
        (r'.trans ⟨q.i j, q.p j, q.splitting j⟩)⟩⟩
    choose T hT ht using hlocal
    refine ⟨Sieve.bind S (fun {V} {f} hf ↦ T V f hf),
      J.bind_covering hS (fun _ _ hf ↦ hT _ _ hf), ?_⟩
    intro V f hf
    obtain ⟨W, g, h, hh, hg, rfl⟩ := hf
    exact ht W h hh V g hg

/-- Upper cohomological bounds can be realized by locally bounded finite-projective
models of a site-perfect object.

Source: Stacks Project, Cohomology on Sites, Tag 08FX, proof of (1), the descending
shortening induction

Proof: Choose the bounded finite-free-retract models in the definition of perfectness.
For a top degree n > b, cohomological vanishing makes the incoming differential epic.
Locally lift the finitely many generators of a finite free module retracting onto the
last term. Compose the lift with the retract inclusion to obtain a section of the
incoming differential. Its kernel is then a finite free retract, and the complex splits
as the shortened complex plus the contractible identity complex on the last term.
Remove that identity summand. Descend through the finitely many degrees above b.
Exact restriction preserves the quasi-isomorphisms, and transitivity composes the
finitely many covering refinements and the initial perfect covering. The lower bound
can move during shortening but remains finite. This includes zero top terms and
empty covering sieves.
(blueprint: lem-sf-site-perfect-upper-model). -/
theorem exists_strictPerfect_upper_model
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    [∀ U : C, HasDerivedCategory.{w'} (SheafOfModules.{max u v}
      (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R).over U))]
    (E : DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (hperfect : IsPerfectOnRingedSiteOfUniverses.{u, v, 0} R E)
    (b : ℤ)
    (hcoh : ∀ r : ℤ, b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj E)) :
    ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R V
          (ringedSiteDerivedRestrictionOfUniverses
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) V E),
          ∀ r : ℤ, b < r → IsZero (P.F.X r) := by
  classical
  let O := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  obtain ⟨K, hK, ⟨eK⟩⟩ := hperfect
  have hKcoh (r : ℤ) (hr : b < r) : IsZero (K.homology r) :=
    (hcoh r hr).of_iso
      (((DerivedCategory.homologyFunctor _ r).mapIso eK ≪≫
        (DerivedCategory.homologyFunctorFactors _ r).app K).symm)
  intro U
  obtain ⟨S, hS, hP⟩ := hK U
  have hlocal (V : C) (f : V ⟶ U) (hf : S f) :
      ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g →
        ∃ P : StrictPerfectCoefficientRepresentationOfUniverses.{u, v, 0} R W
          (ringedSiteDerivedRestrictionOfUniverses O W E),
          ∀ r : ℤ, b < r → IsZero (P.F.X r) := by
    obtain ⟨P, ⟨l, t, hbound⟩, ⟨p⟩, α, hα⟩ := hP V f hf
    have : QuasiIso α := hα
    let F := overFunctor.{max u v} O V
    have : PreservesFiniteLimits F := (overFunctor_exact_ofUniverses O V).1
    have : PreservesFiniteColimits F := (overFunctor_exact_ofUniverses O V).2
    have hex (r : ℤ) (hr : b < r) : IsZero (P.homology r) := by
      have hz : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj K).homology r) :=
        (F.map_isZero (hKcoh r hr)).of_iso ((K.sc r).mapHomologyIso F)
      exact hz.of_iso (isoOfQuasiIsoAt α r)
    obtain ⟨T, hT, hc⟩ := locally_finiteFree_retract_cycles O V P p b hex
      (t - b).toNat b (le_refl _) (fun k hk ↦ hbound k (Or.inr (by omega)))
    refine ⟨T, hT, ?_⟩
    intro W g hg
    obtain ⟨m, ⟨rc⟩⟩ := hc W g hg
    let G := overMap.{max u v} O g
    have : PreservesFiniteLimits G := (overMap_exact_ofUniverses O g).1
    have : PreservesFiniteColimits G := (overMap_exact_ofUniverses O g).2
    let L : CochainComplex (SheafOfModules.{max u v} (O.over W)) ℤ :=
      (G.mapHomologicalComplex (.up ℤ)).obj P
    let Q := L.truncLE b
    let q := p.map G (overMapUnitIso g)
    have hz (r : ℤ) (hr : b < r) : IsZero (Q.X r) :=
      CochainComplex.isZero_of_isStrictlyLE _ b r hr
    have hlow (r : ℤ) (hr : r < min l b) : IsZero (Q.X r) := by
      exact (G.map_isZero (hbound r (Or.inl (by omega)))).of_iso
        (L.truncLEXIso b r (by omega))
    have hexc (r : ℤ) (hr : b < r) : IsZero (L.homology r) :=
      (G.map_isZero (hex r hr)).of_iso ((P.sc r).mapHomologyIso G)
    have : L.IsLE b := (L.isLE_iff b).2
      (fun r hr ↦ (L.exactAt_iff_isZero_homology r).2 (hexc r hr))
    have : QuasiIso (L.ιTruncLE b) := inferInstance
    have hp (r : ℤ) : ∃ n : ℕ,
        Nonempty (Retract (Q.X r) (∏ᶜ fun _ : Fin n ↦ unit (O.over W))) := by
      obtain hr | rfl | hr := lt_trichotomy r b
      · exact ⟨p.N r, ⟨(Retract.ofIso (L.truncLEXIso b r hr)).trans
          ⟨q.i r, q.p r, q.splitting r⟩⟩⟩
      · exact ⟨m, ⟨(Retract.ofIso (L.truncLEXIsoCycles r ≪≫
          (P.sc r).mapCyclesIso G)).trans rc⟩⟩
      · exact ⟨0, ⟨(hz r hr).retract _⟩⟩
    choose n rn using hp
    let package : StrictPerfectCoefficientPackageOnSite (O.over W) Q :=
      { N := n
        i r := (rn r).some.i
        p r := (rn r).some.r
        splitting r := (rn r).some.retract }
    let H := overFunctor.{max u v} O W
    have : PreservesFiniteLimits H := (overFunctor_exact_ofUniverses O W).1
    have : PreservesFiniteColimits H := (overFunctor_exact_ofUniverses O W).2
    let eg := (Functor.mapHomologicalComplexCompIso
      (overFunctorMap O g) (.up ℤ)).app K
    let ep : ringedSiteDerivedRestrictionOfUniverses O W E ≅ DerivedCategory.Q.obj L :=
      overFunctor_derivedRestrictionIso O W E ≪≫
      H.mapDerivedCategory.mapIso eK ≪≫ H.mapDerivedCategoryFactors.app K ≪≫
      (DerivedCategory.Q.mapIso eg).symm ≪≫
      (asIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map α))).symm
    refine ⟨⟨Q, ⟨min l b, b, ?_⟩,
      ep ≪≫ (asIso (DerivedCategory.Q.map (L.ιTruncLE b))).symm, package⟩, hz⟩
    intro r hr
    exact hr.elim (hlow r) (hz r)
  choose T hT hmodel using hlocal
  refine ⟨Sieve.bind S (fun {V} {f} hf ↦ T V f hf),
    J.bind_covering hS (fun _ _ hf ↦ hT _ _ hf), ?_⟩
  intro V f hf
  obtain ⟨W, g, h, hh, hg, _⟩ := hf
  exact hmodel W h hh V g hg

end SheafOfModules
