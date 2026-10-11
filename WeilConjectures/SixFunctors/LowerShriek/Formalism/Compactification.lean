/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.Compactification.RefinementUniqueness
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Identity
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Pasting

/-!
# Compactly supported direct images in a compact support formalism

In a `AlgebraicGeometry.CompactSupportFormalism` `F`, a compactification `c = (X ⟶[i] Z ⟶[g] Y)`
of `f : X ⟶ Y` gives the compactly supported direct image `F.shriek c = i_! ⋙ g_*`. A refinement
`r : c.Refinement d` with cartesian square over `X` gives the comparison
`F.refinementComparison r : F.shriek d ⟶ F.shriek c`, built from the exchange map of the square
```
X --𝟙--> X
|c.i     |d.i
c.Z -r-> d.Z
```
It satisfies the identity and composition laws, and it is an isomorphism when `F` satisfies
proper base change. Comparing two compactifications through their common refinement gives
`F.shriekIso c d : F.shriek c ≅ F.shriek d`, which does not depend on the common refinement and
satisfies the cocycle condition (blueprint `sk-prop-sf-comp-coherence`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The compactly supported direct image `i_! ⋙ g_*` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`. -/
def shriek (c : Compactification f) : F.obj X ⥤ F.obj Y := F.sh c.i ⋙ F.pf c.g

section Refinement

variable [F.HasBaseChange] {c d e : Compactification f}

/-- **The comparison along a refinement** `r : c.Refinement d` whose square over `X` is
cartesian: the map `F.shriek d ⟶ F.shriek c` given by the exchange map
`(𝟙 X)_* ⋙ (d.i)_! ⟶ (c.i)_! ⋙ (r.hom)_*` followed by `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*`. -/
noncomputable def refinementComparison (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) : F.shriek d ⟶ F.shriek c :=
  haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pfId X).inv (F.shriek d) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (F.exchange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans (F.pf d.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.sh c.i) (F.pfComp' r.hom d.g c.g r.hom_g).inv

lemma refinementComparison_app (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : F.obj X) :
    haveI := HasBaseChange.isIso_baseChange (F := F) hr.flip
    (F.refinementComparison r hr).app K =
      (F.pf d.g).map ((F.sh d.i).map ((F.pfId X).inv.app K) ≫
          (F.exchange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K) ≫
        (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K) := by
  simp [refinementComparison, shriek]


/-- **The identity law**: the comparison along a refinement whose map is the identity is the
identity. -/
lemma refinementComparison_eq_id (r : c.Refinement c) (hr : IsPullback c.i (𝟙 X) r.hom c.i)
    (h : r.hom = 𝟙 c.Z) : F.refinementComparison r hr = 𝟙 _ := by
  obtain ⟨hom, i_hom, hom_g⟩ := r
  subst h
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  ext K
  have h₁ := congr_app (F.exchange_id_horiz c.i hr.flip.w) K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Functor.comp_obj, Functor.id_obj] at h₁
  rw [refinementComparison_app, h₁, Category.comp_id, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [F.pfComp'_id_left_inv_app, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rfl


/-- **The composition law**: the comparison along a composite of refinements is the composite of
the comparisons, in the opposite order. -/
lemma refinementComparison_comp (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    F.refinementComparison (r.comp s) (Compactification.Refinement.isPullback_comp r s hr hs) =
      F.refinementComparison s hs ≫ F.refinementComparison r hr := by
  have hrs := Compactification.Refinement.isPullback_comp r s hr hs
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have := HasBaseChange.isIso_baseChange (F := F) hs.flip
  have := HasBaseChange.isIso_baseChange (F := F) hrs.flip
  ext K
  have hpaste := congr_app (F.exchange_paste_horiz (𝟙 X) (𝟙 X) c.i d.i e.i r.hom s.hom (𝟙 X)
    (r.comp s).hom hr.flip.w hs.flip.w (Category.id_comp _) rfl hrs.flip.w) K
  have hassoc := congr_app (F.pfComp'_assoc r.hom s.hom e.g (r.comp s).hom d.g c.g rfl s.hom_g
    (r.comp s).hom_g) ((F.sh c.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj]
    at hpaste hassoc
  have hnat := congrArg (F.pf e.g).map
    ((F.exchange (𝟙 X) d.i e.i s.hom hs.flip.w).natTrans.naturality ((F.pfId X).inv.app K))
  have hnat2 := (F.pfComp' s.hom e.g d.g s.hom_g).inv.naturality
    ((F.sh d.i).map ((F.pfId X).inv.app K) ≫
      (F.exchange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K)
  have hassoc' : (F.pfComp' s.hom e.g d.g s.hom_g).inv.app ((F.pf r.hom).obj ((F.sh c.i).obj K)) ≫
      (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K) =
      (F.pf e.g).map ((F.pfComp' r.hom s.hom (r.comp s).hom
          (Compactification.Refinement.comp_hom r s).symm).inv.app ((F.sh c.i).obj K)) ≫
        (F.pfComp' (r.comp s).hom e.g c.g (r.comp s).hom_g).inv.app ((F.sh c.i).obj K) := by
    rw [← cancel_epi ((F.pfComp' s.hom e.g d.g s.hom_g).hom.app
        ((F.pf r.hom).obj ((F.sh c.i).obj K))),
      ← cancel_epi ((F.pfComp' r.hom d.g c.g r.hom_g).hom.app ((F.sh c.i).obj K))]
    simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rw [← reassoc_of% hassoc]
    simp [← Functor.map_comp_assoc]
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at hnat hnat2
  rw [NatTrans.comp_app, refinementComparison_app, refinementComparison_app,
    refinementComparison_app, hpaste, F.pfComp'_id_left_hom_app]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hnat2, hassoc', reassoc_of% hnat]

/-- **The comparison along a refinement, through a base change isomorphism**: if the base change
map of the square of `r` is `β : c.i_! ≅ d.i_! ⋙ r^*` up to `(𝟙 X)^* ≅ 𝟭`, then the comparison
along `r` is the unit of `r^* ⊣ r_*`, followed by `β⁻¹` and by `r_* ⋙ (d.g)_* ≅ (c.g)_*`. -/
lemma refinementComparison_eq_of_baseChange (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (β : F.sh c.i ≅ F.sh d.i ⋙ F.pb r.hom)
    (hβ : (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans =
      Functor.whiskerRight (F.pbId X).hom (F.sh c.i) ≫ (Functor.leftUnitor _).hom ≫ β.hom) :
    F.refinementComparison r hr =
      Functor.whiskerRight (Functor.whiskerLeft (F.sh d.i) (F.adj r.hom).unit) (F.pf d.g) ≫
        Functor.whiskerRight β.inv (F.pf r.hom ⋙ F.pf d.g) ≫
        Functor.whiskerLeft (F.sh c.i) (F.pfComp' r.hom d.g c.g r.hom_g).inv := by
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have hinv : inv (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans =
      β.inv ≫ (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pbId X).inv (F.sh c.i) := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    rw [hβ]
    ext K
    simp [← Functor.map_comp]
  ext K
  have key : (F.sh d.i).map ((F.pfId X).inv.app K) ≫
      (F.exchange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans.app K =
      (F.adj r.hom).unit.app ((F.sh d.i).obj K) ≫ (F.pf r.hom).map (β.inv.app K) := by
    have hc := conjugateEquiv_counit Adjunction.id (F.adj (𝟙 X)) (F.pbId X).hom K
    rw [← pfId_inv] at hc
    simp only [exchange, mateEquiv_apply, hinv, NatTrans.comp_app]
    dsimp [TwoSquare.natTrans]
    simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
    have hc' : (F.pbId X).inv.app ((F.pf (𝟙 X)).obj K) ≫ (F.adj (𝟙 X)).counit.app K =
        (F.pfId X).hom.app K := by
      rw [← cancel_epi ((F.pfId X).inv.app K)]
      erw [(F.pbId X).inv.naturality_assoc, hc]
      simp
    simp only [← Functor.map_comp, hc']
    rw [← β.inv.naturality, Functor.map_comp, Functor.comp_map, Adjunction.unit_naturality_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [refinementComparison_app, key]
  simp


end Refinement


section ProperExchange

variable [F.HasProperExchange] {c d e : Compactification f}

instance isIso_refinementComparison (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) : IsIso (F.refinementComparison r hr) := by
  have := HasBaseChange.isIso_baseChange (F := F) hr.flip
  have := HasProperExchange.isIso_exchange (F := F) hr.flip
  unfold refinementComparison
  infer_instance

/-- Equal refinements give equal comparisons. -/
lemma asIso_refinementComparison_congr {r r' : c.Refinement d} (h : r = r')
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hr' : IsPullback c.i (𝟙 X) r'.hom d.i) :
    asIso (F.refinementComparison r hr) = asIso (F.refinementComparison r' hr') := by
  subst h
  rfl

lemma asIso_refinementComparison_comp (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    asIso (F.refinementComparison (r.comp s)
        (Compactification.Refinement.isPullback_comp r s hr hs)) =
      asIso (F.refinementComparison s hs) ≪≫ asIso (F.refinementComparison r hr) := by
  ext : 1
  exact F.refinementComparison_comp r s hr hs

/-- Comparing through a common refinement `e` gives the same isomorphism as comparing through
any further refinement of `e`. -/
lemma refinementComparison_trans_eq_of_refinement {c d e e' : Compactification f}
    (r : e.Refinement c) (s : e.Refinement d)
    (hr : IsPullback e.i (𝟙 X) r.hom c.i) (hs : IsPullback e.i (𝟙 X) s.hom d.i)
    (t : e'.Refinement e) (ht : IsPullback e'.i (𝟙 X) t.hom e.i) :
    asIso (F.refinementComparison r hr) ≪≫ (asIso (F.refinementComparison s hs)).symm =
      asIso (F.refinementComparison (t.comp r)
          (Compactification.Refinement.isPullback_comp t r ht hr)) ≪≫
        (asIso (F.refinementComparison (t.comp s)
          (Compactification.Refinement.isPullback_comp t s ht hs))).symm := by
  rw [F.asIso_refinementComparison_comp t r ht hr, F.asIso_refinementComparison_comp t s ht hs]
  ext : 1
  simp

variable [QuasiCompact f]

/-- **The comparison of two compactifications**: the isomorphism `F.shriek c ≅ F.shriek d`
obtained through the common refinement `Compactification.inf c d`. -/
noncomputable def shriekIso (c d : Compactification f) : F.shriek c ≅ F.shriek d :=
  asIso (F.refinementComparison (Compactification.infFst c d)
      (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (F.refinementComparison (Compactification.infSnd c d)
      (Compactification.isPullback_infSnd c d))).symm

/-- **Independence of the common refinement**: comparing `c` and `d` through any common
refinement with cartesian squares over `X` gives `F.shriekIso c d`. -/
theorem shriekIso_eq (r : e.Refinement c) (s : e.Refinement d)
    (hr : IsPullback e.i (𝟙 X) r.hom c.i) (hs : IsPullback e.i (𝟙 X) s.hom d.i) :
    F.shriekIso c d =
      asIso (F.refinementComparison r hr) ≪≫ (asIso (F.refinementComparison s hs)).symm := by
  set e' := Compactification.inf c d
  have hdense := Compactification.isSchemeTheoreticallyDominant_inf_i e e'
  rw [shriekIso, F.refinementComparison_trans_eq_of_refinement r s hr hs
      (Compactification.infFst e e') (Compactification.isPullback_infFst e e'),
    F.refinementComparison_trans_eq_of_refinement _ _
      (Compactification.isPullback_infFst c d) (Compactification.isPullback_infSnd c d)
      (Compactification.infSnd e e') (Compactification.isPullback_infSnd e e'),
    F.asIso_refinementComparison_congr
      (Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant hdense
        ((Compactification.infSnd e e').comp (Compactification.infFst c d))
        ((Compactification.infFst e e').comp r)),
    F.asIso_refinementComparison_congr
      (Compactification.Refinement.ext_of_isSchemeTheoreticallyDominant hdense
        ((Compactification.infSnd e e').comp (Compactification.infSnd c d))
        ((Compactification.infFst e e').comp s))]

/-- For a refinement `r : c.Refinement d` with cartesian square, `F.shriekIso c d` is the inverse
of the comparison along `r`. -/
theorem shriekIso_eq_symm (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    F.shriekIso c d = (asIso (F.refinementComparison r hr)).symm := by
  have hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i := by
    rw [Compactification.Refinement.id_hom]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  rw [F.shriekIso_eq (Compactification.Refinement.id c) r hid hr]
  ext : 1
  simp [F.refinementComparison_eq_id _ hid rfl]

@[simp]
theorem shriekIso_refl (c : Compactification f) : F.shriekIso c c = Iso.refl _ := by
  rw [F.shriekIso_eq (Compactification.infFst c c) (Compactification.infFst c c)
    (Compactification.isPullback_infFst c c) (Compactification.isPullback_infFst c c)]
  ext : 1
  simp

/-- **The cocycle condition.** -/
theorem shriekIso_trans (c₁ c₂ c₃ : Compactification f) :
    F.shriekIso c₁ c₂ ≪≫ F.shriekIso c₂ c₃ = F.shriekIso c₁ c₃ := by
  set e₁₂ := Compactification.inf c₁ c₂
  have h₁ := Compactification.Refinement.isPullback_comp (Compactification.infFst e₁₂ c₃)
    (Compactification.infFst c₁ c₂) (Compactification.isPullback_infFst e₁₂ c₃)
    (Compactification.isPullback_infFst c₁ c₂)
  have h₂ := Compactification.Refinement.isPullback_comp (Compactification.infFst e₁₂ c₃)
    (Compactification.infSnd c₁ c₂) (Compactification.isPullback_infFst e₁₂ c₃)
    (Compactification.isPullback_infSnd c₁ c₂)
  have h₃ := Compactification.isPullback_infSnd e₁₂ c₃
  rw [F.shriekIso_eq _ _ h₁ h₂, F.shriekIso_eq _ _ h₂ h₃, F.shriekIso_eq _ _ h₁ h₃]
  ext : 1
  simp

theorem shriekIso_symm (c d : Compactification f) :
    (F.shriekIso c d).symm = F.shriekIso d c := by
  have h := F.shriekIso_trans c d c
  rw [shriekIso_refl] at h
  ext : 1
  rw [Iso.symm_hom, ← cancel_epi (F.shriekIso c d).hom, Iso.hom_inv_id]
  exact (congrArg Iso.hom h).symm

end ProperExchange

end AlgebraicGeometry.CompactSupportFormalism
