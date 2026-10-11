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

end Refinement

end AlgebraicGeometry.CompactSupportFormalism
