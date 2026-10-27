/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenSupportCompactificationModel
import Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import Sheaf.AlgebraicGeometry.EtaleGraphRefinementNormalization
import Sheaf.SixFunctors.OpenSupportRefinementExchange

/-! # Changing the compactifications in an open-support comparison

Source: blueprint `prop-asd-smooth-base-change`, coherence (i).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem graphFromOpen_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (t : EtaleGraphPresentation f) :
    rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
      etaleGraphComparisonFromOpen A d t = etaleGraphComparisonFromOpen A c t := by
  have h := (etaleGraphComparisonBaseChange A c).2.1 d t
  have hn := (etaleGraphComparisonBaseChange A c).2.2.2.2.2.2 c d
  have hc := (etaleGraphComparisonBaseChange A c).2.2.2.1
    (EtaleGraphPresentation.ofCompactification c)
    (EtaleGraphPresentation.ofCompactification d) t
  rw [(etaleGraphComparisonBaseChange A c).2.1 c t, h, hn] at hc
  apply Iso.ext
  have he := congrArg Iso.hom hc
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] at he
  apply (cancel_epi (etaleGraphOpenNormalization A c).hom).1
  simpa only [Iso.trans_hom] using he

private theorem graphIso_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e : Compactification f) :
    rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
      openRestrictionGraphIso A d e = openRestrictionGraphIso A c e := by
  have h := congrArg (fun k ↦ k ≪≫ etaleGraphOpenNormalization A e)
    (graphFromOpen_change A c d (EtaleGraphPresentation.ofCompactification e))
  simpa only [openRestrictionGraphIso, etaleGraphComparisonFromOpen,
    EtaleGraphPresentation.ofCompactification, etaleGraphOpenNormalization,
    sfGraphCompactificationComparison, locallyClosedGraphIso,
    locallyClosedGraphSide₁, locallyClosedGraphSide₂, locallyClosedGraphMiddle,
    locallyClosedGraphV, locallyClosedGraphS₁, locallyClosedGraphS₂,
    locallyClosedGraphS₁₂, Iso.trans_assoc] using h

private theorem graphIso_eq_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    openRestrictionGraphIso A c d = rightDerivedLowerShriekOfCompactificationIso A c d := by
  have h := (etaleGraphComparisonBaseChange A c).2.1 c
    (EtaleGraphPresentation.ofCompactification d)
  rw [(etaleGraphComparisonBaseChange A c).2.2.2.2.2.2 c d] at h
  have he := congrArg (fun k ↦ (etaleGraphOpenNormalization A c).symm ≪≫ k ≪≫
    etaleGraphOpenNormalization A d) h
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
    Iso.trans_refl] at he
  change _ = openRestrictionGraphIso A c d at he
  exact he.symm

private theorem graphIso_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    openRestrictionGraphIso A d c =
      asIso (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
        r hr) := by
  have h := congrArg (fun k ↦ k ≪≫ etaleGraphOpenNormalization A c)
    (etaleGraphFromOpen_refinement A d c r hr)
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] at h
  exact h

attribute [local irreducible] openRestrictionGraphIso sfGraphCompactificationComparison
  etaleGraphComparisonFromOpen rightDerivedLowerShriekOfCompactificationIso
  openSupportPullbackIso

private theorem graphIso_comp_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (b : Compactification f) {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (openRestrictionGraphIso A b d).hom ≫
        rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr =
      (openRestrictionGraphIso A b c).hom := by
  have h := graphIso_change A b d c
  rw [← graphIso_eq_comparison, graphIso_refinement A r hr] at h
  exact congrArg Iso.hom h

private theorem support_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f)
    (b : Compactification p) :
    (openSupportCompactificationIso A sq c b).hom =
      Functor.whiskerRight (openRestrictionGraphIso A b (c.ofIsPullback sq)).hom
        D((j)_!open[ModuleCat.{u + 1} A]) ≫ (openSupportPullbackIso A sq c).hom := by
  simp only [openSupportCompactificationIso, openSupportPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom]

private theorem support_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} [QuasiCompact p] (sq : IsPullback a p f j)
    (b : Compactification p) {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (openSupportCompactificationIso A sq d b).hom ≫
        Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr) =
      (openSupportCompactificationIso A sq c b).hom := by
  rw [support_factor, support_factor, Category.assoc,
    ← openSupportPullbackIso_refinement A sq r hr, ← Category.assoc,
    ← Functor.whiskerRight_comp, graphIso_comp_refinement]

private theorem support_change_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} [QuasiCompact p] (sq : IsPullback a p f j)
    (c : Compactification f) (b d : Compactification p) :
    Functor.whiskerRight (rightDerivedLowerShriekOfCompactificationIso A b d).hom
        D((j)_!open[ModuleCat.{u + 1} A]) ≫
      (openSupportCompactificationIso A sq c d).hom =
    (openSupportCompactificationIso A sq c b).hom := by
  rw [support_factor, support_factor, ← Category.assoc, ← Functor.whiskerRight_comp]
  rw [← Iso.trans_hom, graphIso_change]

/-- Changing both supplied compactifications commutes with the open-support comparison.
Source: blueprint `prop-asd-smooth-base-change`, coherence (i), comparison of the
compactification diagram with its restriction to an open.

Proof: the existing graph-normalization and cocycle API identifies graph comparisons
with the common-refinement comparison and with the specified comparison for one
cartesian refinement. Factor each support comparison as a graph map followed by
its literal-pullback proper/open comparison. The two explicit composition triangles
(p,j) and (a,f) show that this latter comparison intertwines a refinement with its
pullback: apply general triangle-composition naturality twice and cancel their common
output compositor. Thus E(d,b) followed by the refinement map equals E(c,b).
Graph cocycles also give source-change naturality. Apply both laws to the two
projections of the actual common refinement inf(cf,df). Expand I(cf,df) as the first
projection comparison followed by the inverse of the second. Reassociate and cancel
that second comparison to obtain the displayed equation. Quasi-compactness is used
only for common refinements; empty opens and zero rings use the same identities.
(blueprint: lem-asd-open-support-compactification-naturality) -/
theorem openSupportCompactificationIso_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} [QuasiCompact p] (sq : IsPullback a p f j)
    (cf df : Compactification f) (cp dp : Compactification p) :
    Functor.whiskerRight (rightDerivedLowerShriekOfCompactificationIso Λ cp dp).hom
        D((j)_!open[ModuleCat.{u + 1} Λ]) ≫
      (openSupportCompactificationIso Λ sq df dp).hom =
    (openSupportCompactificationIso Λ sq cf cp).hom ≫
      Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ])
        (rightDerivedLowerShriekOfCompactificationIso Λ cf df).hom := by
  let A := ModuleCat.{u + 1} Λ
  let r := Compactification.inf cf df
  let rc := Compactification.infFst cf df
  let rd := Compactification.infSnd cf df
  let ec : Rf_!(cf)[ModuleCat.{u + 1} Λ] ≅ Rf_!(r)[ModuleCat.{u + 1} Λ] :=
    asIso (rightDerivedLowerShriekOfCompactificationComparison A rc
    (Compactification.isPullback_infFst cf df))
  let ed : Rf_!(df)[ModuleCat.{u + 1} Λ] ≅ Rf_!(r)[ModuleCat.{u + 1} Λ] :=
    asIso (rightDerivedLowerShriekOfCompactificationComparison A rd
    (Compactification.isPullback_infSnd cf df))
  have hc := support_refinement Λ sq cp rc (Compactification.isPullback_infFst cf df)
  have hd := support_refinement Λ sq dp rd (Compactification.isPullback_infSnd cf df)
  have hs := support_change_source Λ sq r cp dp
  change _ ≫ Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ]) ec.hom = _ at hc
  change _ ≫ Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ]) ed.hom = _ at hd
  conv_rhs => rw [rightDerivedLowerShriekOfCompactificationIso]
  change _ = _ ≫ Functor.whiskerLeft D((a)_!open[A]) (ec.hom ≫ ed.inv)
  rw [Functor.whiskerLeft_comp]
  have hd' : (openSupportCompactificationIso Λ sq df dp).hom =
      (openSupportCompactificationIso Λ sq r dp).hom ≫
        Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ]) ed.inv := by
    rw [← hd, Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id,
      Functor.whiskerLeft_id', Category.comp_id]
  rw [hd', ← Category.assoc, hs, ← Category.assoc, hc]


end AlgebraicGeometry.Etale
