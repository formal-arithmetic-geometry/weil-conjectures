/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.TraceFormula.SpaceLinePresentationDefs
import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
import WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful
import Sheaf.TraceFormula.SpaceLinePresentationHomExistence

/-!
# Full faithfulness of cartesian line-module realization

Source: Stacks Project, Descent, Tag 023T; Properties of Spaces, Tag 03G7
(blueprint: lem-trf-cartesian-line-presentation-hom-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

private theorem openSection_map_naturality {A : Scheme.{u}} (U : A.Opens)
    {M N : A.Modules} (f : M ⟶ N) :
    ((Scheme.Modules.tensorPullback U.ι).map f).app ⊤ ≫
        (Scheme.Modules.tensorOpenSectionIso A N U).hom =
      (Scheme.Modules.tensorOpenSectionIso A M U).hom ≫ f.app U := by
  let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
    (Scheme.Modules.restrictAdjunction U.ι)
  have hn := congrArg (fun k ↦ k.app ⊤) (e.hom.naturality f)
  change ((Scheme.Modules.tensorPullback U.ι).map f).app ⊤ ≫ (e.hom.app N).app ⊤ =
    (e.hom.app M).app ⊤ ≫ f.app (U.ι ''ᵁ ⊤) at hn
  have hr := f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ f.app U =
    f.app (U.ι ''ᵁ ⊤) ≫ N.presheaf.map (eqToHom U.ι_image_top.symm).op at hr
  change ((Scheme.Modules.tensorPullback U.ι).map f).app ⊤ ≫
      ((e.hom.app N).app ⊤ ≫ N.presheaf.map (eqToHom U.ι_image_top.symm).op) =
    ((e.hom.app M).app ⊤ ≫ M.presheaf.map (eqToHom U.ι_image_top.symm).op) ≫ f.app U
  rw [← Category.assoc, hn, Category.assoc, ← hr, ← Category.assoc]

private theorem testLineHom_etale_app_eq {X : AlgebraicSpace S}
    (P Q : EtaleLinePresentation X)
    (e f : TestLineHom P.toTestLineFamily Q.toTestLineFamily)
    (h : ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
      (e.app T.obj).app ⊤ s = (f.app T.obj).app ⊤ s) (T : X.EtaleSite) :
    e.app T.obj = f.app T.obj := by
  apply Scheme.Modules.hom_ext
  intro U
  let B := (schemeOpens X T).obj U
  let j : B.obj ⟶ T.obj := CostructuredArrow.homMk (Over.homMk U.ι) (by rfl)
  have he := congrArg (fun t ↦ t.app ⊤) (e.naturality j)
  have hf := congrArg (fun t ↦ t.app ⊤) (f.naturality j)
  have hB : (e.app B.obj).app ⊤ = (f.app B.obj).app ⊤ := by
    ext s
    exact h B s
  have hp : ((Scheme.Modules.tensorPullback U.ι).map (e.app T.obj)).app ⊤ =
      ((Scheme.Modules.tensorPullback U.ι).map (f.app T.obj)).app ⊤ := by
    apply (cancel_mono ((Q.pullbackIso j).hom.app ⊤)).mp
    exact he.symm.trans ((congrArg (fun k ↦ (P.pullbackIso j).hom.app ⊤ ≫ k) hB).trans hf)
  apply (cancel_epi (Scheme.Modules.tensorOpenSectionIso T.obj.left.left
    (P.module T.obj) U).hom).mp
  exact (openSection_map_naturality U (e.app T.obj)).symm.trans
    ((congrArg (fun k ↦ k ≫ (Scheme.Modules.tensorOpenSectionIso T.obj.left.left
      (Q.module T.obj) U).hom) hp).trans (openSection_map_naturality U (f.app T.obj)))

private theorem tensor_map_injective_of_etale_surjective {A B : Scheme.{u}}
    (p : A ⟶ B) [Etale p] [Surjective p] (M N : B.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Injective ((Scheme.Modules.tensorPullback p).map : (M ⟶ N) → _) := by
  intro e f h
  have hp : Sieve.ofArrows (fun _ : PUnit.{1} ↦ A) (fun _ ↦ p) ∈ Scheme.fpqcTopology B := by
    rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
    exact Scheme.fppfTopology_le_fpqcTopology _
      (Precoverage.generate_mem_toGrothendieck p.singleton_mem_fppfPrecoverage)
  apply (bijective_toDescentData_map_of_mem_fpqcTopology
    (fun _ : PUnit.{1} ↦ p) hp M N inferInstance inferInstance).injective
  apply CategoryTheory.Pseudofunctor.DescentData.hom_ext
  intro i
  change (Scheme.Modules.pullback p).map e = (Scheme.Modules.pullback p).map f
  apply (cancel_epi ((Scheme.Modules.boundaryPullbackComparison p).hom.app M)).mp
  rw [← (Scheme.Modules.boundaryPullbackComparison p).hom.naturality e,
    ← (Scheme.Modules.boundaryPullbackComparison p).hom.naturality f, h]

private theorem exists_atlas_test {X : AlgebraicSpace S} (W : SchemeTests X.obj.obj) :
    ∃ (T : X.EtaleSite) (B : SchemeTests X.obj.obj) (j : B ⟶ W) (_k : B ⟶ T.obj),
      Etale j.left.left ∧ Surjective j.left.left := by
  obtain ⟨U, a, ha, hs⟩ := X.property.2
  obtain ⟨B, p, q, hb, hp⟩ := ha W.left W.hom
  obtain ⟨B', p', q', hb', hp'⟩ := hs W.left W.hom
  let e : B ≅ B' := yoneda.preimageIso (hb.isoIsPullback _ _ hb')
  have hep : e.hom ≫ p' = p := by
    apply yoneda.map_injective
    rw [Functor.map_comp]
    change yoneda.map (yoneda.preimage (hb.isoIsPullback _ _ hb').hom) ≫
      yoneda.map p' = yoneda.map p
    rw [Functor.map_preimage]
    exact hb.isoIsPullback_hom_snd _ _ hb'
  have : Surjective p.left := by
    have : Surjective p'.left := hp'
    have : Surjective e.hom.left := inferInstance
    have hsur : Surjective (e.hom.left ≫ p'.left) := inferInstance
    change Surjective ((e.hom ≫ p').left) at hsur
    rwa [hep] at hsur
  let T : X.EtaleSite := ⟨CostructuredArrow.mk a, ha⟩
  let V : SchemeTests X.obj.obj := CostructuredArrow.mk (yoneda.map p ≫ W.hom)
  refine ⟨T, V, CostructuredArrow.homMk p rfl,
    CostructuredArrow.homMk (yoneda.preimage q) ?_, hp, this⟩
  rw [Functor.map_preimage]
  exact hb.w

private theorem testLineHom_ext_of_etale {X : AlgebraicSpace S}
    (P Q : EtaleLinePresentation X)
    (e f : TestLineHom P.toTestLineFamily Q.toTestLineFamily)
    (h : ∀ (T : X.EtaleSite) (s : Γ(P.module T.obj, ⊤)),
      (e.app T.obj).app ⊤ s = (f.app T.obj).app ⊤ s) : e = f := by
  apply TestLineHom.ext
  intro W
  obtain ⟨T, B, j, k, hj, hs⟩ := exists_atlas_test W
  have heT := testLineHom_etale_app_eq P Q e f h T
  have heB : e.app B = f.app B := by
    apply (cancel_epi (P.pullbackIso k).hom).mp
    rw [e.naturality, f.naturality, heT]
  have heW : (Scheme.Modules.tensorPullback j.left.left).map (e.app W) =
      (Scheme.Modules.tensorPullback j.left.left).map (f.app W) := by
    apply (cancel_mono (Q.pullbackIso j).hom).mp
    rw [← e.naturality, ← f.naturality, heB]
  have : Etale j.left.left := hj
  have : Surjective j.left.left := hs
  exact tensor_map_injective_of_etale_surjective j.left.left _ _ heW

/-- A map of small-etale line modules lifts uniquely to the cartesian presentations.
Source: Stacks, Descent, Tag 023T; Properties of Spaces, Tag 03G7
(blueprint: lem-trf-cartesian-line-presentation-hom-descent).
Proof: existence is descent of the chartwise morphism. For uniqueness, restrict to
all opens of each small-etale scheme test. The global-section comparisons and
cartesian naturality imply equality of the ordinary sheaf morphisms on these
charts. Every test admits a surjective etale cover mapping to a small-etale atlas
chart. The two maps agree on that cover, and faithful fpqc descent gives equality
on the test. This applies to empty schemes as well. -/
theorem existsUnique_testLineHom {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (f : P.line ⟶ Q.line) :
    ∃! e : TestLineHom P.toTestLineFamily Q.toTestLineFamily,
      e.IsEtaleCompatible P Q f := by
  obtain ⟨e, he⟩ := exists_testLineHom P Q f
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply testLineHom_ext_of_etale P Q
  intro T s
  apply (Q.etaleSections T).injective
  exact (he' T s).trans (he T s).symm

end AlgebraicGeometry.AlgebraicSpace
