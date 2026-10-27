/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescentData
import Sheaf.AlgebraicGeometry.PolarizedSchemeCharts
import Sheaf.AlgebraicGeometry.PolarizedModuleOnCharts
import Sheaf.AlgebraicGeometry.PolarizedLineIsoDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Effective étale descent for polarized schemes

Source: Stacks Project, Spaces, Tag 02WW; Spaces Descent, Tags 04W8 and 0D3C;
Descent, Tag 023Q (blueprint: lem-trf-polarized-scheme-etale-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

section

variable {S : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
  {uMap : ∀ i, U i ⟶ S} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ U i}
  {L : ∀ i, (X i).Modules} {hL : ∀ i, Scheme.Modules.IsInvertible (L i)}

private theorem chartMap_over (d : PolarizedDescentPair U uMap X f L) (i : I) :
    polarizedChartMap d i ≫ d.g = f i ≫ uMap i := by
  calc
    _ = (d.chart i).schemeIso.inv ≫ pullback.snd d.g (uMap i) ≫ uMap i := by
      simp only [polarizedChartMap, Category.assoc, pullback.condition]
    _ = _ := by rw [← (d.chart i).over]; simp

private theorem chartMap_hom_ext (d : PolarizedDescentPair U uMap X f L)
    (i : I) {T : Scheme.{u}} (a b : T ⟶ X i)
    (ha : a ≫ polarizedChartMap d i = b ≫ polarizedChartMap d i)
    (hb : a ≫ f i = b ≫ f i) : a = b := by
  have hs : (d.chart i).schemeIso.inv ≫ pullback.snd d.g (uMap i) = f i := by
    rw [← (d.chart i).over]
    simp
  apply (cancel_mono (d.chart i).schemeIso.inv).mp
  apply pullback.hom_ext
  · simpa only [polarizedChartMap, Category.assoc] using ha
  · simpa only [Category.assoc, hs] using hb

private theorem chartMap_cover (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    (d : PolarizedDescentPair U uMap X f L) :
    Sieve.ofArrows X (polarizedChartMap d) ∈ Scheme.fppfTopology d.Y := by
  let C : S.Cover Scheme.fppfPrecoverage :=
    Scheme.Cover.mkOfCovers I U uMap D.jointlySurjective (fun i ↦ by
      have := D.isEtale i
      exact ⟨inferInstance, inferInstance⟩)
  let C' := C.pullback₁ d.g
  let C'' : d.Y.Cover Scheme.fppfPrecoverage :=
    Scheme.Cover.copy (P := @Flat ⊓ @LocallyOfFinitePresentation) C'
      I X (polarizedChartMap d) (Equiv.refl I)
      (fun i ↦ (d.chart i).schemeIso.symm) (fun _ ↦ rfl)
  exact Precoverage.generate_mem_toGrothendieck C''.mem₀

private theorem chartMap_ext (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    (d : PolarizedDescentPair U uMap X f L) {T : Scheme.{u}} (a b : d.Y ⟶ T)
    (h : ∀ i, polarizedChartMap d i ≫ a = polarizedChartMap d i ≫ b) : a = b := by
  have hsheaf : Presieve.IsSheaf Scheme.fppfTopology (yoneda.obj T) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply (hsheaf.isSheafFor _ (chartMap_cover D d)).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  exact h i

private theorem existsUnique_chartMap
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL)
    (d d' : PolarizedDescentPair U uMap X f L)
    (hd : IsPolarizedDescentRealization D d) (hd' : IsPolarizedDescentRealization D d') :
    ∃! a : d.Y ⟶ d'.Y, ∀ i, polarizedChartMap d i ≫ a = polarizedChartMap d' i := by
  have hsheaf : Presieve.IsSheaf Scheme.fppfTopology (yoneda.obj d'.Y) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  apply (Presieve.isSheafFor_arrows_iff _ _).1
    (hsheaf.isSheafFor _ (chartMap_cover D d)) (polarizedChartMap d')
  intro i j T a b hab
  change a ≫ polarizedChartMap d' i = b ≫ polarizedChartMap d' j
  have hbase : (a ≫ f i) ≫ uMap i = (b ≫ f j) ≫ uMap j := by
    simpa only [Category.assoc, chartMap_over] using congrArg (fun t ↦ t ≫ d.g) hab
  let r : T ⟶ polarizedOverlap U uMap X f i j :=
    pullback.lift a (pullback.lift (a ≫ f i) (b ≫ f j) hbase) (by simp)
  have hr : r ≫ polarizedOverlapX U uMap X f i j = a := by
    simp [r, polarizedOverlapX]
  have hrj : r ≫ polarizedOverlapUj U uMap X f i j = b ≫ f j := by
    simp [r, polarizedOverlapUj]
  have ht : r ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i = b := by
    apply chartMap_hom_ext d j
    · calc
        _ = (r ≫ polarizedOverlapX U uMap X f i j) ≫ polarizedChartMap d i := by
          simpa only [Category.assoc] using
            (congrArg (fun t ↦ r ≫ t) (hd.theta i j)).symm
        _ = a ≫ polarizedChartMap d i := by rw [hr]
        _ = _ := hab
    · calc
        _ = r ≫ polarizedOverlapUj U uMap X f i j := by
          simpa only [polarizedOverlapUi, Category.assoc] using
            congrArg (fun t ↦ r ≫ t) (D.theta_over_left i j)
        _ = _ := hrj
  calc
    _ = r ≫ polarizedOverlapX U uMap X f i j ≫ polarizedChartMap d' i := by
      rw [← Category.assoc, hr]
    _ = r ≫ (D.theta i j).hom ≫ polarizedOverlapX U uMap X f j i ≫
        polarizedChartMap d' j := by rw [hd'.theta]; simp only [Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ polarizedChartMap d' j) ht

end

/-- Effective etale descent for polarized schemes.
Source: Stacks Project, spaces.tex, Tags 02WW and 02WV; spaces-descent.tex, Tags 04W8
and 0D3C; Descent, Tag 023Q (blueprint: lem-trf-polarized-scheme-etale-descent).

Proof:
1. Obtain the underlying scheme and its prescribed theta charts from
   exists_polarizedSchemeCharts. On this fixed scheme descend the line module using
   exists_polarizedModule_on_schemeCharts; its comparisons give a realization.
2. The chart maps of every candidate form an fppf covering: base change the given
   etale covering and transport it along its chart isomorphisms. The subcanonical
   fppf topology makes these charts jointly detect equality of scheme maps.
3. For two realizations, lift any pair of test maps with the same source-scheme
   image into their specified overlap. Its theta-transport has the same source-scheme
   and base-chart coordinates as the second map, hence equals it by pullback
   uniqueness. The other realization's theta equation proves overlap compatibility.
   Representable-sheaf gluing therefore supplies the unique global scheme map.
4. Glue in the reverse direction. Chartwise equality proves both inverse identities,
   and detects that the isomorphism is over S.
5. For this fixed scheme isomorphism, existsUnique_polarizedLineIso supplies its
   unique compatible module isomorphism. Uniqueness of scheme maps first identifies
   the scheme component of any competitor; then module uniqueness identifies its
   module component, and proof irrelevance identifies the remaining fields. -/
theorem exists_polarizedScheme_of_etaleDescent (S : Scheme.{u}) (I : Type v)
    (U : I → Scheme.{u}) (uMap : ∀ i, U i ⟶ S) (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ U i) (L : ∀ i, (X i).Modules)
    (hL : ∀ i, Scheme.Modules.IsInvertible (L i))
    (D : PolarizedSchemeEtaleDescentDatum S I U uMap X f L hL) :
    ∃ d : PolarizedDescentPair U uMap X f L, IsPolarizedDescentRealization D d ∧
      ∀ d' : PolarizedDescentPair U uMap X f L, IsPolarizedDescentRealization D d' →
        ∃ e : PolarizedDescentPairIso d d', ∀ e' : PolarizedDescentPairIso d d', e' = e := by
  obtain ⟨Y, g, e, he, htheta⟩ := exists_polarizedSchemeCharts D
  obtain ⟨M, hM, c, hd⟩ := exists_polarizedModule_on_schemeCharts D Y g e he htheta
  let d : PolarizedDescentPair U uMap X f L :=
    { Y := Y, g := g, M := M, isInvertible := hM,
      chart := fun i ↦ { schemeIso := e i, over := he i, moduleIso := c i } }
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  obtain ⟨a, ha, hua⟩ := existsUnique_chartMap D d d' hd hd'
  obtain ⟨b, hb, _⟩ := existsUnique_chartMap D d' d hd' hd
  have hab : a ≫ b = 𝟙 d.Y := by
    apply chartMap_ext D d
    intro i
    rw [← Category.assoc, ha, hb, Category.comp_id]
  have hba : b ≫ a = 𝟙 d'.Y := by
    apply chartMap_ext D d'
    intro i
    rw [← Category.assoc, hb, ha, Category.comp_id]
  let E : d.Y ≅ d'.Y := ⟨a, b, hab, hba⟩
  have hE : E.hom ≫ d'.g = d.g := by
    apply chartMap_ext D d
    intro i
    rw [← Category.assoc, ha, chartMap_over, chartMap_over]
  obtain ⟨μ, hμ, huμ⟩ := existsUnique_polarizedLineIso D d d' hd hd' E hE ha
  let q : PolarizedDescentPairIso d d' :=
    { schemeIso := E, over := hE, moduleIso := μ, chart := ha, line := hμ }
  refine ⟨q, ?_⟩
  intro q'
  have hs : q'.schemeIso = E := Iso.ext (hua q'.schemeIso.hom q'.chart)
  cases q' with
  | mk e' over' μ' chart' line' =>
    dsimp only at hs
    subst e'
    have hm : μ' = μ := huμ μ' line'
    subst μ'
    rfl

end AlgebraicGeometry
