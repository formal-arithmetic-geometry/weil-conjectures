/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.GrothendieckHypercoverComparison
import Sheaf.AlgebraicGeometry.GrothendieckHypercoverLimitGeneration
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.SixFunctors.Etale.Gabber
import Sheaf.AlgebraicGeometry.FixedBaseCohomologyClassDescent

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ]). This is blueprint
`lemma-weil-pbc-etale-cohomology-continuity`, which belongs to the subsection `sk-prop-h2`; its
elementwise version below follows from class descent and finite-stage vanishing.
The general-coefficient vanishing criterion reduces to the explicit hypercover comparison
and finite-stage generation of the hypercover colimit.

## Main definitions

- `AlgebraicGeometry.Etale.sectionsFunctor`: the global sections functor of the small étale
  site, the sections over the terminal object.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The global sections functor `Γ(X, -)` on étale sheaves: the sections over the terminal
object `X` of the small étale site. -/
noncomputable abbrev sectionsFunctor (X : Scheme.{u}) : Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf _ A ⋙
    (evaluation _ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an étale sheaf on `S`. Then
`H^q(X, F|_X) = colimᵢ H^q(Dᵢ, F|_{Dᵢ})`; in particular `H^q(X, F|_X)` vanishes as soon as all
the `H^q(Dᵢ, F|_{Dᵢ})` do. -/
theorem isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology A) {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ)
    (h : ∀ i, IsZero (((sectionsFunctor A (D.obj i).left).rightDerived q).obj
      ((Etale.upperStar A (D.obj i).hom).obj F))) :
    IsZero (((sectionsFunctor A c.pt.left).rightDerived q).obj
      ((Etale.upperStar A c.pt.hom).obj F)) := by
  let E := D ⋙ Over.forget S
  let d := (Over.forget S).mapCone c
  have : ∀ i, CompactSpace (E.obj i) := fun i ↦ inferInstanceAs
    (CompactSpace (D.obj i).left)
  have : ∀ i, QuasiSeparatedSpace (E.obj i) := fun i ↦ inferInstanceAs
    (QuasiSeparatedSpace (D.obj i).left)
  have : ∀ {i j} (g : i ⟶ j), IsAffineHom (E.map g) :=
    fun g ↦ inferInstanceAs (IsAffineHom (D.map g).left)
  have : CompactSpace c.pt.left := Scheme.compactSpace_of_isLimit E d hc
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (d.π.app i) := isAffineHom_π_app E d hc i
  have : QuasiSeparatedSpace c.pt.left :=
    quasiSeparatedSpace_of_quasiSeparated (d.π.app i)
  let e (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
      (G : Sheaf X.smallEtaleTopology A) :=
    FiniteSplitEtaleHypercover.nonempty_hypercoverCohomology_iso A q
      ((sectionsFunctor A X).rightDerived q)
      (FiniteSplitEtaleHypercover.isCohomologyColimit_rightDerived_sections A X q) G
  obtain ⟨eLimit⟩ := e c.pt.left ((Etale.upperStar A c.pt.hom).obj F)
  apply IsZero.of_iso _ eLimit.symm
  apply (IsZero.iff_id_eq_zero _).2
  apply FiniteSplitEtaleHypercover.hypercoverCohomology_limit_hom_ext A F D c hc q
  intro j a
  obtain ⟨eStage⟩ := e (D.obj j).left ((Etale.upperStar A (D.obj j).hom).obj F)
  exact (IsZero.of_iso (h j) eStage).eq_of_src _ _

attribute [local irreducible] upperStar cohomologyMap Sheaf.H.map
  CategoryTheory.Abelian.Ext.instAddCommGroup

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity, in the
form of an elementwise colimit statement for the pullback maps.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an abelian étale sheaf on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` along the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap`: every class on `X` comes from some `Dᵢ` (up to the
canonical identification `F|_X ≅ (F|_{Dᵢ})|_X` of `AlgebraicGeometry.Etale.upperStarComp`), and a
class on `Dᵢ` which vanishes on `X` already vanishes on some `Dⱼ`, `j ⟶ i`. -/
theorem cohomologyMap_isColimit_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0 :=
  by
  classical
  constructor
  · exact exists_cohomologyMap_preimage_of_isLimit F D c hc q
  · intro i y hy
    let E₀ := D ⋙ Over.forget S
    let E : Over i ⥤ Scheme.{u} := Over.forget i ⋙ E₀
    let : ∀ a : Over i, CompactSpace (E.obj a) :=
      fun a ↦ inferInstanceAs (CompactSpace (D.obj a.left).left)
    let : ∀ a : Over i, QuasiSeparatedSpace (E.obj a) :=
      fun a ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj a.left).left)
    let : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom (E.map g) :=
      fun g ↦ inferInstanceAs (IsAffineHom (D.map g.left).left)
    let π : E ⟶ (Functor.const (Over i)).obj (D.obj i).left :=
      { app := fun a ↦ (D.map a.hom).left
        naturality := fun a b g ↦ by
          change (D.map g.left).left ≫ (D.map b.hom).left = (D.map a.hom).left ≫ 𝟙 _
          simpa only [Category.comp_id, ← Over.comp_left, ← D.map_comp] using
            congrArg (fun f ↦ (D.map f).left) g.w }
    let c₀ := (Over.forget S).mapCone c
    let c' : Cone E := c₀.whisker (Over.forget i)
    have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv _ c₀).symm hc
    have hz' : cohomologyMap (c'.π.app (Over.mk (𝟙 i)) ≫
        π.app (Over.mk (𝟙 i))) _ q y = 0 := by
      change cohomologyMap ((c.π.app i).left ≫ (D.map (𝟙 i)).left) _ q y = 0
      have hm : (c.π.app i).left ≫ (D.map (𝟙 i)).left = (c.π.app i).left := by
        rw [D.map_id, Over.id_left, Category.comp_id]
      exact (congrArg (fun m ↦ cohomologyMap m _ q y = 0) hm).mpr hy
    obtain ⟨a, ha⟩ := exists_cohomologyMap_eq_zero_of_isLimit E π c' hc' _ y (Over.mk (𝟙 i)) hz'
    exact ⟨a.left, a.hom, ha⟩


end AlgebraicGeometry.Etale
