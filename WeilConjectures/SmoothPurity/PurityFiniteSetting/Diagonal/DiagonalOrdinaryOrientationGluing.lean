/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrientationRefinement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryDiagonal.DiagonalOrdinaryOverlap

/-! # Gluing the ordinary diagonal orientation

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, combining paragraph;
Stacks Tags 06XS, 0118, 03EM and 04TQ.
(blueprint: lem-pur-diagonal-ordinary-orientation-gluing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem iso_naturality {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (a : F ≅ G) {M N : C} (e : M ≅ N) :
    F.mapIso e = a.app M ≪≫ G.mapIso e ≪≫ (a.app N).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv]
  rw [← a.hom.naturality_assoc e.hom]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

private theorem glue_iso (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (hMN : ∀ i, _root_.DerivedCategory.homologyConcentratedIn 0 0
      ((OrdinaryDiagonal.restrict P (U i).ι).obj M) ∧
      _root_.DerivedCategory.homologyConcentratedIn 0 0
        ((OrdinaryDiagonal.restrict P (U i).ι).obj N))
    (a : ∀ i, (OrdinaryDiagonal.restrict P (U i).ι).obj M ≅
      (OrdinaryDiagonal.restrict P (U i).ι).obj N)
    (ha : ∀ i j,
      OrdinaryDiagonal.onSmallerIso P X (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
        OrdinaryDiagonal.onSmallerIso P X (inf_le_right : U i ⊓ U j ≤ U j) (a j)) :
    ∃ e : M ≅ N, ∀ i, (OrdinaryDiagonal.restrict P (U i).ι).mapIso e = a i := by
  let G := (DegreeZeroMapGluing.degreeZeroDerivedMapGluing P.Coefficient X U hU).1
  obtain ⟨_, _, hglue, _, _, _⟩ := G.2 M N hMN
  obtain ⟨g, hg, _⟩ := (hglue (fun i ↦ (a i).hom)).1 (by
    intro i j
    simpa only [OrdinaryDiagonal.onSmallerIso, DegreeZeroMapGluing.onSmallerOpen,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      Category.assoc] using congrArg Iso.hom (ha i j))
  obtain ⟨_, _, hglue', _, _, _⟩ := G.2 N M (fun i ↦ ⟨(hMN i).2, (hMN i).1⟩)
  obtain ⟨g', hg', _⟩ := (hglue' (fun i ↦ (a i).inv)).1 (by
    intro i j
    simpa only [OrdinaryDiagonal.onSmallerIso, DegreeZeroMapGluing.onSmallerOpen,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Category.assoc] using congrArg Iso.inv (ha i j))
  have hgg' : g ≫ g' = 𝟙 M := by
    obtain ⟨_, _, _, _, _, test⟩ := G.2 M M (fun i ↦ ⟨(hMN i).1, (hMN i).1⟩)
    apply (test _ _).1
    intro i
    change (OrdinaryDiagonal.restrict P (U i).ι).map (g ≫ g') =
      (OrdinaryDiagonal.restrict P (U i).ι).map (𝟙 M)
    rw [CategoryTheory.Functor.map_comp, hg, hg', Iso.hom_inv_id]
    exact ((OrdinaryDiagonal.restrict P (U i).ι).map_id M).symm
  have hg'g : g' ≫ g = 𝟙 N := by
    obtain ⟨_, _, _, _, _, test⟩ := G.2 N N (fun i ↦ ⟨(hMN i).2, (hMN i).2⟩)
    apply (test _ _).1
    intro i
    change (OrdinaryDiagonal.restrict P (U i).ι).map (g' ≫ g) =
      (OrdinaryDiagonal.restrict P (U i).ι).map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, hg, hg', Iso.inv_hom_id]
    exact ((OrdinaryDiagonal.restrict P (U i).ι).map_id N).symm
  refine ⟨⟨g, g', hgg', hg'g⟩, ?_⟩
  intro i
  exact Iso.ext (hg i)

/-- Compatible affine-target diagonal/DNC/vector comparisons have an ordinary-etale
realization. The conclusion prescribes every local restriction, but asserts neither
coordinate-counit normalization nor uniqueness.
Source: blueprint diagonal-dualizing proof, combining paragraph, and the affine-target
assembly in thm-pur-diagonal-dualizing-object, Steps 1--3;
Stacks Tags 06XS, 0118, 03EM, 04TQ
(blueprint: lem-pur-diagonal-ordinary-orientation-gluing).

Proof:
1. Apply affineTargetDiagonalDnc to obtain a finite affine cover of Y. Its inverse
   images cover X. On each chart, theta is rho, alpha inverse, delta, then beta.
   The comparison-unit isomorphism identifies the degree-zero coefficient object
   with the monoidal unit in omega. Thus theta has the displayed endpoints.
2. Shift the source and Tate object by -2d. The Tate line is a sheaf in degree zero;
   theta gives the same concentration for the source on each chart. Exact open
   pullback commutes with cohomology, so concentration is global.
3. On an overlap refine by finite-type affine target opens. Agrees identifies both
   local maps with theta for that refinement. DegreeZeroDerivedMapGluing tests their
   equality there, so they agree on the entire overlap, including nonaffine overlaps.
4. Apply its Hom bijection to glue the maps and their inverses after the shift.
   The equality test makes their composites identities. Shift back to get the
   pro-etale isomorphism, with the prescribed restrictions on every affine open.
5. These objects and maps are of ordinary-etale origin: rho and alpha are the
   specified ordinary base-change mates, delta is the ordinary DNC comparison
   carried by nu*, and beta uses betaEtale. The bounded-below comparison is fully
   faithful. Equivalently perform Steps 2--4 on the ordinary site after these
   identifications. This gives e with the displayed comparison-unit equation.
   Refinement gives the equation for affine opens outside the initial cover.
   The empty cover glues the unique maps of zero objects; d=0 uses shift zero. -/
theorem diagonalOrdinaryOrientationGluing (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsNoetherian X] [IsNoetherian Y] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (D : ∀ (V : Y.affineOpens), (V.1.ι ≫ aY).appTop.hom.FiniteType →
      OrientationRefinement.Chart P f aY d V)
    (hD : ∀ (V V' : Y.affineOpens)
      (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType)
      (hV' : (V'.1.ι ≫ aY).appTop.hom.FiniteType) (h : V'.1 ≤ V.1),
      OrientationRefinement.Agrees P f aY d (D V hV) (D V' hV') h) :
    ∃ e : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d,
      ∀ (V : Y.affineOpens) (hV : (V.1.ι ≫ aY).appTop.hom.FiniteType),
        (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
            ((Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
              (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).symm ≪≫
                e)) ≪≫
          OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d =
        OrientationRefinement.theta P f aY d V (D V hV).geometry (D V hV).betaEtale := by
  classical
  let M := P.diagonalOrdinaryDualizing f
  let N := P.diagonalTwistEtale X d
  let n : ℤ := -(2 * (d : ℤ))
  choose b hb using fun V hV ↦ OrdinaryDiagonal.chart_lift P f aY d V (D V hV)
  let I := {V : Y.affineOpens // (V.1.ι ≫ aY).appTop.hom.FiniteType}
  let U : I → X.Opens := fun V ↦ f ⁻¹ᵁ V.val.1
  have hU : iSup U = ⊤ := by
    obtain ⟨⟨S, hS, hfin⟩, _⟩ :=
      P.affineTargetDiagonalDnc aY (f ≫ aY) f rfl d
    apply top_unique
    intro x _
    have hx : f x ∈ (⨆ V ∈ S, V.1) := by rw [hS]; trivial
    obtain ⟨V, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hV, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hfin V hV⟩, hx⟩
  let a : ∀ i : I, (OrdinaryDiagonal.restrict P (U i).ι).obj (M⟦n⟧) ≅
      (OrdinaryDiagonal.restrict P (U i).ι).obj (N⟦n⟧) :=
    fun i ↦ OrdinaryDiagonal.shiftLocal P _ (b i.val i.property) n
  have hN := OrdinaryDiagonal.twist_concentrated P X (f ≫ aY) d
  have hMN : ∀ i : I, _root_.DerivedCategory.homologyConcentratedIn 0 0
      ((OrdinaryDiagonal.restrict P (U i).ι).obj (M⟦n⟧)) ∧
      _root_.DerivedCategory.homologyConcentratedIn 0 0
        ((OrdinaryDiagonal.restrict P (U i).ι).obj (N⟦n⟧)) := by
    intro i
    have hn := Functor.homologyConcentratedIn_mapDerivedCategory_obj
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (U i).ι) hN
    exact ⟨OrdinaryDiagonal.concentrated_iso (a i).symm hn, hn⟩
  obtain ⟨es, hes⟩ := glue_iso P X U hU (M⟦n⟧) (N⟦n⟧) hMN a (by
    intro i j
    exact OrdinaryDiagonal.overlap P d f aY D hD b hb i.val j.val i.property j.property)
  let e : M ≅ N := (shiftFunctor _ n).preimageIso es
  have he : (shiftFunctor _ n).mapIso e = es := by
    exact (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ n)).isoEquiv.apply_symm_apply es
  have heV (i : I) : (OrdinaryDiagonal.restrict P (U i).ι).mapIso e =
      b i.val i.property := by
    apply (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ n)).isoEquiv.injective
    apply Iso.ext
    change (shiftFunctor _ n).map
      ((OrdinaryDiagonal.restrict P (U i).ι).map e.hom) =
        (shiftFunctor _ n).map (b i.val i.property).hom
    have hi := congrArg Iso.hom (hes i)
    have hs := congrArg Iso.hom he
    dsimp only [Functor.mapIso_hom] at hs
    dsimp only [a, OrdinaryDiagonal.shiftLocal, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv] at hi
    rw [← hs] at hi
    change (OrdinaryDiagonal.restrict P (U i).ι).map
      ((shiftFunctor _ n).map e.hom) =
        ((OrdinaryDiagonal.restrict P (U i).ι).commShiftIso n).hom.app M ≫
          (shiftFunctor _ n).map (b i.val i.property).hom ≫
            ((OrdinaryDiagonal.restrict P (U i).ι).commShiftIso n).inv.app N at hi
    have hn := (OrdinaryDiagonal.restrict P (U i).ι).commShiftIso_hom_naturality e.hom n
    apply (cancel_epi
      (((OrdinaryDiagonal.restrict P (U i).ι).commShiftIso n).hom.app M)).1
    rw [← hn, hi]
    simp only [CategoryTheory.Category.assoc, Iso.inv_hom_id_app]
    exact congrArg
      (fun z ↦ ((OrdinaryDiagonal.restrict P (U i).ι).commShiftIso n).hom.app M ≫ z)
      (CategoryTheory.Category.comp_id ((shiftFunctor _ n).map (b i.val i.property).hom))
  refine ⟨e, ?_⟩
  intro V hV
  have hc := iso_naturality (OrdinaryDiagonal.comparison P (f ⁻¹ᵁ V.1).ι) e
  change (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
        (OrdinaryDiagonal.unit P f ≪≫ e)) ≪≫
    OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d = _
  rw [← hb V hV, ← heV ⟨V, hV⟩]
  simp only [OrdinaryDiagonal.realize, Functor.mapIso_trans]
  change (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso e) =
    (OrdinaryDiagonal.comparison P (f ⁻¹ᵁ V.1).ι).app M ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) (f ⁻¹ᵁ V.1).toScheme).mapDerivedCategory.mapIso
        ((OrdinaryDiagonal.restrict P (U ⟨V, hV⟩).ι).mapIso e) ≪≫
      ((OrdinaryDiagonal.comparison P (f ⁻¹ᵁ V.1).ι).app N).symm at hc
  simpa only [Iso.trans_assoc] using
    congrArg (fun z ↦
      (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (OrdinaryDiagonal.unit P f)) ≪≫ z ≪≫
        OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d) hc

end WeilConjectures.PurityFiniteSetting
