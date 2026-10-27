/-
Copyright (c) 2026 The Weil SHEAF project authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Blowup.FlatBaseChange
public import Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts
public import WeilConjectures.Compactification.FiniteTypeExtension
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Étale coordinate models for blowups of smooth pairs

Source: Stacks Project, `more-morphisms.tex`, Tags 0FUE and 0FUT;
`divisors.tex`, Tag 0805
(blueprint: lem-trf-smooth-pair-blowup-local-models).

The polynomial center is the existing `CoordinateSubspaceBlowup.center`. The helpers
only identify the two coordinate indexings and compose canonical flat comparisons.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The canonical flat comparison, with `Y` as the first pullback factor.
It is the upstream relative-Proj comparison followed by pullback symmetry.
Source: Stacks Project, Tag 0805
(blueprint: lem-trf-smooth-pair-blowup-local-models). -/
def Scheme.IdealSheafData.blowupFlatBaseChangeFirst {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) [Flat g] : (I.comap g).blowup ⟶ pullback g I.blowupMap :=
  I.blowupFlatBaseChange g ≫ (pullbackSymmetry I.blowupMap g).hom

/-- The isomorphism carried by the same canonical flat comparison. Its map is
`blowupFlatBaseChangeFirst`; no isomorphism is chosen by an existence theorem.
Source: Stacks Project, Tag 0805
(blueprint: lem-trf-smooth-pair-blowup-local-models). -/
def Scheme.IdealSheafData.blowupFlatBaseChangeFirstIso {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) [Flat g] : (I.comap g).blowup ≅ pullback g I.blowupMap :=
  I.blowupFlatBaseChangeIso g ≪≫ pullbackSymmetry I.blowupMap g


/-- The canonical identification of affine `(a+b)`-space with the existing polynomial
model, sending the first coordinates to `x` and the last coordinates to `y`.
Source: Stacks Project, Tag 0FUE, lemma-etale-local-structure
(blueprint: lem-trf-smooth-pair-blowup-local-models). -/
def smoothPairPolynomialIso (R : Type u) [CommRing R] (a b : ℕ) :
    AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of R)) ≅
      Spec (.of (CoordinateSubspaceBlowup.PolynomialRing R a b)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin (a + b))) (.of R) ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.renameEquiv R
        (finSumFinEquiv.trans Equiv.ulift.symm)).toRingEquiv.toCommRingCatIso.op

/-- The second comparison in the local model: transport along equality of the defining
ideal sheaves, then apply the canonical flat blowup comparison. The étale hypothesis
supplies flatness; it does not specify an arbitrary comparison map.
Source: Stacks Project, Tag 0805, applied as in Tag 0FUT
(blueprint: lem-trf-smooth-pair-blowup-local-models). -/
def smoothPairCoordinateBlowupIso (R : Type u) [CommRing R]
    {P : Scheme.{u}} (I : P.IdealSheafData) (V : P.Opens) (a b : ℕ)
    (h : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of R)))
    (hEtale : Etale h)
    (e : I.comap V.ι = (CoordinateSubspaceBlowup.center R a b).comap
      (h ≫ (smoothPairPolynomialIso R a b).hom)) :
    (I.comap V.ι).blowup ≅ pullback (h ≫ (smoothPairPolynomialIso R a b).hom)
      (CoordinateSubspaceBlowup.center R a b).blowupMap :=
  letI := hEtale
  eqToIso (congrArg Scheme.IdealSheafData.blowup e) ≪≫
    (CoordinateSubspaceBlowup.center R a b).blowupFlatBaseChangeFirstIso
      (h ≫ (smoothPairPolynomialIso R a b).hom)

private lemma polynomialIso_coord (R : Type u) [CommRing R] (a b : ℕ) (j : Fin b) :
    (smoothPairPolynomialIso R a b).hom.appTop
      ((Scheme.ΓSpecIso (.of (CoordinateSubspaceBlowup.PolynomialRing R a b))).inv
        (MvPolynomial.X (Sum.inr j))) =
      AffineSpace.coord (Spec (.of R)) (ULift.up (Fin.natAdd a j)) := by
  simp only [smoothPairPolynomialIso, Iso.trans_hom, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  have hnat {A B : CommRingCat.{u}} (f : A ⟶ B) (x : A) :
      (Spec.map f).appTop ((Scheme.ΓSpecIso A).inv x) =
        (Scheme.ΓSpecIso B).inv (f x) :=
    congrArg (fun k : A ⟶ Γ(Spec B, ⊤) ↦ k x) (Scheme.ΓSpecIso_inv_naturality f).symm
  rw [hnat, AffineSpace.SpecIso_hom_appTop]
  simp [MvPolynomial.renameEquiv]

private lemma center_comap_ideal (R : Type u) [CommRing R] {V : Scheme.{u}}
    (a b : ℕ)
    (h : V ⟶ AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of R)))
    (W : V.affineOpens) :
    ((CoordinateSubspaceBlowup.center R a b).comap
      (h ≫ (smoothPairPolynomialIso R a b).hom)).ideal W =
      Ideal.span (Set.range (fun j : Fin b ↦
        V.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
          (h.appTop (AffineSpace.coord (Spec (.of R)) (ULift.up (Fin.natAdd a j)))))) := by
  rw [CoordinateSubspaceBlowup.center, Scheme.IdealSheafData.comap_ofIdealTop,
    Scheme.IdealSheafData.ofIdealTop_ideal, CoordinateSubspaceBlowup.centerIdeal,
    Ideal.map_map, Ideal.map_map, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext j
  simp only [Function.comp_apply, RingHom.comp_apply, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact congrArg (fun z ↦ V.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op (h.appTop z))
    (polynomialIso_coord R a b j)

private lemma firstIso_hom_fst {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) [Flat g] :
    (I.blowupFlatBaseChangeFirstIso g).hom ≫ pullback.fst _ _ =
      (I.comap g).blowupMap := by
  simp [Scheme.IdealSheafData.blowupFlatBaseChangeFirstIso]

private lemma blowupMap_eqToHom {X : Scheme.{u}} {I J : X.IdealSheafData}
    (e : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.blowup e) ≫ J.blowupMap = I.blowupMap := by
  subst J
  simp

/-- The ideal of a smooth closed pair is of finite type, its immersion is of finite
presentation, and every point of its center has the specified étale blowup model.
Equality of quasi-coherent ideals states the scheme-theoretic inverse-image condition.
Both displayed isomorphisms are constrained to be the canonical flat comparisons.
Source: Stacks Project, Tags 0FUE, 0FUT and 0805
(blueprint: lem-trf-smooth-pair-blowup-local-models).

Proof:
1. Apply `lem-pur-smooth-pair-local-coordinates` to `p`, `q`, `i`, and the point `c`.
   This gives the open neighbourhood, the two nonnegative coordinate counts, the
   étale map over the base, the cartesian coordinate-subspace square, and generators
   of the restricted ideal. Identify the two polynomial indexings by
   `smoothPairPolynomialIso`; the cartesian square gives equality of ideal sheaves.
2. These neighbourhoods cover the center. On its open complement the ideal is the
   unit ideal, generated by one. Thus it is of finite type everywhere, including
   when the center is empty. Use `def-sbc-closed-immersion-ideal-sheaf` and
   `def-weil-closed-immersion` for the kernel and the complement.
3. Apply `lem-trf-closed-immersion-finite-presentation-ideal`: a closed immersion with
   finite-type ideal is locally of finite presentation, quasi-compact and
   quasi-separated. No quasi-compactness assumption on either smooth scheme is used.
4. The open inclusion and the étale coordinate map are flat. Apply
   `thm-nagata-blowup-flat-base-change` to each. The first identifies the inverse
   image of the open with its restricted blowup. Equality of the coordinate ideals
   identifies that restricted blowup with the one pulled back from the polynomial
   center. These are exactly the two isomorphisms below, and each commutes with its
   projection to the open. Use `def-nagata-blowup-flat-base-change-map` and
   `def-pc-fibre-product` for their canonical maps and projections.
5. The second projection is the base change of the étale coordinate map, so
   `lem-weil-pbc-etale-scheme-base-change` makes it étale. Composing with the two
   specified isomorphisms gives the asserted étale map. Zero codimension gives the
   zero ideal and empty blowup, so whole open components are allowed as well.
-/
theorem Scheme.Hom.smooth_pair_blowup_local_models
    (R : Type u) [CommRing R] {P C : Scheme.{u}}
    (p : P ⟶ Spec (.of R)) (q : C ⟶ Spec (.of R)) (i : C ⟶ P)
    [Smooth p] [Smooth q] [IsClosedImmersion i] (hi : i ≫ p = q) :
    i.ker.ofFiniteType ∧
    (LocallyOfFinitePresentation i ∧ QuasiCompact i ∧ QuasiSeparated i) ∧
    ∀ c : C, ∃ (V : P.Opens) (_ : i c ∈ V) (a b : ℕ)
      (h : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of R)))
      (hEtale : Etale h)
      (e : i.ker.comap V.ι = (CoordinateSubspaceBlowup.center R a b).comap
        (h ≫ (smoothPairPolynomialIso R a b).hom)),
      h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) (Spec (.of R)) ↘ Spec (.of R)) =
        V.ι ≫ p ∧
      (∀ W : V.toScheme.affineOpens,
        (i.ker.comap V.ι).ideal W = Ideal.span (Set.range (fun j : Fin b ↦
          V.toScheme.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
            (h.appTop (AffineSpace.coord (Spec (.of R)) (ULift.up (Fin.natAdd a j))))))) ∧
      ∃ E₁ : pullback V.ι i.ker.blowupMap ≅ (i.ker.comap V.ι).blowup,
        E₁ = (i.ker.blowupFlatBaseChangeFirstIso V.ι).symm ∧
        E₁.hom ≫ (i.ker.comap V.ι).blowupMap = pullback.fst V.ι i.ker.blowupMap ∧
        ∃ E₂ : (i.ker.comap V.ι).blowup ≅
            pullback (h ≫ (smoothPairPolynomialIso R a b).hom)
              (CoordinateSubspaceBlowup.center R a b).blowupMap,
          E₂ = smoothPairCoordinateBlowupIso R i.ker V a b h hEtale e ∧
          E₂.hom ≫ pullback.fst _ _ = (i.ker.comap V.ι).blowupMap ∧
          Etale (E₁.hom ≫ E₂.hom ≫ pullback.snd _ _) := by
  have : LocallyOfFinitePresentation (i ≫ p) := by rw [hi]; infer_instance
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i p
  refine ⟨(Scheme.IdealSheafData.ofFiniteType_iff _).mpr (i.fg_ideal_ker),
    ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  intro c
  obtain ⟨a, b, V, hc, h, v, hEtale, hbase, _hsq, _hv, hgen⟩ :=
    Scheme.Hom.exists_etale_smooth_pair_coordinates p q i hi c
  have hker : (pullback.snd i V.ι).ker = i.ker.comap V.ι :=
    i.ker_of_isPullback V.ι (IsPullback.of_hasPullback i V.ι)
  have hg (W : V.toScheme.affineOpens) := (hgen W).1
  simp only [hker] at hg
  have e : i.ker.comap V.ι = (CoordinateSubspaceBlowup.center R a b).comap
      (h ≫ (smoothPairPolynomialIso R a b).hom) := by
    ext W
    rw [hg W, center_comap_ideal]
  let _ := hEtale
  refine ⟨V, hc, a, b, h, hEtale, e, hbase, hg,
    (i.ker.blowupFlatBaseChangeFirstIso V.ι).symm, rfl, ?_,
    smoothPairCoordinateBlowupIso R i.ker V a b h hEtale e, rfl, ?_, ?_⟩
  · change (i.ker.blowupFlatBaseChangeFirstIso V.ι).inv ≫ _ = _
    rw [Iso.inv_comp_eq]
    exact (firstIso_hom_fst i.ker V.ι).symm
  · simp only [smoothPairCoordinateBlowupIso, Iso.trans_hom, Category.assoc,
      firstIso_hom_fst, eqToIso.hom]
    exact blowupMap_eqToHom e
  · infer_instance

end

end AlgebraicGeometry
