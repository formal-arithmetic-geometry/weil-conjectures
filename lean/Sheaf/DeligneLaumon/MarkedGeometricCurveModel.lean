/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
import Sheaf.AlgebraicGeometry.GeometricClosedCurveSmoothModel
import WeilConjectures.WeilSheaf.FinitePointCohomology

/-! # Finite-field models of marked geometric curves in the source conventions -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The data of a marked finite-field model, bundled to keep its dependent scheme and
field instances shared during kernel checking.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: lem-zl-marked-geometric-curve-model). -/
structure MarkedGeometricCurveModel
    {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ)
    {X : Scheme.{u}} [X.Over (Spec (.of k₀))]
    (x y : X.finitePoints) (D : Scheme.{u})
    (v : D ⟶ (X ↘ Spec (.of k₀)).geometricFiber) where
  k₁ : Type u
  [field₁ : Field k₁]
  [finite₁ : Finite k₁]
  [algebra₁ : Algebra k₀ k₁]
  [char₁ : Fact (ringChar k₁ ≠ l)]
  C : Scheme.{u}
  [overC : C.Over (Spec (.of k₁))]
  [affineC : IsAffine C]
  [smoothC : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k₁))]
  [connectedC : GeometricallyConnected (C ↘ Spec (.of k₁))]
  [separatedC : IsSeparated (C ↘ Spec (.of k₁))]
  [finiteTypeC : LocallyOfFiniteType (C ↘ Spec (.of k₁))]
  [quasiCompactC : QuasiCompact (C ↘ Spec (.of k₁))]
  r : ℕ
  positive : 0 < r
  cardinality : Nat.card k₁ = Nat.card k₀ ^ r
  τ : AlgebraicClosure k₀ ≃+* AlgebraicClosure k₁
  c : C ⟶ X
  u : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber
  z : D ≅ (C ↘ Spec (.of k₁)).geometricFiber
  τ_comm : ∀ a : k₀, τ (algebraMap k₀ (AlgebraicClosure k₀) a) =
    algebraMap k₁ (AlgebraicClosure k₁) (algebraMap k₀ k₁ a)
  structure_comm : c ≫ (X ↘ Spec (.of k₀)) =
    (C ↘ Spec (.of k₁)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))
  projection_comm : u ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
    (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c
  closure_comm : u ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
    (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
      Spec.map (CommRingCat.ofHom τ.toRingHom)
  frobenius_comm : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ u =
    u ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom
  immersion_comm : z.hom ≫ u = v
  s : C.finitePoints
  t : C.finitePoints
  image_s : c s.1 = x.1
  image_t : c t.1 = y.1

/-- A geometric smooth affine closed curve, with two marked lifts, descends to a single
finite field. The output compares the actual algebraic closures used by the source library.
This assertion concerns schemes only, with no sheaves or local Frobenius operators.

Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: lem-zl-marked-geometric-curve-model).

Proof: Choose the finite-field datum with base k0 and closure AlgebraicClosure k0.
A smooth connected curve is irreducible because its regular local rings are domains.
Its dimension is one by the relative-dimension theorem. Apply the existing smooth closed
curve model theorem, which descends the closed immersion to a subfield E of the closure.
The model is affine, smooth, geometrically connected and pure of dimension one. Hence it is
irreducible and smooth of relative dimension one; affineness gives separatedness. Give E
its specified k0-algebra structure. Both E and its embedding have been chosen by the
unique-subfield theorem, which supplies its cardinality and the scalar tower. The closure
of k0 is an algebraic closure of E. An E-algebra isomorphism from its chosen algebraic closure
identifies the base change of this model with the input curve. Compose this identification
with the given closed immersion to obtain u. Its projections give the two displayed squares.
The two scheme Frobenii commute with u, because the model projection is fixed and the
closure Frobenius is raised to the degree r of E/k0. The images of the marked points are
closed on the same model, by the universal point assertion of the model theorem; the given
lift equalities identify their images in X with x and y. No distinctness is required. -/
theorem exists_marked_geometric_curve_model
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (.of k₀))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [QuasiCompact (X ↘ Spec (.of k₀))]
    (x y : X.finitePoints) (D : Scheme.{u})
    (v : D ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsClosedImmersion v] [IsAffine D]
    [SmoothOfRelativeDimension 1
      (v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure)]
    [ConnectedSpace D]
    (sx sy : Spec (.of (AlgebraicClosure k₀)) ⟶ D)
    (hsx : sx ≫ v = (X ↘ Spec (.of k₀)).geometricFiberPointOfFinitePoint x)
    (hsy : sy ≫ v = (X ↘ Spec (.of k₀)).geometricFiberPointOfFinitePoint y) :
    Nonempty (MarkedGeometricCurveModel l x y D v) := by
  classical
  let := Fintype.ofFinite k₀
  obtain ⟨a, hp, hcard⟩ := FiniteField.card k₀ (ringChar k₀)
  let F : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := ringChar k₀
      a := a
      q := Nat.card k₀
      prime := hp
      exponent_pos := a.2
      cardinality_eq := by simpa only [Nat.card_eq_fintype_card] using hcard
      k₀ := k₀
      card_base := rfl
      k := AlgebraicClosure k₀ }
  let X₀ := Over.mk (X ↘ Spec (.of k₀))
  have : IsAffine X₀.left := inferInstanceAs (IsAffine X)
  have : LocallyOfFiniteType X₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k₀)))
  have : QuasiCompact X₀.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k₀)))
  let d := v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  have : Smooth d := SmoothOfRelativeDimension.smooth 1 d
  have : Smooth (v ≫ (F.geometricFiber X₀).hom) := inferInstanceAs (Smooth d)
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian d
  have : IrreducibleSpace D := irreducibleSpace_of_isDomain_stalk D fun x ↦ by
    have := Smooth.isRegularLocalRing_stalk d x
    infer_instance
  have hdim : topologicalKrullDim D = (1 : WithBot ℕ∞) :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq d 1).mp inferInstance
  have hpure : D.IsPureDimension 1 := by
    intro Z hZ
    have hZ' : Z = Set.univ := by
      simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hZ
    subst Z
    exact (Homeomorph.Set.univ D).isHomeomorph.topologicalKrullDim_eq _ |>.trans hdim
  obtain ⟨m, hm, C₀, i₀, haff, hlft, hqc, hi, hsm, hconn, hpureC, z, hz, hpoints⟩ :=
    F.exists_smooth_closed_curve_finiteField_model X₀ D v hpure
  have : IsAffine C₀.left := haff
  have : LocallyOfFiniteType C₀.hom := hlft
  have : QuasiCompact C₀.hom := hqc
  have : Smooth C₀.hom := hsm
  have : GeometricallyConnected C₀.hom := hconn
  have : GeometricallyIrreducible C₀.hom := .of_smooth_of_geometricallyConnected _
  have : IrreducibleSpace C₀.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton C₀.hom
  have hdimC : topologicalKrullDim C₀.left = (1 : WithBot ℕ∞) := by
    have hp := hpureC Set.univ (by simp only [irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff])
    exact ((Homeomorph.Set.univ C₀.left).isHomeomorph.topologicalKrullDim_eq _).symm.trans hp
  have hrel : SmoothOfRelativeDimension 1 C₀.hom :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq C₀.hom 1).mpr hdimC
  let E := F.extensionSubfield m hm
  let α := F.extensionEmbedding m hm
  let : Algebra k₀ E := α.toAlgebra
  have hα : E.subtype.comp α = algebraMap k₀ (AlgebraicClosure k₀) :=
    (FiniteField.exists_unique_subfield_of_closure F.p F.a F.q F.prime F.exponent_pos
      F.cardinality_eq F.k₀ F.card_base F.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have hEcard : Nat.card E = Nat.card k₀ ^ m :=
    (FiniteField.exists_unique_subfield_of_closure F.p F.a F.q F.prime F.exponent_pos
      F.cardinality_eq F.k₀ F.card_base F.k m hm).choose_spec.2.1
  have : Finite E := (Nat.card_pos_iff.mp (hEcard ▸ Nat.pow_pos (Nat.card_pos) )).2
  have : IsScalarTower k₀ E (AlgebraicClosure k₀) :=
    IsScalarTower.of_algebraMap_eq' hα.symm
  have : Algebra.IsAlgebraic E (AlgebraicClosure k₀) :=
    Algebra.IsAlgebraic.tower_top (K := k₀) E
  have : IsAlgClosure E (AlgebraicClosure k₀) := ⟨inferInstance, inferInstance⟩
  let ψ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure k₀ := IsAlgClosure.equiv E _ _
  let τ := ψ.symm.toRingEquiv
  have hτ (a : k₀) : τ (algebraMap k₀ (AlgebraicClosure k₀) a) =
      algebraMap E (AlgebraicClosure E) (algebraMap k₀ E a) := by
    apply ψ.injective
    change ψ (ψ.symm (algebraMap k₀ (AlgebraicClosure k₀) a)) =
      ψ (algebraMap E (AlgebraicClosure E) (algebraMap k₀ E a))
    rw [ψ.apply_symm_apply, ψ.commutes]
    exact IsScalarTower.algebraMap_apply k₀ E (AlgebraicClosure k₀) a
  let g := Spec.map (CommRingCat.ofHom E.subtype)
  let g' := Spec.map (CommRingCat.ofHom (algebraMap E (AlgebraicClosure E)))
  let σ : Spec (.of (AlgebraicClosure k₀)) ≅ Spec (.of (AlgebraicClosure E)) :=
    Scheme.Spec.mapIso ψ.toRingEquiv.toCommRingCatIso.op
  have hσ : g = σ.hom ≫ g' := by
    dsimp [g, g', σ]
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (ψ.commutes a).symm
  let β : pullback C₀.hom g ≅ pullback C₀.hom g' :=
    asIso (pullback.map C₀.hom g C₀.hom g' (𝟙 _) σ.hom (𝟙 _)
      (by simp) (by simpa using hσ))
  let z' : D ≅ pullback C₀.hom g' := (Over.forget _).mapIso z ≪≫ β
  let c := i₀.left ≫ pullback.fst X₀.hom
    (Spec.map (CommRingCat.ofHom α))
  let : C₀.left.Over (Spec (.of E)) := ⟨C₀.hom⟩
  have hchar : Fact (ringChar E ≠ l) :=
    ⟨by rw [← Algebra.ringChar_eq k₀ E]; exact Fact.out⟩
  have hsep : IsSeparated C₀.hom := IsSeparated.of_isAffineHom _
  have hc : c ≫ X₀.hom = C₀.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k₀ E)) := by
    change (i₀.left ≫ pullback.fst X₀.hom
      (Spec.map (CommRingCat.ofHom α))) ≫ X₀.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw : i₀.left ≫ pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom α)) =
        C₀.hom := Over.w i₀
    exact congrArg (· ≫ Spec.map (CommRingCat.ofHom α)) hw
  let U : (C₀.left ↘ Spec (.of E)).geometricFiber ⟶
      (X ↘ Spec (.of k₀)).geometricFiber :=
    pullback.lift ((C₀.left ↘ Spec (.of E)).geometricFiberProj ≫ c)
      ((C₀.left ↘ Spec (.of E)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom)) (by
      change (pullback.fst C₀.hom g' ≫ c) ≫ X₀.hom =
        (pullback.snd C₀.hom g' ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k₀ (AlgebraicClosure k₀)))
      rw [Category.assoc, hc, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc]
      apply congrArg (pullback.snd C₀.hom g' ≫ ·)
      dsimp only [g']
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact (hτ a).symm)
  have hup : U ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C₀.left ↘ Spec (.of E)).geometricFiberProj ≫ c := pullback.lift_fst _ _ _
  have huτ : U ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C₀.left ↘ Spec (.of E)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom) := pullback.lift_snd _ _ _
  have hzu : z'.hom ≫ U = v := by
    apply Scheme.Hom.geometricFiber_hom_ext
    · rw [Category.assoc, hup]
      change (z.hom.left ≫ β.hom) ≫ pullback.fst C₀.hom g' ≫ c = _
      dsimp [β]
      simp only [Category.assoc, pullback.lift_fst_assoc, Category.id_comp]
      exact hz
    · rw [Category.assoc, huτ]
      change (z.hom.left ≫ β.hom) ≫ pullback.snd C₀.hom g' ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom) = d
      dsimp [β]
      simp only [Category.assoc, pullback.lift_snd_assoc]
      have hzbase : z.hom.left ≫ pullback.snd C₀.hom g = d := Over.w z.hom
      rw [← Category.assoc z.hom.left, hzbase]
      change d ≫ σ.hom ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = d
      have hστ : σ.hom ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) = 𝟙 _ := by
        change Spec.map (CommRingCat.ofHom ψ.toRingEquiv.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ψ.symm.toRingEquiv.toRingHom) = 𝟙 _
        exact (spec_map_comp_spec_map_eq _ _ (RingHom.id _)
          (fun a ↦ ψ.apply_symm_apply a)).trans (Spec.map_id _)
      rw [hστ, Category.comp_id]
  have hfrob : (specGeometricFrobenius E).hom ≫
      Spec.map (CommRingCat.ofHom τ.toRingHom) =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        (specGeometricFrobenius k₀ ^ m).hom := by
    let := Fintype.ofFinite E
    rw [specGeometricFrobenius_hom, specGeometricFrobenius_pow_hom,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change FiniteField.geometricFrobeniusAlgEquivOfAlgebraic E
      (AlgebraicClosure E) (τ a) =
      τ ((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀
        (AlgebraicClosure k₀) ^ m) a)
    apply ψ.injective
    have h := algEquiv_geometricFrobenius_apply m
      (by simpa only [Nat.card_eq_fintype_card] using hEcard) ψ.toRingEquiv (τ a)
    simpa only [τ, AlgEquiv.coe_ringEquiv, AlgEquiv.apply_symm_apply] using h
  have hu : (C₀.left ↘ Spec (.of E)).geometricGaloisFrobenius.hom ≫ U =
      U ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).hom := by
    apply Scheme.Hom.geometricFiber_hom_ext
    · simp only [Category.assoc, hup,
        Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj_assoc,
        Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
    · rw [Category.assoc, huτ, ← Category.assoc,
        Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure,
        Category.assoc, hfrob]
      rw [Category.assoc,
        Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure]
      simp only [← Category.assoc, huτ]
  let p := z.hom.left ≫ pullback.fst C₀.hom g
  have hpoint (w : Spec (.of (AlgebraicClosure k₀)) ⟶ D)
      (hw : w ≫ d = 𝟙 _) : p (w (IsLocalRing.closedPoint (AlgebraicClosure k₀))) ∈
        C₀.left.finitePoints := by
    let w' : Over.mk (𝟙 (Spec (.of (AlgebraicClosure k₀)))) ⟶ Over.mk d :=
      Over.homMk w hw
    obtain ⟨_, hfinite⟩ := hpoints w' _ rfl
    let := (C₀.hom.residueFieldAlgebraMap
      (p (w (IsLocalRing.closedPoint (AlgebraicClosure k₀))))).toAlgebra
    have : Module.Finite E (C₀.left.residueField
        (p (w (IsLocalRing.closedPoint (AlgebraicClosure k₀))))) := hfinite
    exact Module.finite_of_finite E
  have hsxd : sx ≫ d = 𝟙 _ := by
    dsimp [d]
    rw [← Category.assoc, hsx]
    exact Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure _ x
  have hsyd : sy ≫ d = 𝟙 _ := by
    dsimp [d]
    rw [← Category.assoc, hsy]
    exact Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure _ y
  let s : C₀.left.finitePoints := ⟨p (sx (IsLocalRing.closedPoint _)), hpoint sx hsxd⟩
  let t : C₀.left.finitePoints := ⟨p (sy (IsLocalRing.closedPoint _)), hpoint sy hsyd⟩
  have hcs : c s.1 = x.1 := by
    have hpv : p ≫ c = v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj := hz
    have h := congrArg (fun f : Spec (.of (AlgebraicClosure k₀)) ⟶ X ↦
      f (IsLocalRing.closedPoint _))
      (show sx ≫ p ≫ c = (X ↘ Spec (.of k₀)).geometricFiberPointOfFinitePoint x ≫
        (X ↘ Spec (.of k₀)).geometricFiberProj by rw [hpv, ← Category.assoc, hsx])
    exact h.trans
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ x)
  have hct : c t.1 = y.1 := by
    have hpv : p ≫ c = v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj := hz
    have h := congrArg (fun f : Spec (.of (AlgebraicClosure k₀)) ⟶ X ↦
      f (IsLocalRing.closedPoint _))
      (show sy ≫ p ≫ c = (X ↘ Spec (.of k₀)).geometricFiberPointOfFinitePoint y ≫
        (X ↘ Spec (.of k₀)).geometricFiberProj by rw [hpv, ← Category.assoc, hsy])
    exact h.trans
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ y)
  exact ⟨{
    k₁ := E
    char₁ := hchar
    C := C₀.left
    affineC := haff
    smoothC := hrel
    connectedC := hconn
    separatedC := hsep
    finiteTypeC := hlft
    quasiCompactC := hqc
    r := m
    positive := hm
    cardinality := hEcard
    τ := τ
    c := c
    u := U
    z := z'
    τ_comm := hτ
    structure_comm := hc
    projection_comm := hup
    closure_comm := huτ
    frobenius_comm := hu
    immersion_comm := hzu
    s := s
    t := t
    image_s := hcs
    image_t := hct }⟩


end AlgebraicGeometry
