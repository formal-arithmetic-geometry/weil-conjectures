/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H5
-/
module

public import Sheaf.Paper.ConstantExtensionWeilHeartData
import Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy
import Sheaf.Paper.ConstantExtensionReturnExactFunctor
import Sheaf.Paper.ConstantExtensionReturnLocalOperators
import Sheaf.Paper.ConstantExtensionPullbackReturnResidue
import Sheaf.Paper.ConstantExtensionSheetGeometry
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Constant extension and the two constructible Weil hearts

Source: Deligne, Weil II, (1.1.7)--(1.1.10), pp. 150--152.
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]

/-- The disjoint union of m clopen sheets, with cyclic geometric-Frobenius return.
Source: Deligne, Weil II, p. 152; blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the Galois tensor splitting k_m tensor_{k_0} k = product_sigma k gives
exactly m open-and-closed components. Geometric Frobenius permutes embeddings
cyclically. The sheet for the fixed inclusion is the pullback lift already defined;
its translates give the coproduct cocone. The mth power returns with gamma^m,
which is the geometric Frobenius for the k_m-model. Compare projections to obtain
the final equality. This includes the empty scheme and m=1. -/
theorem constantExtensionCyclicSheets :
    (∀ i : Fin m, IsOpenImmersion (constantExtensionCyclicSheet D m hm X₀ i) ∧
      IsClosedImmersion (constantExtensionCyclicSheet D m hm X₀ i)) ∧
    Nonempty (IsColimit (Cofan.mk
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left
      (constantExtensionCyclicSheet D m hm X₀))) ∧
    (constantExtensionFiberIso D m hm X₀).inv ≫ constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ m).hom =
      ((D.geometricFrobenius X₀) ^ m).hom ≫
        (constantExtensionFiberIso D m hm X₀).inv ≫ constantExtensionSheet D m hm X₀ := by
  obtain ⟨G⟩ := constantExtensionSheetGeometry D m hm X₀
  have hopen (i : Fin m) : IsOpenImmersion (constantExtensionCyclicSheet D m hm X₀ i) := by
    rw [← G.factor i]
    infer_instance
  have hrange (i : Fin m) :
      (constantExtensionCyclicSheet D m hm X₀ i).opensRange = G.opens i := by
    simpa only [G.factor i] using
      (Scheme.Hom.opensRange_comp_of_isIso (G.coordinate i).hom (G.opens i).ι).trans
        (Scheme.Opens.opensRange_ι (G.opens i))
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨hopen i, IsClosedImmersion.of_isPreimmersion _ ?_⟩
    rw [← Scheme.Hom.coe_opensRange, hrange]
    exact G.closed i
  · apply nonempty_isColimit_cofanMk_of
    · simpa only [hrange] using G.cover
    · simpa only [hrange] using G.disjoint
  · let i : Fin m := ⟨m - 1, by omega⟩
    have h := G.return_map i (by dsimp [i]; omega)
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hp (a : Aut (D.geometricFiber X₀).left) (n : ℕ) :
        localPositivePower a.hom n = (a ^ (n + 1)).hom := by
      induction n with
      | zero => simp [localPositivePower]
      | succ n ih =>
        rw [localPositivePower, ih]
        exact (congrArg (fun b : Aut (D.geometricFiber X₀).left ↦ b.hom)
          (pow_succ' a (n + 1))).symm
    have hstep :
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^
          (m - 1)).hom ≫
            (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom =
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ m).hom := by
      calc
        _ = ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^
            (m - 1 + 1)).hom := by rw [pow_succ']; rfl
        _ = _ := congrArg
          (fun n ↦ ((D.geometricFrobenius
            (constantExtensionOriginalModel D m hm X₀)) ^ n).hom) hm'
    have hone : (1 : Aut
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left).hom = 𝟙 _ := rfl
    simpa [constantExtensionCyclicSheet, i, hp, hm', Category.assoc, hstep, hone] using h

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem sheetSpecIso
    (R S : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionSheetSpec D m hm X₀ l hl Ω R)
    (hS : ConstantExtensionSheetSpec D m hm X₀ l hl Ω S) : Nonempty (R ≅ S) := by
  obtain ⟨α, hα⟩ := hR
  obtain ⟨β, hβ⟩ := hS
  let e := α ≪≫ β.symm
  let h (N : sfCommonStageWeilSheaf D l hl
      (constantExtensionOriginalModel D m hm X₀) Ω) :
      (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω).map (e.app N).hom ≫
          (S.obj N).obj.str.hom = (R.obj N).obj.str.hom ≫ (e.app N).hom := by
    let P := sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω
    let U := (constantExtensionReturnComparison D m hm X₀ l hl Ω N.obj.carrier).hom ≫
      (constantExtensionSheetPull D m hm X₀ l hl Ω).map
        (constantExtensionWeilIterate D l hl Ω
          (constantExtensionOriginalModel D m hm X₀) N.obj (m - 1)).hom
    have hα' : P.map (α.hom.app N) ≫ U = (R.obj N).obj.str.hom ≫ α.hom.app N := by
      simpa only [U, Category.assoc] using hα N
    have hβ' : P.map (β.hom.app N) ≫ U = (S.obj N).obj.str.hom ≫ β.hom.app N := by
      simpa only [U, Category.assoc] using hβ N
    apply (cancel_mono (β.hom.app N)).mp
    change (P.map (α.hom.app N ≫ β.inv.app N) ≫ (S.obj N).obj.str.hom) ≫
      β.hom.app N = ((R.obj N).obj.str.hom ≫
        (α.hom.app N ≫ β.inv.app N)) ≫ β.hom.app N
    simp only [Functor.map_comp, Category.assoc, β.inv_hom_id_app, Category.comp_id]
    rw [← hβ']
    simpa only [← Functor.map_comp_assoc, Category.assoc, β.inv_hom_id_app,
      Functor.map_id, Category.id_comp, Category.comp_id] using hα'
  refine ⟨NatIso.ofComponents (fun N ↦
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (CategoryTheory.Endofunctor.Algebra.isoMk (e.app N) (h N)))) ?_⟩
  intro N N' f
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply CategoryTheory.Endofunctor.Algebra.Hom.ext
  exact e.hom.naturality f

private theorem sheetCoordinateIso
    (N : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
    (i : Fin m) :
    Nonempty ((constantExtensionSheetPullAt D m hm X₀ l hl Ω i).obj N.obj.carrier ≅
      (constantExtensionSheetPull D m hm X₀ l hl Ω).obj N.obj.carrier) := by
  have h (n : ℕ) (hn : n < m) :
      Nonempty ((constantExtensionSheetPullAt D m hm X₀ l hl Ω ⟨n, hn⟩).obj
        N.obj.carrier ≅ (constantExtensionSheetPull D m hm X₀ l hl Ω).obj N.obj.carrier) := by
    induction n with
    | zero => exact ⟨(constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω).app _⟩
    | succ n ih =>
      obtain ⟨a⟩ := ih (by omega)
      exact ⟨constantExtensionCoordinateStep D m hm X₀ l hl Ω N.obj
        ⟨n, by omega⟩ ⟨n + 1, hn⟩ rfl ≪≫ a⟩
  exact h i.val i.isLt

private theorem normalizationReturnIso
    (S : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hS : ConstantExtensionSheetSpec D m hm X₀ l hl Ω S)
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
    (hG : ConstantExtensionPullbackNormalization D m hm X₀ l hl Ω R G) :
    Nonempty (G ⋙ S ≅ R) := by
  obtain ⟨α, hα⟩ := hS
  obtain ⟨γ, -, hγ⟩ := hG
  let δ := Functor.isoWhiskerLeft
      (G ⋙ constantExtensionHeartForget D l hl Ω
        (constantExtensionOriginalModel D m hm X₀))
      (constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω).symm ≪≫ γ ⟨0, hm⟩
  let e := Functor.isoWhiskerLeft G α ≪≫ δ
  have he (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
      (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω).map (e.app F).hom ≫
          (R.obj F).obj.str.hom = (S.obj (G.obj F)).obj.str.hom ≫ (e.app F).hom := by
    dsimp only [e, Iso.trans_hom, NatTrans.comp_app, Iso.app_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    rw [Functor.map_comp, Category.assoc]
    have hh := hγ F
    change (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω).map (δ.hom.app F) ≫ _ = _ at hh
    rw [hh]
    simpa only [δ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.comp_obj, constantExtensionHeartForget,
      sfCommonStageWeilForget, ObjectProperty.ι_obj, Endofunctor.IsoAlgebra.forget_obj,
      Category.assoc] using congrArg (fun f ↦ f ≫ δ.hom.app F) (hα (G.obj F))
  refine ⟨NatIso.ofComponents (fun F ↦
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (CategoryTheory.Endofunctor.Algebra.isoMk (e.app F) (he F)))) ?_⟩
  intro F F' f
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply CategoryTheory.Endofunctor.Algebra.Hom.ext
  exact e.hom.naturality f

private theorem restrictionSpecIso
    (R S : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (e : R ≅ S) (hS : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω S) :
    ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω R := by
  obtain ⟨α, hα⟩ := hS
  let β := Functor.isoWhiskerRight e
      (constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀)) ≪≫ α
  refine ⟨β, ?_⟩
  intro F
  have he := (e.hom.app F).hom.hom.h
  change (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀) Ω).map
      ((constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀)).map (e.hom.app F)) ≫
        (S.obj F).obj.str.hom = (R.obj F).obj.str.hom ≫ _ at he
  dsimp only [β, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [hα]
  simpa only [Functor.comp_obj, Functor.comp_map, constantExtensionHeartForget,
    sfCommonStageWeilForget, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    Endofunctor.IsoAlgebra.forget_obj, Endofunctor.IsoAlgebra.forget_map,
    Category.assoc] using congrArg (fun f ↦ f ≫ α.hom.app F) he

include hsep in
/-- Constant extension on constructible Weil hearts, with its canonical return map,
residue-degree local powers, exact cyclic-sheet equivalence, and weight filtrations.
Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152; blueprint main-20261015,
thm-zl-real-mixed-by-curves, proof paragraphs 1 and 5
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).

Proof:
1. Split k_m tensor_{k_0} k as the product indexed by its m embeddings. Base change
splits the geometric k_0-scheme into the clopen sheets of constantExtensionCyclicSheets.
The mth power of geometric Frobenius returns to sheet zero as q^m-Frobenius.
2. The finite-clopen coefficient equivalence and exact inverse image under sheet
isomorphisms give componentwise equivalences on integral, rational, and common-stage
constructible categories. Scalar localization retains the normalized compositors.
3. In semilinear sheet coordinates a Weil object is a cycle of isomorphisms
A_(i+1) to A_i, with the final arrow P^m A_0 to A_(m-1). Send it to A_0 with the
composite return arrow. Conversely put A on every sheet, identities on intermediate
arrows and the given q^m-Weil map on the final arrow, then glue the clopen pieces.
4. The two composites are naturally isomorphic to the identity: normalize a cycle
by the partial products of its transition arrows. The commuting squares of a Weil
morphism make these products natural. For m=1 there are no intermediate arrows.
5. Kernels and cokernels of Weil morphisms are computed on carriers, because
Frobenius is an exact equivalence of the underlying constructible heart. Restriction
and gluing are componentwise exact. Thus the equivalence and its inverse are exact,
identify all subobjects and quotients, and carry arbitrary finite filtrations.
6. Apply this equivalence to the actual k_0-Weil pullback along g_m. Associativity of
base change gives the original carrier, and the composite return is theta^[m]. Its
canonical inverse comparison recovers precisely this pullback before pushforward.
7. At a closed point of degree d, tensoring its residue field with k_m splits into
gcd(d,m) fields of degree m/gcd(d,m) over the original residue field. Thus f has the
stated value and #kappa(z)=#kappa(x)^f, including nonsplit residue extensions.
8. Use the specified point transports and their composition laws. The return path
at z groups f consecutive return paths at x, giving conjugacy with F_x^f. In the
two interpretations of z the absolute residue return is identical, giving f=1.
Check this at finite coefficient stages and extend scalars; common-stage descent
and independence of residue embeddings give exactly LocalConjugacy below.
9. Conjugate local operators have the same eigenvalues and the same absolute
residue size. Consequently the exact equivalence preserves punctual purity of
every weight and pure quotients. Apply it and its inverse to finite filtrations
to obtain mixedness with any specified bound. Zero objects have length-zero
filtrations; Jordan blocks are allowed throughout. No lissity is used. -/
theorem constantExtensionWeilHeartEquivalence (iota : Ω ≃+* ℂ) :
    ∃ e : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ≌
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionSheetSpec D m hm X₀ l hl Ω e.functor ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω
        (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      PreservesFiniteLimits (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      PreservesFiniteColimits (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      Nonempty (constantExtensionRestriction D m hm X₀ l hl Ω e ⋙ e.inverse ≅
        zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)) ∧
      (∀ (A : sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω) (i : Fin m),
        Nonempty ((constantExtensionSheetPullAt D m hm X₀ l hl Ω i).obj
          (e.inverse.obj A).obj.carrier ≅ A.obj.carrier)) ∧
      (∀ (z : {z : (constantExtensionModel D m hm X₀).left //
            z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
        constantExtensionResidueDegree D m hm X₀ z.val =
          m / Nat.gcd (localClosedPointDegree D X₀
            (constantExtensionClosedImage D m hm X₀ z)) m ∧
        Nat.card ((constantExtensionModel D m hm X₀).left.residueField z.val) =
          Nat.card (X₀.left.residueField
            (constantExtensionClosedImage D m hm X₀ z).val) ^
              constantExtensionResidueDegree D m hm X₀ z.val ∧
        (∀ F : sfCommonStageWeilSheaf D l hl X₀ Ω,
          ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω X₀ F
            ((constantExtensionRestriction D m hm X₀ l hl Ω e).obj F)
            (constantExtensionClosedImage D m hm X₀ z) z
            (constantExtensionResidueDegree D m hm X₀ z.val))) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω)
        (z : {z : (constantExtensionModel D m hm X₀).left //
          z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
        ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω
          (constantExtensionOriginalModel D m hm X₀) N (e.functor.obj N) z z 1) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
        (w : ℝ),
        (SfIsPunctuallyPureOfWeight D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (e.functor.obj N) w) ∧
        (SfIsMixedOfWeightsAtMost D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsMixedOfWeightsAtMost (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (e.functor.obj N) w)) := by
  obtain ⟨S, hS, hlim, hcolim, -, -, hpure, hmixed, -, hlocal⟩ :=
    constantExtensionReturnLocalOperators D m hm X₀ l hl Ω iota
  obtain ⟨T, hT, hequiv⟩ := sheetReturnExactFunctor D m hm X₀ l hl Ω
  obtain ⟨a⟩ := sheetSpecIso D m hm X₀ l hl Ω T S hT hS
  let := hequiv
  let : S.IsEquivalence := Functor.isEquivalence_of_iso a
  let e := S.asEquivalence
  obtain ⟨R, hR, hRlim, hRcolim, G, hG, ⟨b⟩⟩ :=
    constantExtensionPullbackReturn D m hm X₀ l hl Ω
  obtain ⟨c⟩ := normalizationReturnIso D m hm X₀ l hl Ω S hS R G hG
  let d : zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀) ⋙ S ≅ R :=
    Functor.isoWhiskerRight b.symm S ≪≫ c
  have hres := restrictionSpecIso D m hm X₀ l hl Ω _ _ d hR
  let := hRlim
  let := hRcolim
  have hreslim : PreservesFiniteLimits (constantExtensionRestriction D m hm X₀ l hl Ω e) :=
    preservesFiniteLimits_of_natIso d.symm
  have hrescolim :
      PreservesFiniteColimits (constantExtensionRestriction D m hm X₀ l hl Ω e) :=
    preservesFiniteColimits_of_natIso d.symm
  refine ⟨e, hS, hlim, hcolim, inferInstance, inferInstance,
    hres, hreslim, hrescolim, ?_, ?_, ?_, hlocal, ?_⟩
  · exact ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _⟩
  · intro A i
    obtain ⟨a⟩ := sheetCoordinateIso D m hm X₀ l hl Ω (e.inverse.obj A) i
    obtain ⟨α, -⟩ := hS
    exact ⟨a ≪≫ (α.app (e.inverse.obj A)).symm ≪≫
      (constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀)).mapIso (e.counitIso.app A)⟩
  · intro z
    have hz := constantExtensionResidueCompositum D m hm X₀ z
    refine ⟨hz.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2, ?_⟩
    intro F
    exact constantExtensionRestrictionLocalConjugacy D m hm X₀ l hl Ω S hS F z
  · intro N w
    exact ⟨hpure N w, hmixed N w⟩

end WeilConjectures
