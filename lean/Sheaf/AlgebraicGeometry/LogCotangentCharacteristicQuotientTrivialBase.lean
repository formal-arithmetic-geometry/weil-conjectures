/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.AlgebraicGeometry.LogDifferentialStalk
public import Sheaf.AlgebraicGeometry.LogCotangentComparison
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The characteristic quotient over a trivial log field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé X, proof of
Proposition 1.2, printed pp.136--137, canonical surjection (1)
(blueprint: lem-sfb-log-cotangent-characteristic-quotient).

The target is the residue field tensored with the group completion of the actual
characteristic monoid. The prescribed ordinary and logarithmic symbols uniquely
characterize the map. No log smoothness assumption is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.EtaleLogHom

-- Pulling back pointed base neighbourhoods gives a cocone into the source log stalk.
private noncomputable def logPullbackNeighbourhood
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    (W : Y.scheme.Etale) : X.scheme.Etale :=
  Scheme.Etale.mk (pullback.fst f.base W.hom)

private noncomputable def logPullbackPoint
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (W : Y.scheme.Etale) (w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W) :
    (Scheme.pointSmallEtale t).fiber.obj (logPullbackNeighbourhood f W) :=
  Over.homMk (pullback.lift t w.left (Over.w w).symm) (by
    change pullback.lift t w.left _ ≫ pullback.fst f.base W.hom = t
    exact pullback.lift_fst _ _ _)

private noncomputable def logPullbackCocone
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    Cocone (pointedEtaleStalkDiagram Y.logStructure.monoidSheaf (t ≫ f.base)) where
  pt := X.logStructure.stalk t
  ι :=
    { app := fun W ↦ CommMonCat.ofHom
        (f.sectionMap W.unop.1 (logPullbackNeighbourhood f W.unop.1)
          (pullback.snd f.base W.unop.1.hom) (pullback.condition (f := f.base)).symm) ≫
        X.logStructure.germ t _ (logPullbackPoint f t W.unop.1 W.unop.2)
      naturality := by
        intro W V a
        let c : logPullbackNeighbourhood f V.unop.1 ⟶
            logPullbackNeighbourhood f W.unop.1 :=
          MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst f.base V.unop.1.hom)
              (pullback.snd f.base V.unop.1.hom ≫ a.unop.val.left) (by
                rw [Category.assoc, MorphismProperty.Over.w a.unop.val]
                exact pullback.condition)) (by
                  change pullback.lift _ _ _ ≫ pullback.fst f.base W.unop.1.hom =
                    pullback.fst f.base V.unop.1.hom
                  exact pullback.lift_fst _ _ _)
        have hc := f.naturality V.unop.1 W.unop.1 _ _ a.unop.val c
          (pullback.snd f.base V.unop.1.hom) (pullback.snd f.base W.unop.1.hom)
          (pullback.condition (f := f.base)).symm (pullback.condition (f := f.base)).symm (by
            dsimp [c]
            simp)
        change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc]
        have hc' : Y.logStructure.monoidSheaf.obj.map a.unop.val.op ≫
            CommMonCat.ofHom (f.sectionMap V.unop.1 _
              (pullback.snd f.base V.unop.1.hom) (pullback.condition (f := f.base)).symm) =
            CommMonCat.ofHom (f.sectionMap W.unop.1 _
              (pullback.snd f.base W.unop.1.hom) (pullback.condition (f := f.base)).symm) ≫
              X.logStructure.monoidSheaf.obj.map c.op :=
          by
            ext s
            exact congrArg (fun g ↦ g s) hc.symm
        change (Y.logStructure.monoidSheaf.obj.map a.unop.val.op ≫ _) ≫ _ = _
        rw [hc', Category.assoc]
        congr 1
        change _ ≫ colimit.ι (pointedEtaleStalkDiagram X.logStructure.monoidSheaf t)
          (op ⟨logPullbackNeighbourhood f V.unop.1,
            logPullbackPoint f t V.unop.1 V.unop.2⟩) = _
        have hp : (Scheme.pointSmallEtale t).fiber.map c
            (logPullbackPoint f t V.unop.1 V.unop.2) =
            logPullbackPoint f t W.unop.1 W.unop.2 := by
          apply Over.OverMorphism.ext
          change pullback.lift t V.unop.2.left _ ≫
              pullback.lift (pullback.fst f.base V.unop.1.hom)
                (pullback.snd f.base V.unop.1.hom ≫ a.unop.val.left) _ =
            pullback.lift t W.unop.2.left _
          apply pullback.hom_ext
          · simp only [Category.assoc, pullback.lift_fst]
          · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
            exact congrArg (fun z ↦ z.left) a.unop.property
        exact colimit.w (pointedEtaleStalkDiagram X.logStructure.monoidSheaf t)
          (CategoryOfElements.homMk
            ⟨logPullbackNeighbourhood f V.unop.1,
              logPullbackPoint f t V.unop.1 V.unop.2⟩
            ⟨logPullbackNeighbourhood f W.unop.1,
              logPullbackPoint f t W.unop.1 W.unop.2⟩ c hp).op
    }

private theorem logBaseGerm_isUnit
    {F : Type u} [Field F] (X : FineSaturatedLogScheme.{u})
    (N : EtaleLogStructure (Spec (.of F))) (hN : N.IsFineSaturated)
    (f : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩)
    (htriv : N.trivialityLocus = Set.univ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (W : (Spec (.of F)).Etale) (V : X.scheme.Etale)
    (v : (Scheme.pointSmallEtale t).fiber.obj V) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ f.base)
    (b : N.monoidSheaf.obj.obj (op W)) :
    IsUnit (X.logStructure.germ t V v (f.sectionMap W V k hk b)) := by
  let w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W :=
    Over.homMk (v.left ≫ k) (by
      change (v.left ≫ k) ≫ W.hom = t ≫ f.base
      rw [Category.assoc, hk, ← Category.assoc]
      exact congrArg (fun g ↦ g ≫ f.base) (Over.w v))
  have hs : Subsingleton (N.characteristic (t ≫ f.base)) := by
    have hx : (Scheme.SpecToEquivOfField Ω _ (t ≫ f.base)).1 ∈ N.trivialityLocus := by
      rw [htriv]
      trivial
    exact hx Ω (t ≫ f.base) rfl
  have hb : IsUnit (N.germ (t ≫ f.base) W w b) :=
    Associates.mk_eq_one.mp (hs.elim _ _)
  let c : V ⟶ logPullbackNeighbourhood f W :=
    MorphismProperty.Over.homMk
      (pullback.lift V.hom k hk.symm) (by
        change pullback.lift V.hom k hk.symm ≫ pullback.fst f.base W.hom = V.hom
        simp)
  have hc := f.naturality W W V (logPullbackNeighbourhood f W) (𝟙 W) c k
    (pullback.snd f.base W.hom) hk (pullback.condition (f := f.base)).symm (by
      change pullback.lift V.hom k hk.symm ≫ pullback.snd f.base W.hom = k ≫ 𝟙 _
      simp)
  have hp : (Scheme.pointSmallEtale t).fiber.map c v = logPullbackPoint f t W w := by
    apply Over.OverMorphism.ext
    change v.left ≫ c.left = pullback.lift t w.left _
    apply pullback.hom_ext
    · change (v.left ≫ pullback.lift V.hom k hk.symm) ≫ _ = _
      simp only [Category.assoc, pullback.lift_fst]
      exact Over.w v
    · change (v.left ≫ pullback.lift V.hom k hk.symm) ≫ _ = _
      simp only [Category.assoc, pullback.lift_snd]
      rfl
  have he : X.logStructure.germ t V v (f.sectionMap W V k hk b) =
      (colimit.desc _ (logPullbackCocone f t)).hom (N.germ (t ≫ f.base) W w b) := by
    change _ = ((colimit.ι (pointedEtaleStalkDiagram N.monoidSheaf (t ≫ f.base))
      (op ⟨W, w⟩) ≫ colimit.desc _ (logPullbackCocone f t)) : _ ⟶ _) b
    rw [colimit.ι_desc]
    change _ = X.logStructure.germ t _ _ (f.sectionMap W _ _ _ b)
    have hc' := congrArg (fun g ↦ g b) hc
    change (X.logStructure.monoidSheaf.obj.map c.op).hom
      (f.sectionMap W _ _ _ b) = f.sectionMap W V k hk
        ((N.monoidSheaf.obj.map (𝟙 (op W))).hom b) at hc'
    rw [N.monoidSheaf.obj.map_id] at hc'
    change (X.logStructure.monoidSheaf.obj.map c.op).hom
      (f.sectionMap W _ _ _ b) = f.sectionMap W V k hk b at hc'
    rw [← hc']
    change ((X.logStructure.monoidSheaf.obj.map c.op ≫
      colimit.ι (pointedEtaleStalkDiagram X.logStructure.monoidSheaf t)
        (op ⟨V, v⟩)) : _ ⟶ _) _ = _
    exact congrArg (fun e : _ ⟶ X.logStructure.stalk t ↦ e
      (f.sectionMap W (logPullbackNeighbourhood f W) (pullback.snd f.base W.hom)
        (pullback.condition (f := f.base)).symm b))
      (colimit.w (pointedEtaleStalkDiagram X.logStructure.monoidSheaf t)
        (CategoryOfElements.homMk ⟨V, v⟩
          ⟨logPullbackNeighbourhood f W, logPullbackPoint f t W w⟩ c hp).op)
  rw [he]
  exact hb.map (colimit.desc _ (logPullbackCocone f t)).hom

/-- The canonical surjection from the logarithmic cotangent fibre to the characteristic
fibre over a trivial log field. Triviality of the base log structure is expressed by
its triviality locus being the whole spectrum; the log unit condition identifies it
with the units. The quotient `logCotangentResidue` is the geometric local ring modulo
its nonunits, hence is precisely its residue field, without identifying it with `Ω`.

Source: ILO, Exposé X, proof of Proposition 1.2, printed pp.136--137, map (1)
(blueprint: lem-sfb-log-cotangent-characteristic-quotient).

Proof plan, following the seven steps of the node:
1. Use affine-neighbourhood cofinality
   [lemma-weil-pbc-affine-neighbourhood-cofinal] to identify the geometric ring
   colimit with the strict-henselization colimit [def-weil-pbc-strict-henselization-limit].
   Locality follows from [lem-weil-pbc-strict-henselization-local-structure]. The
   residue map kills nonunits by [lem-weil-pbc-local-ring-unit-criterion].
2. Let `c(m)` be the image in the group completion of the characteristic monoid
   [def-trf-fs-log-blowup]. On the free module of [def-per-log-differential-stalk],
   send `da` to zero and `dlog m` to `1 ⊗ c(m)`, reducing coefficients to the residue ring.
3. Additivity and Leibniz relations map to zero. The multiplicative-log relation
   maps to zero because `c(mm') = c(m) + c(m')`.
4. The image of `dα(m) - α(m) dlog m` vanishes: a nonunit `α(m)` has zero residue;
   otherwise the log unit axiom makes `m` a unit and hence `c(m) = 0`. Also `c(um) = c(m)`
   for units, so the prescription is independent of the characteristic representative.
5. All base ordinary symbols vanish. Every base log section is a unit since the base
   structure is trivial; compatibility of the log morphism preserves that unit, so
   every base log relation in the relative-neighbourhood presentation vanishes too.
6. Descend through the differential relation submodule. The resulting map is linear
   over the geometric local ring. The balanced pairing `(b,w) ↦ b h(w)` induces the
   residue-linear map by [def-weil-pbc-module-tensor-product, def-weil-module-base-change].
7. The classes `c(m)` generate the characteristic group as an abelian group, so their
   pure tensors span the target and have the displayed preimages. Thus the map is
   surjective. The ordinary and logarithmic symbols span the differential module,
   so the two formulas determine a unique linear map. No step uses log smoothness. -/
theorem existsUnique_logCotangent_characteristicQuotient_of_trivialBase
    {F : Type u} [Field F] (X : FineSaturatedLogScheme.{u})
    (N : EtaleLogStructure (Spec (.of F))) (hN : N.IsFineSaturated)
    (f : EtaleLogHom X ⟨Spec (.of F), inferInstance, N, hN⟩)
    (htriv : N.trivialityLocus = Set.univ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    ∃! π : LogCotangentTarget f t →ₗ[logCotangentResidue t]
        TensorProduct ℤ (logCotangentResidue t)
          (Additive (Algebra.GrothendieckGroup (X.logStructure.characteristic t))),
      Function.Surjective π ∧
        (∀ m : X.logStructure.stalk t,
          π (TensorProduct.tmul (strictLocalRing X.scheme t) 1 (f.logDLog t m)) =
            TensorProduct.tmul ℤ 1
              (Additive.ofMul (Algebra.GrothendieckGroup.of (Associates.mk m)))) ∧
        ∀ a : strictLocalRing X.scheme t,
          π (TensorProduct.tmul (strictLocalRing X.scheme t) 1 (f.logD t a)) = 0 := by
  classical
  let A := strictLocalRing X.scheme t
  let K := logCotangentResidue t
  let C := Additive (Algebra.GrothendieckGroup (Associates (X.logStructure.stalk t)))
  let T := TensorProduct ℤ K C
  change ∃! π : LogCotangentTarget f t →ₗ[K] T,
    Function.Surjective π ∧
      (∀ m : X.logStructure.stalk t,
        π (TensorProduct.tmul A 1 (f.logDLog t m)) =
          TensorProduct.tmul ℤ 1
            (Additive.ofMul (Algebra.GrothendieckGroup.of (Associates.mk m)))) ∧
      ∀ a : A, π (TensorProduct.tmul A 1 (f.logD t a)) = 0
  let c : X.logStructure.stalk t → C := fun m ↦
    Additive.ofMul (Algebra.GrothendieckGroup.of (Associates.mk m))
  have cmul (m n : X.logStructure.stalk t) : c (m * n) = c m + c n := by
    dsimp [c]
    change Additive.ofMul _ = Additive.ofMul _
    congr 1
    rw [← Associates.mk_mul_mk, map_mul]
    rfl
  have cunit (m : X.logStructure.stalk t) (hm : IsUnit m) : c m = 0 := by
    dsimp [c]
    rw [Associates.mk_eq_one.mpr hm, map_one]
    rfl
  let v : Sum A (X.logStructure.stalk t) → T := Sum.elim (fun _ ↦ 0)
    (fun m ↦ TensorProduct.tmul ℤ 1 (c m))
  let h₀ : (Sum A (X.logStructure.stalk t) →₀ A) →ₗ[A] T :=
    Finsupp.linearCombination A v
  have hd (a : A) : h₀ (Finsupp.single (Sum.inl a) 1) = 0 := by
    simp [h₀, v]
  have hl (m : X.logStructure.stalk t) :
      h₀ (Finsupp.single (Sum.inr m) 1) = TensorProduct.tmul ℤ 1 (c m) := by
    simp [h₀, v]
  -- Check the presentation before descending and extending scalars.
  have hrel : f.logDifferentialRelations t ≤ LinearMap.ker h₀ := by
    apply Submodule.span_le.mpr
    intro z hz
    change h₀ z = 0
    rcases hz with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨m, n, rfl⟩ |
      ⟨m, rfl⟩ | ⟨W, V, v, k, hk, a, rfl⟩ | ⟨W, V, v, k, hk, b, rfl⟩
    · simp only [map_sub, hd, sub_zero]
    · simp only [map_sub, map_smul, hd, smul_zero, sub_zero]
    · simp only [map_sub, hl, cmul, TensorProduct.tmul_add, add_sub_cancel_left, sub_self]
    · rw [map_sub, hd, map_smul, hl]
      by_cases hm : IsUnit (X.logStructure.stalkAlpha t m)
      · rw [cunit m (X.logStructure.reflectsUnits Ω t m hm)]
        simp
      · have he : algebraMap A K (X.logStructure.stalkAlpha t m) = 0 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          exact Ideal.subset_span hm
        rw [TensorProduct.smul_tmul', Algebra.smul_def, he]
        simp
    · exact hd _
    · rw [hl, cunit _ (logBaseGerm_isUnit X N hN f htriv t
        W V v k hk b)]
      simp
  let h : f.LogDifferential t →ₗ[A] T := (f.logDifferentialRelations t).liftQ h₀ hrel
  have hD (a : A) : h (f.logD t a) = 0 := hd a
  have hL (m : X.logStructure.stalk t) : h (f.logDLog t m) =
      TensorProduct.tmul ℤ 1 (c m) := hl m
  let π : LogCotangentTarget f t →ₗ[K] T :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun b ↦ b • h
        map_add' := fun a b ↦ add_smul a b h
        map_smul' := fun a b ↦ by simp [smul_smul] }
  have πtmul (b : K) (q : f.LogDifferential t) :
      π (TensorProduct.tmul A b q) = b • h q := rfl
  have πL (m : X.logStructure.stalk t) :
      π (TensorProduct.tmul A 1 (f.logDLog t m)) = TensorProduct.tmul ℤ 1 (c m) := by
    rw [πtmul, one_smul, hL]
  have πD (a : A) : π (TensorProduct.tmul A 1 (f.logD t a)) = 0 := by
    rw [πtmul, one_smul, hD]
  refine ⟨π, ⟨?_, πL, πD⟩, ?_⟩
  · have cg (g : C) : ∃ m n : X.logStructure.stalk t, g = c m - c n := by
      obtain ⟨⟨a, b⟩, he⟩ := (Localization.monoidOf
        (⊤ : Submonoid (Associates (X.logStructure.stalk t)))).surj (Additive.toMul g)
      obtain ⟨m, hm⟩ := Associates.mk_surjective a
      obtain ⟨n, hn⟩ := Associates.mk_surjective b.1
      refine ⟨m, n, ?_⟩
      change Additive.toMul g = Additive.toMul (c m - c n)
      change Additive.toMul g =
        Algebra.GrothendieckGroup.of (Associates.mk m) /
          Algebra.GrothendieckGroup.of (Associates.mk n)
      apply (eq_div_iff_mul_eq').mpr
      change Additive.toMul g * Algebra.GrothendieckGroup.of b.1 =
        Algebra.GrothendieckGroup.of a at he
      rw [hm, hn]
      exact he
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero π⟩
    | tmul b g =>
      obtain ⟨m, n, rfl⟩ := cg g
      refine ⟨b • (TensorProduct.tmul A 1 (f.logDLog t m) -
        TensorProduct.tmul A 1 (f.logDLog t n)), ?_⟩
      rw [map_smul, map_sub, πL, πL, ← TensorProduct.tmul_sub,
        TensorProduct.smul_tmul']
      simp
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add π a b⟩
  · intro ψ hψ
    apply TensorProduct.AlgebraTensorModule.ext
    intro b q
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul]
    congr 1
    induction q using Submodule.Quotient.induction_on with
    | H q =>
      induction q using Finsupp.induction_linear with
      | zero => simp
      | add q r hq hr =>
        simpa only [Submodule.Quotient.mk_add, map_add, TensorProduct.tmul_add] using
          congrArg₂ (· + ·) hq hr
      | single i a =>
        rw [show Finsupp.single i a = a • Finsupp.single i 1 by simp]
        simp only [Submodule.Quotient.mk_smul]
        rw [← TensorProduct.smul_tmul, TensorProduct.tmul_eq_smul_one_tmul,
          map_smul, map_smul]
        congr 1
        cases i with
        | inl a => exact (hψ.2.2 a).trans (πD a).symm
        | inr m => exact (hψ.2.1 m).trans (πL m).symm

end AlgebraicGeometry.EtaleLogHom
