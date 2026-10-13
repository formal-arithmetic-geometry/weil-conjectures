/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds

/-!
# The trace formula through the Weil `!`-pushforward

For a morphism `f₀ : X₀ ⟶ Y₀` of separated schemes of finite type over a finite field `k`, the
trace formula for `X₀` follows from the trace formula for `Y₀` and for all fibres
`X₀ ×_{Y₀} Spec k'` over points of `Y₀` with values in finite fields `k'`: push forward with the
Weil `!`-pushforward (`WeilComplex.trace_globalOperator_lowerShriekPush`), whose stalk
Frobenius at a fixed point is the degree-one global operator of the fibre
(`WeilComplex.exists_isModelFrobenius_fibre`). This is the argument of Step 4 of the proof of
blueprint `thm-trf-coefficient-morphism-trace-formula`, also used in Step 2 for `𝔸¹ ⊆ ℙ¹`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.exists_isFrobenius`: every scheme over `k` has a `#k`-power
  Frobenius.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_comp_of_traceFormulaHolds_fibre`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.Scheme

/-- The absolute Frobenius is natural: for `g : Y ⟶ X` between schemes in which the prime `p`
vanishes, `g ≫ F_X = F_Y ≫ g`. -/
lemma iterateFrobenius_naturality {X Y : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) (g : Y ⟶ X) :
    g ≫ X.iterateFrobenius hp hX n = Y.iterateFrobenius hp hY n ≫ g := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext s
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, preimage_iterateFrobenius,
    Hom.comp_app, eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact map_pow (g.app U).hom s (p ^ n)

/-- On an affine scheme `Spec R`, the absolute Frobenius is `Spec` of the `p ^ n`-power map. -/
lemma specMap_eq_iterateFrobenius {R : CommRingCat.{u}} {p : ℕ} (hp : p.Prime)
    (hR : (p : Γ(Spec R, ⊤)) = 0) (n : ℕ) {φ : R ⟶ R} (hφ : ∀ r, φ.hom r = r ^ p ^ n) :
    Spec.map φ = (Spec R).iterateFrobenius hp hR n := by
  refine ext_of_isAffine ?_
  ext s
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, hφ,
    ← map_pow]
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {k : Type u} [Field k] [Finite k]

namespace GeometricOperations

/-- The stalk of a complex `K ∈ Dᵇctf(Y)` at a section `y` of a geometric scheme
`a_Y : Y ⟶ Spec Ω` is dualizable: it lies in `Dᵇctf(Spec Ω)`, and is identified with its
compactly supported cohomology `R(𝟙)_! (Ly^* K)`, which is perfect. -/
lemma nonempty_hasRightDual_leftDerivedUpperStar_of_comp_eq_id {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (G : GeometricOperations A (Spec (.of Ω))) {Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of Ω)) [IsGeometric aY]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hK : G.ctf Y K)
    (y : Spec (.of Ω) ⟶ Y) (hy : y ≫ aY = 𝟙 _) :
    Nonempty (HasRightDual (((upperStar A y).leftDerivedFunctor).obj K)) := by
  have hP := G.ctf_upperStar y (.mk (aX := 𝟙 _) (aY := aY) hy) hK
  obtain ⟨d⟩ := G.nonempty_hasRightDual_rightDerivedLowerShriek (𝟙 _) hP
  let e : ((upperStar A y).leftDerivedFunctor).obj K ≅
      (rightDerivedLowerShriek A (𝟙 (Spec (.of Ω)))).obj
        (((upperStar A y).leftDerivedFunctor).obj K) :=
    ((G.ctf _).ι.mapIso ((G.lowerShriekId _ (.id (𝟙 _))).app ⟨_, hP⟩)).symm
  exact ⟨{ rightDual := HasRightDual.rightDual
              ((rightDerivedLowerShriek A (𝟙 (Spec (.of Ω)))).obj
                (((upperStar A y).leftDerivedFunctor).obj K))
           exact := exactPairingCongrLeft e }⟩

end GeometricOperations

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- Transport of a stalk endomorphism along a propositional equality of endomorphisms: the
stalk endomorphism `Lx^* K ≃ L(x ≫ g₁)^* K ≃ Lx^* Lg₁^* K ⟶ Lx^* K` built from `g₁ = g` and
`c : Lg^* K ⟶ K` is the one built from `g` and `c`. -/
lemma leftDerivedUpperStar_stalk_congr_aux {T Y : Scheme.{u}} {x : T ⟶ Y} {g₁ g : Y ⟶ Y}
    (e : g₁ = g) (hx₁ : x ≫ g₁ = x) (hx : x ≫ g = x)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (c : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K) :
    (leftDerivedUpperStarCongr A hx₁).inv.app K ≫ (leftDerivedUpperStarComp A x g₁).hom.app K ≫
        ((upperStar A x).leftDerivedFunctor).map ((leftDerivedUpperStarCongr A e).hom.app K ≫ c) =
      (leftDerivedUpperStarCongr A hx).inv.app K ≫ (leftDerivedUpperStarComp A x g).hom.app K ≫
        ((upperStar A x).leftDerivedFunctor).map c := by
  subst e
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

namespace WeilComplex

variable {s X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s} (W : WeilComplex (A := A) aX)

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- If `f` intertwines the Frobenius morphisms of two Weil complexes, it intertwines their
iterates. -/
lemma frobeniusIterate_comp_eq_comp (W' : WeilComplex (A := A) aY) (f : X ⟶ Y)
    (h : f ≫ W'.frobenius = W.frobenius ≫ f) (m : ℕ) :
    W.frobeniusIterate m ≫ f = f ≫ W'.frobeniusIterate m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [frobeniusIterate_succ, frobeniusIterate_succ, Category.assoc, ih, ← Category.assoc,
      ← Category.assoc, h]

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- The Frobenius of the fibre `X_y` is the restriction of `Φ_m`. -/
@[reassoc (attr := simp)]
lemma fibre_frobenius_fst (f : X ⟶ Y) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY) (y : s ⟶ Y) (hy : y ≫ gY = y) :
    (W.fibre f m gY hfg y hy).frobenius ≫ pullback.fst f y =
      pullback.fst f y ≫ W.frobeniusIterate m :=
  pullback.lift_fst _ _ _

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- The Frobenius of the fibre `X_y` is a morphism over `s`. -/
@[reassoc (attr := simp)]
lemma fibre_frobenius_snd (f : X ⟶ Y) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY) (y : s ⟶ Y) (hy : y ≫ gY = y) :
    (W.fibre f m gY hfg y hy).frobenius ≫ pullback.snd f y = pullback.snd f y :=
  pullback.lift_snd _ _ _

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- A section of the fibre `X_y ⟶ s` maps to a section of `a_X`. -/
lemma comp_fst_comp_eq_id {f : X ⟶ Y} (hf : f ≫ aY = aX) {y : s ⟶ Y} (hy : y ≫ aY = 𝟙 s)
    {x : s ⟶ pullback f y} (hx : x ≫ pullback.snd f y = 𝟙 s) :
    (x ≫ pullback.fst f y) ≫ aX = 𝟙 s := by
  subst hf
  rw [Category.assoc, pullback.condition_assoc, hy, Category.comp_id, hx]

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- A point of the fibre `X_y` fixed by its Frobenius maps to a point of `X` fixed by `Φ_m`. -/
lemma comp_fst_frobeniusIterate (f : X ⟶ Y) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY) (y : s ⟶ Y) (hy : y ≫ gY = y)
    (x : s ⟶ pullback f y) (hx : x ≫ (W.fibre f m gY hfg y hy).frobeniusIterate 1 = x) :
    (x ≫ pullback.fst f y) ≫ W.frobeniusIterate m = x ≫ pullback.fst f y := by
  rw [Category.assoc, ← W.fibre_frobenius_fst f m gY hfg y hy, ← Category.assoc,
    ← frobeniusIterate_one, hx]

/-- A section of the fibre `X_ȳ ⟶ s` fixed by its Frobenius gives, by composing with the
projection `X_ȳ ⟶ X`, a section of `a_X` fixed by `Φ_m`. -/
noncomputable def fibreFixedPoint (f : X ⟶ Y) (hf : f ≫ aY = aX) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY)
    (y : {y : s ⟶ Y // y ≫ aY = 𝟙 s ∧ y ≫ gY = y})
    (x : {x : s ⟶ pullback f y.1 // x ≫ pullback.snd f y.1 = 𝟙 s ∧
      x ≫ (W.fibre f m gY hfg y.1 y.2.2).frobeniusIterate 1 = x}) :
    {x : s ⟶ X // x ≫ aX = 𝟙 s ∧ x ≫ W.frobeniusIterate m = x} :=
  ⟨x.1 ≫ pullback.fst f y.1, comp_fst_comp_eq_id hf y.2.1 x.2.1,
    W.comp_fst_frobeniusIterate f m gY hfg y.1 y.2.2 x.1 x.2.2⟩

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- Composition with the projection is injective on the fixed sections of a fibre. -/
lemma fibreFixedPoint_injective (f : X ⟶ Y) (hf : f ≫ aY = aX) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY)
    (y : {y : s ⟶ Y // y ≫ aY = 𝟙 s ∧ y ≫ gY = y}) :
    Function.Injective (W.fibreFixedPoint f hf m gY hfg y) := fun x₁ x₂ h ↦
  Subtype.ext (pullback.hom_ext (congrArg Subtype.val h) (by rw [x₁.2.1, x₂.2.1]))

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- Item 3 of blueprint `lem-trf-weil-shriek-operator-fibres`: the sections of `a_X` fixed by
`Φ_m` are the disjoint union, over the sections `ȳ` of `a_Y` fixed by `g_Y`, of the fixed
sections of the fibres `X_ȳ`. -/
lemma bijective_fibreFixedPoint (f : X ⟶ Y) (hf : f ≫ aY = aX) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY) :
    Function.Bijective (fun z : (Σ y : {y : s ⟶ Y // y ≫ aY = 𝟙 s ∧ y ≫ gY = y},
        {x : s ⟶ pullback f y.1 // x ≫ pullback.snd f y.1 = 𝟙 s ∧
          x ≫ (W.fibre f m gY hfg y.1 y.2.2).frobeniusIterate 1 = x}) ↦
      W.fibreFixedPoint f hf m gY hfg z.1 z.2) := by
  refine ⟨fun ⟨y₁, x₁⟩ ⟨y₂, x₂⟩ h ↦ ?_, fun x ↦ ?_⟩
  · have h' : x₁.1 ≫ pullback.fst f y₁.1 = x₂.1 ≫ pullback.fst f y₂.1 :=
      congrArg Subtype.val h
    obtain rfl : y₁ = y₂ := Subtype.ext <| calc
      y₁.1 = (x₁.1 ≫ pullback.snd f y₁.1) ≫ y₁.1 := by rw [x₁.2.1, Category.id_comp]
      _ = (x₁.1 ≫ pullback.fst f y₁.1) ≫ f := by
        rw [Category.assoc, Category.assoc, pullback.condition]
      _ = (x₂.1 ≫ pullback.fst f y₂.1) ≫ f := by rw [h']
      _ = y₂.1 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x₂.2.1, Category.id_comp]
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext (pullback.hom_ext h' (by rw [x₁.2.1, x₂.2.1]))))
  · refine ⟨⟨⟨x.1 ≫ f, by rw [Category.assoc, hf, x.2.1],
      by rw [Category.assoc, ← hfg, ← Category.assoc, x.2.2]⟩,
      ⟨pullback.lift x.1 (𝟙 s) (Category.id_comp _).symm, pullback.lift_snd _ _ _, ?_⟩⟩,
      Subtype.ext (pullback.lift_fst _ _ _)⟩
    rw [frobeniusIterate_one]
    apply pullback.hom_ext
    · rw [Category.assoc, fibre_frobenius_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      exact x.2.2
    · rw [Category.assoc, fibre_frobenius_snd]

omit [Etale.HasBoundedBelowUpperShrieks A] in
/-- The stalk Frobenius of the fibre `X_ȳ` (in degree one) at a fixed point `x` is conjugate,
along `Lx^* L(pr)^* K ≃ L(x ≫ pr)^* K`, to the stalk Frobenius of `φ_m` at the image of `x` in
`X`, so the two have the same trace. -/
theorem trace_stalkFrobenius_fibre (f : X ⟶ Y) (m : ℕ) (gY : Y ⟶ Y)
    (hfg : W.frobeniusIterate m ≫ f = f ≫ gY) (y : s ⟶ Y) (hy : y ≫ gY = y)
    (x : s ⟶ pullback f y) (hx : x ≫ (W.fibre f m gY hfg y hy).frobeniusIterate 1 = x)
    [HasRightDual (((upperStar A x).leftDerivedFunctor).obj (W.fibre f m gY hfg y hy).obj)]
    [HasRightDual (((upperStar A (x ≫ pullback.fst f y)).leftDerivedFunctor).obj W.obj)] :
    MonoidalCategory.trace ((W.fibre f m gY hfg y hy).stalkFrobenius 1 x hx) =
      MonoidalCategory.trace (W.stalkFrobenius m (x ≫ pullback.fst f y)
        (W.comp_fst_frobeniusIterate f m gY hfg y hy x hx)) := by
  have hx₁ : x ≫ (W.fibre f m gY hfg y hy).frobenius = x := by
    rwa [← frobeniusIterate_one]
  refine (trace_eq_of_iso
    (X' := ((upperStar A x).leftDerivedFunctor).obj (W.fibre f m gY hfg y hy).obj)
    ((leftDerivedUpperStarComp A x (pullback.fst f y)).app W.obj) _ _ ?_).symm
  rw [stalkFrobenius, stalkFrobenius, coeffIterate_one,
    leftDerivedUpperStar_stalk_congr_aux _ hx hx₁]
  exact leftDerivedUpperStarComp_stalk_squareIso_aux ⟨pullback.lift_fst _ _ _⟩ hx₁ _
    (W.coeffIterate m)

end WeilComplex

/-- Every scheme `X₀` over a finite field `k` has a `#k`-power Frobenius, the absolute Frobenius
`Scheme.iterateFrobenius` for `#k = pⁿ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_isFrobenius {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) :
    ∃ F : X₀ ⟶ X₀, F.IsFrobenius (Nat.card k) := by
  let := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have hX : (ringChar k : Γ(X₀, ⊤)) = 0 := by
    rw [← map_natCast f₀.appTop.hom, ← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom,
      ringChar.Nat.cast_ringChar, map_zero, map_zero]
  refine ⟨X₀.iterateFrobenius hp hX n, fun R t φ hφ ↦ ?_⟩
  have hR : (ringChar k : Γ(Spec R, ⊤)) = 0 := by
    rw [← map_natCast t.appTop.hom, hX, map_zero]
  rw [Nat.card_eq_fintype_card, hcard] at hφ
  rw [Scheme.iterateFrobenius_naturality hp hX hR, Scheme.specMap_eq_iterateFrobenius hp hR n hφ]

/-- The trace formula for `f₀ ≫ g₀ : X₀ ⟶ Spec k` follows from the trace formula for `g₀` and for
the fibres `X₀ ×_{Y₀, y₀} Spec k'` of `f₀ : X₀ ⟶ Y₀` at all points `y₀` of `Y₀` with values in
finite fields `k'`, through the Weil `!`-pushforward along `f₀`. -/
theorem traceFormulaHolds_comp_of_traceFormulaHolds_fibre {X₀ Y₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Spec (.of k)) [IsSeparated g₀] [LocallyOfFiniteType g₀]
    [QuasiCompact g₀] [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (hY : TraceFormulaHolds A g₀)
    (hfib : ∀ {k' : Type u} [Field k'] [Finite k'] (y₀ : Spec (.of k') ⟶ Y₀),
      TraceFormulaHolds A (pullback.snd f₀ y₀)) :
    TraceFormulaHolds A (f₀ ≫ g₀) := by
  intro Ω _ _ G X aX _ _ W σ p hΦ hctf m hm _ _ hX _
  -- (a) the Frobenius of `Y₀` and (b) the base change `Y = Y₀ ×_k Ω`
  obtain ⟨F₀, hF₀, hpF⟩ := hΦ.exists_isFrobenius
  obtain ⟨FY, hFY⟩ := g₀.exists_isFrobenius
  have hYpb := IsPullback.of_hasPullback g₀ σ
  obtain ⟨frobY, hYfrob, hpY⟩ : ∃ frobY : pullback g₀ σ ⟶ pullback g₀ σ,
      frobY ≫ pullback.snd g₀ σ = pullback.snd g₀ σ ∧
        frobY ≫ pullback.fst g₀ σ = pullback.fst g₀ σ ≫ FY :=
    ⟨pullback.lift (pullback.fst g₀ σ ≫ FY) (pullback.snd g₀ σ)
      (by rw [Category.assoc, hFY.comp_eq g₀, pullback.condition]),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  obtain ⟨f, hf, hpf⟩ : ∃ f : X ⟶ pullback g₀ σ, f ≫ pullback.snd g₀ σ = aX ∧
      f ≫ pullback.fst g₀ σ = p ≫ f₀ :=
    ⟨pullback.lift (p ≫ f₀) aX (by simpa using hΦ.isPullback.w),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  have h : f ≫ frobY = W.frobenius ≫ f := comp_eq_comp_of_isPullback hYpb
    (hF₀.comp_eq_comp (f₀ ≫ g₀) hFY f₀) W.frobenius_comp hYfrob hpF hpY hpf hf
  -- instances
  have : IsFinite W.frobenius := hF₀.isFinite_of_isPullback hΦ.isPullback W.frobenius_comp hpF
  have : IsFinite frobY := hFY.isFinite_of_isPullback hYpb hYfrob hpY
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd g₀ σ)
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd g₀ σ)
  have : IsSeparated (f ≫ pullback.snd g₀ σ) := by
    rw [hf]
    infer_instance
  have : LocallyOfFiniteType (f ≫ pullback.snd g₀ σ) := by
    rw [hf]
    infer_instance
  have : QuasiCompact (f ≫ pullback.snd g₀ σ) := by
    rw [hf]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (pullback.snd g₀ σ)
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (pullback.snd g₀ σ)
  have : QuasiCompact f := QuasiCompact.of_comp f (pullback.snd g₀ σ)
  -- (c) the Weil `!`-pushforward and the trace formula on `Y`
  have hL : (W.lowerShriekPush G hctf f hf frobY hYfrob h).IsModelFrobenius g₀ σ
      (pullback.fst g₀ σ) := ⟨hYpb, FY, hFY, hpY⟩
  have hctfL := G.ctf_lowerShriek f (.mk hf) hctf
  have := hL.isFinite_frobeniusIterate _ m
  have : IsProper ((W.lowerShriekPush G hctf f hf frobY hYfrob h).graph G hctfL m).snd :=
    inferInstanceAs
      (IsProper ((W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m))
  let : HasRightDual ((rightDerivedLowerShriek A (pullback.snd g₀ σ)).obj
      (W.lowerShriekPush G hctf f hf frobY hYfrob h).obj) :=
    (G.nonempty_hasRightDual_rightDerivedLowerShriek _ hctfL).some
  let hLst (y : {y : Spec (.of Ω) ⟶ pullback g₀ σ // y ≫ pullback.snd g₀ σ = 𝟙 _ ∧
      y ≫ (W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m = y}) :
      HasRightDual (((upperStar A y.1).leftDerivedFunctor).obj
        (W.lowerShriekPush G hctf f hf frobY hYfrob h).obj) :=
    (G.nonempty_hasRightDual_leftDerivedUpperStar_of_comp_eq_id _ hctfL y.1 y.2.1).some
  have := hL.finite_fixedPoints (m := m) (by omega)
  let := Fintype.ofFinite {y : Spec (.of Ω) ⟶ pullback g₀ σ // y ≫ pullback.snd g₀ σ = 𝟙 _ ∧
      y ≫ (W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m = y}
  have hfg := W.frobeniusIterate_comp_eq_comp (W.lowerShriekPush G hctf f hf frobY hYfrob h) f h m
  -- (d) the global operators of `W` and of its pushforward have the same trace
  rw [← W.trace_globalOperator_lowerShriekPush G hctf f hf frobY hYfrob h m,
    hY G hL hctfL m hm]
  -- (f) regroup the fixed points of `X` along the fibres
  let hfin (y : {y : Spec (.of Ω) ⟶ pullback g₀ σ // y ≫ pullback.snd g₀ σ = 𝟙 _ ∧
      y ≫ (W.lowerShriekPush G hctf f hf frobY hYfrob h).frobeniusIterate m = y}) :
      Fintype {x : Spec (.of Ω) ⟶ pullback f y.1 // x ≫ pullback.snd f y.1 = 𝟙 _ ∧
        x ≫ (W.fibre f m _ hfg y.1 y.2.2).frobeniusIterate 1 = x} :=
    Fintype.ofInjective _ (W.fibreFixedPoint_injective f hf m _ hfg y)
  refine Eq.trans ?_ (Fintype.sum_bijective _ (W.bijective_fibreFixedPoint f hf m _ hfg) _ _
    fun _ ↦ rfl)
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  -- (e) the stalk at `ȳ` is the degree-one global operator of the fibre
  obtain ⟨k', _, _, σ', y₀, hy₀, -, hfibM, htr⟩ := WeilComplex.exists_isModelFrobenius_fibre G W
    hctf f hf frobY hYfrob h hΦ hYpb FY hFY hpY f₀ rfl hpf m hm hfg y.1 y.2.1 y.2.2
  have hctfF : G.ctf (pullback f y.1) (W.fibre f m _ hfg y.1 y.2.2).obj :=
    G.ctf_upperStar (pullback.fst f y.1) (.mk (aX := pullback.snd f y.1) (aY := aX)
      (by
        have := pullback.condition_assoc (f := f) (g := y.1) (pullback.snd g₀ σ)
        rwa [hf, y.2.1, Category.comp_id] at this)) hctf
  have := hfibM.isFinite_frobeniusIterate _ 1
  have : IsProper ((W.fibre f m _ hfg y.1 y.2.2).graph G hctfF 1).snd :=
    inferInstanceAs (IsProper ((W.fibre f m _ hfg y.1 y.2.2).frobeniusIterate 1))
  let : HasRightDual ((rightDerivedLowerShriek A (pullback.snd f y.1)).obj
      (W.fibre f m _ hfg y.1 y.2.2).obj) :=
    (G.nonempty_hasRightDual_rightDerivedLowerShriek _ hctfF).some
  let hFst (x : {x : Spec (.of Ω) ⟶ pullback f y.1 // x ≫ pullback.snd f y.1 = 𝟙 _ ∧
      x ≫ (W.fibre f m _ hfg y.1 y.2.2).frobeniusIterate 1 = x}) :
      HasRightDual (((upperStar A x.1).leftDerivedFunctor).obj
        (W.fibre f m _ hfg y.1 y.2.2).obj) :=
    let : HasRightDual (((upperStar A (x.1 ≫ pullback.fst f y.1)).leftDerivedFunctor).obj
        W.obj) := hX (W.fibreFixedPoint f hf m _ hfg y x)
    { rightDual := HasRightDual.rightDual
        (((upperStar A (x.1 ≫ pullback.fst f y.1)).leftDerivedFunctor).obj W.obj)
      exact := exactPairingCongrLeft
        ((leftDerivedUpperStarComp A x.1 (pullback.fst f y.1)).app W.obj).symm }
  have hfibY : TraceFormulaHolds A (pullback.snd f₀ y₀) := @hfib k' _ _ y₀
  rw [htr hctfF, hfibY G hfibM hctfF 1 le_rfl]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  let : HasRightDual (((upperStar A (x.1 ≫ pullback.fst f y.1)).leftDerivedFunctor).obj
      W.obj) := hX (W.fibreFixedPoint f hf m _ hfg y x)
  exact W.trace_stalkFrobenius_fibre f m _ hfg y.1 y.2.2 x.1 x.2.2

end AlgebraicGeometry.ProEtale
