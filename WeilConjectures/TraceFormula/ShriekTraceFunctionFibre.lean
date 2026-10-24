/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChange.LocalTrace
public import WeilConjectures.TraceFormula.BaseChange.LowerShriek
-- TEMP public import WeilConjectures.TraceFormula.BaseChange.LowerShriekIterate

/-!

# The sheaf–function compatibility from the trace formula on the geometric fibres

Let `f : X ⟶ Y` be a morphism of separated schemes of finite type over `k = 𝔽_q`, with
automorphisms `e_X ≫ f = f ≫ e_Y`, and let `ȳ` be a point of `Y` of degree `n + 1`. Over
`Ω = k̄`, the base change `f̄ : X̄ ⟶ Ȳ` commutes with the model Frobenii
`Φ_X = (e_X^{n+1} ≫ F_X^{n+1}) ×_k Ω` and `Φ_Y`, and `ȳ' = (ȳ, 𝟙)` is a rational point of `Ȳ`
fixed by `Φ_Y`. Let `Z` be the fibre of `f̄` at `ȳ'`, with an endomorphism `Φ_Z` compatible with
`Φ_X`. Then

1. `t_{n+1}(Rf_!^Weil K; ȳ)` is the trace of the compactly supported Frobenius of the restriction
   `K̄|_Z` of the base change `K̄ = Lπ_X^* K` of the iterate `(K, φ^{(n+1)})`
   (`ProEtale.CondensedRing.homologyUnitEndRingHom_weilStalkSupertrace_weilLowerShriek`): by the
   local trace of a base change (`homologyUnitEndRingHom_weilStalkSupertrace`), the iterates of
   the Weil lower shriek (`weilLowerShriekPowSuccIso`), its geometric base change
   (`nonempty_weilGeometricBaseChange_weilLowerShriek_iso`) and proper base change for the model
   Weil lower shriek (`nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`);
2. the rational points of `Z` fixed by `Φ_Z` are the points of `X` of degree `n + 1` over `ȳ`
   (`ProEtale.CondensedRing.fibreFixedPointEquiv`), with the same local traces.

Hence the trace formula on the fibre `Z` gives the sheaf–function compatibility at `ȳ`
(`ProEtale.CondensedRing.weilStalkSupertrace_weilLowerShriek_eq_finsum_of_fibre`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-! ### Injectivity of `homologyUnitEndRingHom` -/

section Injective

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Placing a complex in degree `0` of the derived category is faithful. -/
instance faithful_single_comp_quotient_comp_qh (C : Type*) [Category C] [Abelian C]
    [HasDerivedCategory C] :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0 ⋙
      HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).Faithful :=
  Functor.Faithful.of_iso ((DerivedCategory.singleFunctorIsoCompQ C 0).trans
    (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso C).symm))

set_option synthInstance.maxHeartbeats 100000 in
-- The ring structure on the endomorphisms of the unit of `Dᵇc` takes long to synthesize.
omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] in
/-- Placing an endomorphism of the unit module in degree `0` is injective. -/
lemma homologyUnitEndRingHom_injective :
    Function.Injective (homologyUnitEndRingHom Λ ℓ X) := by
  intro a b h
  simp only [homologyUnitEndRingHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
  have h₁ := (RingEquiv.injective _) h
  have h₂ := (RingEquiv.injective (asIso (Functor.LaxMonoidal.ε
    (DerivedCategory.Qh (C := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))))).symm.conjRingEquiv) h₁
  exact Functor.map_injective (HomologicalComplex.single
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
      (ComplexShape.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) h₂

end Injective

/-! ### Traces over a separably closed field -/

section Dual

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsSepClosed k]

/-- The chosen right dual of an object of `Dᵇc(s)⟦ℚ̲̄_ℓ⟧` over a separably closed field: every
such object is dualizable (`nonempty_hasRightDual_point`). -/
noncomputable abbrev hasRightDualPoint (P : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    HasRightDual P :=
  (nonempty_hasRightDual_point ℓ k P).some

end Dual

attribute [local instance] hasRightDualPoint

section Frobenius

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsSepClosed k]

/-- The trace of the Frobenius of a Weil object for the identity of the base point only depends
on the Weil object up to isomorphism. -/
lemma WeilBoundedConstructible.trace_frobenius_congr
    {A B : WeilBoundedConstructible ℓ (𝟙 (point k))} (i : A ≅ B) :
    trace A.frobenius.hom = trace B.frobenius.hom :=
  trace_eq_of_iso ((WeilBoundedConstructible.forget ℓ (𝟙 (point k))).mapIso i) _ _
    (WeilBoundedConstructible.frobenius_hom_naturality i.hom)

end Frobenius

/-! ### The local and global Frobenius in degree one -/

section DegreeOne

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Φ : X ⟶ X}

omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- Abstract form of `WeilBoundedConstructible.stalkFrobenius_one`, for families of pullbacks
`U`, `V` with composition isomorphisms `c`. -/
lemma stalkFrobenius_one_aux {𝒞 D E : Type*} [Category 𝒞] [Category D] [Category E] {W X' : 𝒞}
    (U : (X' ⟶ X') → D ⥤ D) (V : (W ⟶ X') → D ⥤ E)
    (c : ∀ (a : W ⟶ X') (b : X' ⟶ X'), V (a ≫ b) ≅ U b ⋙ V a)
    {x : W ⟶ X'} {P Ψ : X' ⟶ X'} (hP : P = Ψ) (hx : x ≫ P = x) (hx' : x ≫ Ψ = x)
    {K K' : D} (hK : K' = K) (φ : (U Ψ).obj K ⟶ K) (ψ : (U P).obj K ⟶ K)
    (hψ : ψ = eqToHom (by rw [hP]) ≫ φ) :
    eqToHom (congrArg (V x).obj hK.symm) ≫
      (eqToHom (congrArg (fun f ↦ (V f).obj K') hx.symm) ≫ (c x P).hom.app K' ≫
        (V x).map ((U P).map (eqToHom hK) ≫ ψ ≫ eqToHom hK.symm)) ≫
      eqToHom (congrArg (V x).obj hK) =
    eqToHom (congrArg (fun f ↦ (V f).obj K) hx'.symm) ≫ (c x Ψ).hom.app K ≫ (V x).map φ := by
  subst hP hK hψ
  simp

/-- The local Frobenius `F_{x,1}` of degree one is the Frobenius of the stalk at `x`. -/
lemma WeilBoundedConstructible.stalkFrobenius_one (K : WeilBoundedConstructible ℓ Φ)
    (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ 1 = x) (hx' : x ≫ Φ = x) :
    K.stalkFrobenius 1 x hx = ((weilStalk ℓ Φ x hx').obj K).frobenius.hom := by
  refine (K.stalkFrobenius_eq_cast 1 x hx).trans (Eq.trans ?_
    (weilStalk_obj_frobenius_hom_eq x hx' K).symm)
  exact stalkFrobenius_one_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (frobeniusIterate_one Φ) hx hx' (K.iterate_carrier 1) K.str.hom _
    ((K.iterateStr_hom_eq_frobeniusCoefficientIterate 1).trans
      (frobeniusCoefficientIterate_one K.str.hom))

set_option linter.overlappingInstances false in
/-- The global operator `F_{c,1}` of degree one is the compactly supported Frobenius. -/
lemma WeilBoundedConstructible.globalOperator_one (K : WeilBoundedConstructible ℓ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left] [IsFinite (frobeniusIterate Φ 1).left]
    [IsUniversalHomeomorphism (frobeniusIterate Φ 1).left] :
    K.globalOperator 1 = K.compactFrobenius := by
  rw [globalOperator_eq_frobeniusCompactOperator, frobeniusCompactOperator_one,
    compactFrobenius_eq]

end DegreeOne

/-! ### The fixed points of the fibre -/

section Fibre

variable {k : Type u} [Field k] [Finite k]
  {X Y : Over (Spec (.of k))} {eX : X ≅ X} {eY : Y ≅ Y} {f : X ⟶ Y}
  (hf : eX.hom ≫ f = f ≫ eY.hom) {n : ℕ} (y : frobeniusFixedPoints eY n)
  {Z : Over (Spec (.of (AlgebraicClosure k)))} {ΦZ : Z ⟶ Z}
  {i : Z ⟶ (geometricBaseChange k (AlgebraicClosure k)).obj X}
  (hi : ΦZ ≫ i = i ≫ baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (eX.powSucc n).hom)
  (hZ : IsPullback i (toPoint Z) ((geometricBaseChange k (AlgebraicClosure k)).map f)
    (geometricBaseChangePoint y.1 y.2.1))

include hZ in
/-- A rational point `z` of the fibre `Z` gives the point `(z ≫ i) ≫ π_X` of `X` over `ȳ`. -/
lemma fibre_left_comp_proj_comp (z : RationalPoint Z) :
    ((z ≫ i).left ≫ geometricBaseChangeProj X) ≫ f.left = y.1 := by
  have h : (z ≫ i ≫ (geometricBaseChange k (AlgebraicClosure k)).map f).left =
      (geometricBaseChangePoint y.1 y.2.1).left := by
    rw [hZ.w, ← Category.assoc, toPoint_ext (z ≫ toPoint Z) (𝟙 _), Category.id_comp]
  rw [Category.assoc, ← geometricBaseChange_map_left_comp_proj, ← Category.assoc,
    ← Over.comp_left, Category.assoc, h, geometricBaseChangePoint_left_comp_proj]

include hi hZ in
/-- **The fixed points of the fibre**: the rational points of the fibre `Z` of `f̄` at `ȳ'`
fixed by `Φ_Z` are the points of `X` of degree `n + 1` over `ȳ`, through `z ↦ (z ≫ i) ≫ π_X`. -/
noncomputable def fibreFixedPointEquiv :
    FixedPoint ΦZ 1 ≃ {x : frobeniusFixedPoints eX n // x.1 ≫ f.left = y.1} where
  toFun z := ⟨(frobeniusFixedPointsEquiv eX n).symm ⟨z.1 ≫ i, by
    have hz : z.1 ≫ ΦZ = z.1 := (congrArg (z.1 ≫ ·) (frobeniusIterate_one ΦZ)).symm.trans z.2
    rw [Category.assoc, ← hi, ← Category.assoc, hz]⟩,
    fibre_left_comp_proj_comp y hZ z.1⟩
  invFun x := ⟨hZ.lift (geometricBaseChangePoint x.1.1 x.1.2.1) (𝟙 _) (by
      refine rationalPoint_ext ?_
      rw [Category.id_comp, Over.comp_left, Category.assoc,
        geometricBaseChange_map_left_comp_proj, geometricBaseChangePoint_left_comp_proj_assoc,
        geometricBaseChangePoint_left_comp_proj, x.2]), by
    rw [frobeniusIterate_one]
    refine hZ.hom_ext ?_ (toPoint_ext _ _)
    rw [Category.assoc, hi, IsPullback.lift_fst_assoc, IsPullback.lift_fst]
    exact ((frobeniusFixedPointsEquiv eX n) x.1).2⟩
  left_inv z := Subtype.ext (hZ.hom_ext (by
    rw [IsPullback.lift_fst]
    exact geometricBaseChangePoint_left_comp_proj_eq (z.1 ≫ i)) (toPoint_ext _ _))
  right_inv x := Subtype.ext (Subtype.ext
    ((congrArg (fun t ↦ t.left ≫ geometricBaseChangeProj X) (hZ.lift_fst _ _ _)).trans
      (geometricBaseChangePoint_left_comp_proj _ _)))

end Fibre

end AlgebraicGeometry.ProEtale.CondensedRing
