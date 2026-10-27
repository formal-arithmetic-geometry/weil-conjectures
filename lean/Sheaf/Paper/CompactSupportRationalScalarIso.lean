/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction

/-! # A step of normalized compact-support scalar comparison

Source: lem-fix-operation-reduction, compact-support and final paragraphs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)
open TensorProduct

private theorem localizeIso
    {R S : Type*} [CommRing R] [CommRing S]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear S D] (p : R) (q : S)
    (F G : C ⥤ D)
    (F' G' : ScalarLocalization R C p ⥤ ScalarLocalization S D q)
    [F'.Additive] [G'.Additive]
    (ψ : Localization.Away p → Localization.Away q)
    (hF : ∀ K, F'.obj K = ⟨F.obj K.obj⟩)
    (hG : ∀ K, G'.obj K = ⟨G.obj K.obj⟩)
    (hFm : ∀ (K M : ScalarLocalization R C p) (a : Localization.Away p)
      (f : K.obj ⟶ M.obj),
      HEq (F'.map (a ⊗ₜ[R] f))
        (ψ a ⊗ₜ[S] F.map f : (⟨F.obj K.obj⟩ : ScalarLocalization S D q) ⟶
          ⟨F.obj M.obj⟩))
    (hGm : ∀ (K M : ScalarLocalization R C p) (a : Localization.Away p)
      (f : K.obj ⟶ M.obj),
      HEq (G'.map (a ⊗ₜ[R] f))
        (ψ a ⊗ₜ[S] G.map f : (⟨G.obj K.obj⟩ : ScalarLocalization S D q) ⟶
          ⟨G.obj M.obj⟩))
    (e : F ≅ G) :
    ∃ e' : F' ≅ G', ∀ K,
      HEq (e'.hom.app K) ((ScalarLocalization.localization S D q).map (e.hom.app K.obj)) := by
  let Q := ScalarLocalization.localization S D q
  let e' : F' ≅ G' := NatIso.ofComponents
    (fun K ↦ eqToIso (hF K) ≪≫ Q.mapIso (e.app K.obj) ≪≫ (eqToIso (hG K)).symm)
    (by
      intro K M f
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul a f =>
        rw [(conj_eqToHom_iff_heq _ _ (hF K) (hF M)).2 (hFm K M a f),
          (conj_eqToHom_iff_heq _ _ (hG K) (hG M)).2 (hGm K M a f)]
        have hn :
            (ψ a ⊗ₜ[S] F.map f : (⟨F.obj K.obj⟩ : ScalarLocalization S D q) ⟶
                ⟨F.obj M.obj⟩) ≫ Q.map (e.hom.app M.obj) =
              Q.map (e.hom.app K.obj) ≫
                (ψ a ⊗ₜ[S] G.map f : (⟨G.obj K.obj⟩ : ScalarLocalization S D q) ⟶
                  ⟨G.obj M.obj⟩) := by
          change ScalarLocalization.composition S D q _ _ _
              (1 ⊗ₜ[S] e.hom.app M.obj) (ψ a ⊗ₜ[S] F.map f) =
            ScalarLocalization.composition S D q _ _ _
              (ψ a ⊗ₜ[S] G.map f) (1 ⊗ₜ[S] e.hom.app K.obj)
          rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul]
          simp only [one_mul, mul_one, e.hom.naturality f]
        simpa only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
          Functor.mapIso_hom, Iso.app_hom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
          eqToHom_refl, Category.id_comp] using
            congrArg (fun z ↦ eqToHom (hF K) ≫ z ≫ eqToHom (hG M).symm) hn
      | add f g hf hg =>
        rw [F'.map_add, G'.map_add]
        rw [Preadditive.add_comp, Preadditive.comp_add, hf, hg])
  refine ⟨e', ?_⟩
  intro K
  apply (conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1
  rfl

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (J : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (J.map f) (J.map g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg J.map (eq_of_heq hf))

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

private theorem rationalScalarIsoOfFields
    (A B : Type u) [Field A] [Field B]
    [Algebra (Padic l) A] [Algebra (Padic l) B]
    [FiniteDimensional (Padic l) A] [FiniteDimensional (Padic l) B]
    (ι : A →ₐ[Padic l] B)
    (b : sfCompactSupportFiniteIntegralFunctor l K₀ hl c A ⋙
        sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) A B ι Y ≅
      sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) A B ι X ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c B) :
    ∃ β : sfCompactSupportFiniteFunctor l K₀ hl c A ⋙
          sfRationalScalarExtension l A Y 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) B ι ≅
        sfRationalScalarExtension l A X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) B ι ⋙
          sfCompactSupportFiniteFunctor l K₀ hl c B,
        ∀ K : sfRationalConstructibleCategory l A X, HEq (β.hom.app K)
          ((sfRationalConstructibleLocalization l B Y).map (b.hom.app K.obj)) := by
  let R := Padic.coefficientExtensionIntegers l A
  let S := Padic.coefficientExtensionIntegers l B
  let p := Padic.coefficientExtensionUniformizer l A
  let q := Padic.coefficientExtensionUniformizer l B
  let FE := sfCompactSupportFiniteIntegralFunctor l K₀ hl c A
  let FL := sfCompactSupportFiniteIntegralFunctor l K₀ hl c B
  let TX := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) A B ι X
  let TY := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) A B ι Y
  let GE := sfCompactSupportFiniteFunctor l K₀ hl c A
  let rationalTarget := sfCompactSupportFiniteFunctor l K₀ hl c B
  let SX := sfRationalScalarExtension l A X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) B ι
  let SY := sfRationalScalarExtension l A Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) B ι
  let ψ (a : Localization.Away p) :=
    (sfRationalCoefficientEquiv l B).symm (ι (sfRationalCoefficientEquiv l A a))
  have hSX := (sfRationalScalarExtension_existsUnique l A X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) B ι).exists.choose_spec
  have hSY := (sfRationalScalarExtension_existsUnique l A Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) B ι).exists.choose_spec
  have hGE (K M : sfRationalConstructibleCategory l A X)
      (a : Localization.Away p) (f : K.obj ⟶ M.obj) :
      GE.map (a ⊗ₜ[R] f) = a ⊗ₜ[R] FE.map f := by
    exact LinearMap.baseChange_tmul _ _ _
  have hrationalTarget (K M : sfRationalConstructibleCategory l B X)
      (a : Localization.Away q) (f : K.obj ⟶ M.obj) :
      rationalTarget.map (a ⊗ₜ[S] f) = a ⊗ₜ[S] FL.map f := by
    exact LinearMap.baseChange_tmul _ _ _
  let : GE.Additive :=
    ⟨fun {K M f g} ↦ (sfCompactSupportFiniteHomMap l K₀ hl c A K M).map_add f g⟩
  let : rationalTarget.Additive :=
    ⟨fun {K M f g} ↦ (sfCompactSupportFiniteHomMap l K₀ hl c B K M).map_add f g⟩
  let : SX.Additive := hSX.1
  let : SY.Additive := hSY.1
  have hoF (K : sfRationalConstructibleCategory l A X) :
      (GE ⋙ SY).obj K = ⟨(FE ⋙ TY).obj K.obj⟩ := by
    change SY.obj (GE.obj K) = _
    exact hSY.2.1 (GE.obj K)
  have hoG (K : sfRationalConstructibleCategory l A X) :
      (SX ⋙ rationalTarget).obj K = ⟨(TX ⋙ FL).obj K.obj⟩ := by
    change (⟨FL.obj (SX.obj K).obj⟩ : sfRationalConstructibleCategory l B Y) = _
    exact congrArg (fun z : sfRationalConstructibleCategory l B X ↦
      (⟨FL.obj z.obj⟩ : sfRationalConstructibleCategory l B Y)) (hSX.2.1 K)
  apply localizeIso p q (FE ⋙ TY) (TX ⋙ FL) (GE ⋙ SY) (SX ⋙ rationalTarget)
    ψ hoF hoG ?_ ?_ b
  · intro K M a f
    change HEq (SY.map (GE.map (a ⊗ₜ[R] f))) _
    rw [hGE]
    exact hSY.2.2 (FE.obj K.obj) (FE.obj M.obj) (FE.map f) a
  · intro K M a f
    change HEq (rationalTarget.map (SX.map (a ⊗ₜ[R] f))) _
    exact (map_heq rationalTarget (hSX.2.1 K) (hSX.2.1 M)
      (hSX.2.2 K.obj M.obj f a)).trans (heq_of_eq (hrationalTarget _ _ _ _))

/-- Raw localization of an integral compact-support scalar isomorphism is a rational
natural isomorphism with exactly the localized components.
Source: lem-fix-operation-reduction, final paragraph;
normalized scalar isomorphisms, proof step 6
(blueprint: lem-sf-compact-support-rational-scalar-iso).
Proof: localize each component and its inverse. Transport the endpoints by the
prescribed object equalities for rational scalar extension. Naturality on a pure
tensor is the integral naturality equation multiplied by the image of its scalar;
bilinearity moves this scalar across composition. Tensor induction gives naturality
on every arrow. Localization preserves identity and composition, so the localized
inverse components satisfy both inverse equations. The component prescription follows
from their construction, with endpoint transport expressed as heterogeneous equality. -/
theorem sfCompactSupportRationalScalarIso
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (b : sfCompactSupportFiniteIntegralFunctor l K₀ hl c (Coefficient.{u} l Ω E) ⋙
        integralTransition l Ω Y E L h ≅
      integralTransition l Ω X E L h ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c (Coefficient.{u} l Ω L)) :
    ∃ β : sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω E) ⋙
          transition l Ω Y E L h ≅
        transition l Ω X E L h ⋙
          sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω L),
        ∀ K : Stage l Ω X E, HEq (β.hom.app K)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
            (b.hom.app K.obj)) := by
  exact rationalScalarIsoOfFields l K₀ hl c
    (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) b

end WeilConjectures
