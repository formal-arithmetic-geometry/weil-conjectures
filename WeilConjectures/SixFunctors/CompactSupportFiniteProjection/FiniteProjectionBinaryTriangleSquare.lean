/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompositionRealization
import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionMate
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionBinaryIterationTrianglePasting

/-! # Fixed-triangle binary square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver

private theorem paste_realized_square
    {A : Type*} [Category A] {a b c d a' b' d' : A}
    (e : a ⟶ b) (p : b ⟶ d) (q : a ⟶ c) (t : c ⟶ d)
    (sa : a ≅ a') (sb : b ≅ b') (td : d ≅ d') (tc : c ≅ d')
    (r : b' ⟶ a') (v : a' ⟶ d') (w : b' ⟶ d')
    (hs : e ≫ sb.hom ≫ r = sa.hom)
    (hp : p ≫ td.hom = sb.hom ≫ w)
    (ht : t ≫ td.hom = tc.hom)
    (hq : q ≫ tc.hom = sa.hom ≫ v)
    (hw : w = r ≫ v) : e ≫ p = q ≫ t := by
  apply (cancel_mono td.hom).1
  simp only [Category.assoc]
  rw [hp, ht, hq, hw]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ v) hs

attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem faithful_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Faithful]
    {a b c d : A} (e : a ⟶ b) (p : b ⟶ d) (q : a ⟶ c) (t : c ⟶ d)
    (h : F.map e ≫ F.map p = F.map q ≫ F.map t) : e ≫ p = q ≫ t := by
  apply F.map_injective
  simpa only [Functor.map_comp] using h

private theorem faithful_paste_realized_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Faithful]
    {a b c d : A} {a' b' d' : B}
    (e : a ⟶ b) (p : b ⟶ d) (q : a ⟶ c) (t : c ⟶ d)
    (sa : F.obj a ≅ a') (sb : F.obj b ≅ b')
    (td : F.obj d ≅ d') (tc : F.obj c ≅ d')
    (r : b' ⟶ a') (v : a' ⟶ d') (w : b' ⟶ d')
    (hs : F.map e ≫ sb.hom ≫ r = sa.hom)
    (hp : F.map p ≫ td.hom = sb.hom ≫ w)
    (ht : F.map t ≫ td.hom = tc.hom)
    (hq : F.map q ≫ tc.hom = sa.hom ≫ v)
    (hw : w = r ≫ v) : e ≫ p = q ≫ t := by
  exact faithful_square F e p q t
    (paste_realized_square _ _ _ _ sa sb td tc r v w hs hp ht hq hw)

attribute [local irreducible] TriangleLaws

private theorem positive_elim
    (P : ∀ (n : ℕ), 1 ≤ n → Prop)
    (h : ∀ (m : ℕ) (hm : 1 ≤ m + 1), P (m + 1) hm)
    {n : ℕ} (hn : 1 ≤ n) : P n hn := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact h m hn

private theorem triangle_laws_transport
    {G : Type*} [Category G] {geo : G ⥤ Scheme.{u}} (c : Calculus G geo)
    {t t' : TensorData c} (h : t = t') (ht : TriangleLaws c t') :
    TriangleLaws c t := by
  cases h
  exact @ht

private theorem coefficient_triangle_laws
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n} :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    TriangleLaws (ordinary D
      (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      (fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)) := by
  exact positive_elim (n := n)
    (fun k hk ↦
      letI := Padic.finite_coefficientExtensionRing C.l E k hk
      TriangleLaws (ordinary D
        (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E k)))
        (fixedScalarTensorData (D := D) (C := C) (E := E) (n := k) (hn := hk)))
    (fun m hm ↦ by
      let := Padic.finite_coefficientExtensionRing C.l E (m + 1) hm
      exact triangle_laws_transport
        (ordinary D (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))
        (fixedScalarTensorData_eq (D := D) (C := C) (E := E) (n := m + 1) (hn := hm))
        @(compositionProjectionMate D C.l C.different E m).1) hn

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  realization fixedComponent fixedTensor

private theorem conjugate_realization
    {A : Type*} [Category A] {P : ObjectProperty A}
    {K L : P.FullSubcategory} {U V : A} (e : K.obj ≅ U) (d : L.obj ≅ V)
    (a : U ⟶ V) :
    P.ι.map (projectionFullConjugate e d a) ≫ d.hom = e.hom ≫ a := by
  change (e.hom ≫ a ≫ d.inv) ≫ d.hom = e.hom ≫ a
  simp only [Category.assoc, d.inv_hom_id, Category.comp_id]

def binarySquareEquation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) : Prop :=
  ((partialTensor S Z).map
    ((S.finite.composition (X := X) (Y := Y) (Z := Z) f g cf cg cfg).hom.app K)).app L ≫
      component S (X := Y) (Y := Z) g cg ((S.finite.support (X := X) (Y := Y) f cf).obj K) L ≫
      (S.finite.support (X := Y) (Y := Z) g cg).map
        (component S (X := X) (Y := Y) f cf K ((torPull S (X := Y) (Y := Z) g).obj L)) =
    component S (X := X) (Y := Z) (f ≫ g) cfg K L ≫
      (S.finite.composition (X := X) (Y := Y) (Z := Z) f g cf cg cfg).hom.app
        (((partialTensor S X).obj K).obj ((torPull S (X := X) (Y := Z) (f ≫ g)).obj L)) ≫
      (S.finite.support (X := Y) (Y := Z) g cg).map ((S.finite.support (X := X) (Y := Y) f cf).map
        (((partialTensor S X).obj K).map
          (torPullComposition S (X := X) (Y := Y) (Z := Z) f g L).hom))

private theorem realized_target_refl
    {A B C₀ : Type*} [Category A] [Category B] [Category C₀]
    (R : A ⥤ B) (H : C₀ ⥤ A) (T : C₀ ⥤ C₀)
    {x : C₀} {a : B} (tc : a ≅ R.obj (H.obj (T.obj x))) :
    (realizedPullTargetIso R H T (Iso.refl x) tc).hom = tc.hom := by
  change tc.hom ≫ R.map (H.map (T.map (𝟙 x))) = tc.hom
  rw [T.map_id x, H.map_id (T.obj x), R.map_id (H.obj (T.obj x)), Category.comp_id]

section TotalFactorPasting

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  [Finite (Padic.coefficientExtensionRing C.l E n)]

local notation "c₀" => ordinary D (ULift (Padic.coefficientExtensionRing C.l E n))
local notation "t₀" =>
  fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)

private abbrev FixedDerived (X : SixFunctorSpace D) :=
  DerivedCategory (Sheaf (ProEt.topology X.obj.left)
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))

/-- Eliminate the factorization index before evaluating the realization. -/
private theorem scalar_factor_realization
    {X V Y : SixFunctorSpace D} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion ((geometry D).map j)] [IsProper ((geometry D).map q)]
    (f : X ⟶ Y) (hf : f = j ≫ q)
    (k : FixedDerived (C := C) (E := E) (n := n) X)
    (l : FixedDerived (C := C) (E := E) (n := n) Y)
    {N : Type v} [Category N]
    (R : FixedDerived (C := C) (E := E) (n := n) Y ⥤ N)
    {a b : N} (p : a ⟶ b)
    (sc : a ⟶ R.obj (((t₀).tensor Y).obj (((compact c₀ j q).obj k), l)))
    (tc : b ≅ R.obj ((compact c₀ j q).obj
      (((t₀).tensor X).obj (k, (((c₀).P f).obj l)))))
    (h : p ≫ tc.hom = sc ≫ R.map
      (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) f
        (sixFunctorFactorCompactification j q
          ‹IsOpenImmersion ((geometry D).map j)› ‹IsProper ((geometry D).map q)› f hf) k l)) :
    p ≫ (realizedPullTargetIso R (compact c₀ j q)
      ((fixedTensor (C := C) (E := E) (n := n) X).obj k)
      (((c₀).pCongr hf).app l) tc).hom =
      sc ≫ R.map (projection c₀ t₀ j q k l) := by
  cases hf
  have ht := realized_target_refl R (compact c₀ j q)
    ((fixedTensor (C := C) (E := E) (n := n) X).obj k) tc
  have hq := fixed_factor_projection_refl (D := D) (C := C) (E := E) (n := n)
    (hn := hn) j q k l
  exact (congrArg (fun z ↦ p ≫ z) ht).trans
    (h.trans (congrArg (fun z ↦ sc ≫ R.map z) hq))

/-- The same factor calculation for morphism-indexed pullback transport. -/
private theorem scalar_factor_realization_morphism
    {X V Y : SixFunctorSpace D} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion ((geometry D).map j)] [IsProper ((geometry D).map q)]
    (f : X ⟶ Y) (hf : f = j ≫ q)
    (k : FixedDerived (C := C) (E := E) (n := n) X)
    (l : FixedDerived (C := C) (E := E) (n := n) Y)
    {N : Type v} [Category N]
    (R : FixedDerived (C := C) (E := E) (n := n) Y ⥤ N)
    {a b : N} (p : a ⟶ b)
    (sc : a ⟶ R.obj (((t₀).tensor Y).obj (((compact c₀ j q).obj k), l)))
    (tc : b ≅ R.obj ((compact c₀ j q).obj
      (((t₀).tensor X).obj (k, (((c₀).P f).obj l)))))
    (h : p ≫ tc.hom = sc ≫ R.map
      (fixedComponent (D := D) (C := C) (E := E) (n := n) (hn := hn) f
        (sixFunctorFactorCompactification j q
          ‹IsOpenImmersion ((geometry D).map j)› ‹IsProper ((geometry D).map q)› f hf) k l)) :
    p ≫ (realizedPullTargetIso R (compact c₀ j q)
      ((fixedTensor (C := C) (E := E) (n := n) X).obj k)
      ((morphismPullbackCongr c₀ hf).app l) tc).hom =
      sc ≫ R.map (projection c₀ t₀ j q k l) := by
  cases hf
  exact scalar_factor_realization (hn := hn) j q (j ≫ q) rfl k l R p sc tc h

end TotalFactorPasting

private theorem total_component_realization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X V W Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
    [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)]
    (hb : b ≫ p = q ≫ i)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let c := ordinary D A
    let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
    let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    let f := j ≫ q
    let g := i ≫ s
    let cfg := binaryTotal j b q p i s hb
    I.map (component S (f ≫ g) cfg K L) ≫
        (binaryTargetComparison S j b q p i s hb K L).hom =
      (sourceComparison S (f ≫ g) cfg K L).hom ≫
        RZ.functor.map (projection c t (j ≫ b) (p ≫ s)
          (RX.inverse.obj K.obj) (RZ.inverse.obj L.obj)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let c := ordinary D A
  let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
  let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let f := j ≫ q
  let g := i ≫ s
  let cfg := binaryTotal j b q p i s hb
  let k := RX.inverse.obj K.obj
  let l := RZ.inverse.obj L.obj
  let sa := sourceComparison S (f ≫ g) cfg K L
  have hq₀ := conjugate_realization
    (P := intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left)
    (K := ((partialTensor S Z).obj ((S.finite.support (f ≫ g) cfg).obj K)).obj L)
    (L := (S.finite.support (f ≫ g) cfg).obj
      (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)))
    (sourceComparison S (f ≫ g) cfg K L)
    (targetComparison S (f ≫ g) cfg K L)
    (RZ.functor.map
      (fixedComponent (C := C) (E := E) (n := n) (hn := hn) (f ≫ g) cfg k l))
  exact scalar_factor_realization_morphism (hn := hn) (j ≫ b) (p ≫ s) (f ≫ g)
    (by
      change (j ≫ q) ≫ (i ≫ s) = (j ≫ b) ≫ (p ≫ s)
      simp only [Category.assoc]
      rw [← Category.assoc q i s, ← hb]
      simp only [Category.assoc]) k l RZ.functor
    (I.map (component S (f ≫ g) cfg K L)) sa.hom
    (targetComparison S (f ≫ g) cfg K L) hq₀

/-- The binary equation holds on a supplied compatible Cartesian triangle.
Source: the fixed-triangle step of fix-prop-projection-formula.proof.md;
coefficient projection formula, raw triangle law and endpoint pasting
(blueprint: lem-sf-finite-projection-binary-triangle-square).

Proof: use the proved projection-free triangle pasting, the raw factor projection
identities and the faithful constructible inclusion. The statement is strictly below
the existential theorem because all six triangle maps and the pullback square are
supplied. Zero objects, identity maps and empty schemes use the same equations. -/
theorem binary_square_on_triangle
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X V W Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
    [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    binarySquareEquation S (X := X) (Y := Y) (Z := Z) (j ≫ q) (i ≫ s)
      (binaryFirst j q) (binarySecond i s)
      (binaryTotal j b q p i s hb) K L := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
  let c := ordinary D A
  let t := fixedScalarTensorData (D := D) (C := C) (E := E) (n := n) (hn := hn)
  let RX := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) X
  let RZ := realization (D := D) (C := C) (E := E) (n := n) (hn := hn) Z
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let f := j ≫ q
  let g := i ≫ s
  let cf := binaryFirst j q
  let cg := binarySecond i s
  let cfg := binaryTotal j b q p i s hb
  let k := RX.inverse.obj K.obj
  let l := RZ.inverse.obj L.obj
  have ht := coefficient_triangle_laws (D := D) (C := C) (E := E) (n := n) (hn := hn)
  unfold TriangleLaws at ht
  obtain ⟨ha, he, _⟩ := ht j b q p i s hb
  have hc := binary_composition_realization S j b q p i s hb sq K L ha
  have hp := binary_iteration_triangle_pasting S j b q p i s hb K L ha
  let sa := sourceComparison S (f ≫ g) cfg K L
  let sb := iterationSourceComparison S f g cf cg K L
  let td := binaryIterationTargetComparison S j b q p i s hb K L ha
  let tc := binaryTargetComparison S j b q p i s hb K L
  let r := RZ.functor.map ((t.tensor Z).map
    (Prod.mkHom ((alpha c j b q p i s hb).app k) (𝟙 l)))
  let v := RZ.functor.map (projection c t (j ≫ b) (p ≫ s) k l)
  let w := RZ.functor.map (leftMap c t j b q p i s hb k l)
  have hw : w = r ≫ v := by
    exact (congrArg RZ.functor.map (he k l)).trans (RZ.functor.map_comp _ _)
  have hq := total_component_realization S j b q p i s hb K L
  unfold binarySquareEquation
  exact faithful_paste_realized_square I _ _ _ _ sa sb td tc r v w
    hc.source hp hc.target hq hw

end WeilConjectures.CompactSupportFiniteProjection
