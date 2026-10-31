/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedCocycle
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedProperTransition
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedOpenTransition

/-! # Actual compact-support coefficient transitions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor HasDerivedCategory.standard
  SemilinearSections.reduction SpTowerShriek.Fcomparison
  Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian scalarExtensionFunctor
variable (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The specified b followed by finite compact support of the input reduction.
The b in this definition is literally the proper counit mate followed by the open
scalar comparison, as fixed by reductionDirectImageComparison.
Source: blueprint paragraph (1), the displayed composite
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def word {m n : ℕ} (h : m ≤ n) (C : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).obj
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C)) ⟶
      (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj C) :=
  letI := b.finite n
  letI := b.finite m
  (reductionDirectImageComparison (quotientMap l E h) c.i c.g).app
      ((SpTowerShriek.Ev l E X n).obj C) ≫
    (SpTowerShriek.finiteF l E b c m).map (rho l E b X h C)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The actual output reduction, conjugated by the canonical compact-support evaluations.
Source: blueprint paragraph (1); det-sp-tower-shriek-levels evaluation identifications
(blueprint: lem-sp-shriek-normalized-transition-comparison). -/
def actual {m n : ℕ} (h : m ≤ n) (C : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).obj
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C)) ⟶
      (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj C) :=
  conjugateReduction (scalarExtensionFunctor (quotientMap l E h) Y)
    ((SpTowerShriek.Fcomparison l E b o c n).app C)
    ((SpTowerShriek.Fcomparison l E b o c m).app C)
    (rho l E b Y h ((SpTowerShriek.F l E b o c).obj C))

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem transport_naturality
    {A B : Type*} [categoryA : Category A] [categoryB : Category B]
    {S S' : A ⥤ B} (s : S ≅ S') {K L : A} {M N : B}
    (v : K ⟶ L) (w : M ⟶ N) (a : S.obj K ⟶ M) (b : S.obj L ⟶ N)
    (h : S.map v ≫ b = a ≫ w) :
    S'.map v ≫ coordinateReduction s b = coordinateReduction s a ≫ w := by
  dsimp only [coordinateReduction]
  rw [← Category.assoc, s.inv.naturality, Category.assoc, h, Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compose_transition
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Jn : A ⥤ C) (Jm : B ⥤ D) (Pn : C ⥤ E) (Pm : D ⥤ F)
    (Sx : A ⥤ B) (Sz : C ⥤ D) (Sy : E ⥤ F)
    (gamma : Pn ⋙ Sy ⟶ Sz ⋙ Pm) (epsilon : Jn ⋙ Sz ⟶ Sx ⋙ Jm)
    {Kn : A} {Km : B} {Zn : C} {Zm : D} {Yn : E} {Ym : F}
    (pn : Yn ⟶ Pn.obj Zn) (pm : Ym ⟶ Pm.obj Zm)
    (jn : Zn ⟶ Jn.obj Kn) (jm : Zm ⟶ Jm.obj Km)
    (rx : Sx.obj Kn ⟶ Km) (rz : Sz.obj Zn ⟶ Zm) (ry : Sy.obj Yn ⟶ Ym)
    (hp : ry ≫ pm = Sy.map pn ≫ gamma.app Zn ≫ Pm.map rz)
    (ho : rz ≫ jm = Sz.map jn ≫ epsilon.app Kn ≫ Jm.map rx) :
    ry ≫ (pm ≫ Pm.map jm) =
      Sy.map (pn ≫ Pn.map jn) ≫
        (gamma.app (Jn.obj Kn) ≫ Pm.map (epsilon.app Kn)) ≫ Pm.map (Jm.map rx) := by
  calc
    _ = Sy.map pn ≫ gamma.app Zn ≫ Pm.map (rz ≫ jm) := by
      rw [← Category.assoc, hp]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [ho]
      simp only [Functor.map_comp, Category.assoc]
      have hn := gamma.naturality jn
      dsimp only [CategoryTheory.Functor.comp_map] at hn
      rw [reassoc_of% hn]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rho_naturality (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) {M N : SpTowerShriek.D l E T} (v : M ⟶ N) :
    (scalarExtensionFunctor (quotientMap l E h) T).map
        ((SpTowerShriek.Ev l E T n).map v) ≫ rho l E b T h N =
      rho l E b T h M ≫ (SpTowerShriek.Ev l E T m).map v := by
  have result := transport_naturality
    (A := proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (B := proEtaleDerivedCategory T (SpTowerShriek.R l E m))
    (categoryA := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryB := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (scalarCoordinates l E b T h) ((SpTowerShriek.Ev l E T n).map v)
    ((SpTowerShriek.Ev l E T m).map v)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) M)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) N)
    (SemilinearSections.reduction_naturality.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
      h ((b.calculus T).scalar h) v)
  exact result

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem actual_eq_word {m n : ℕ} (h : m ≤ n)
    (M : SpTowerShriek.D l E X) : actual l E b o c h M = word l E b c h M := by
  have hp := normalized_proper_transition l E b (o.geometry c.g) h
    ((SpTowerShriek.openD l E b (o.openOp c.i)).obj M)
  have ho := normalized_open_transition l E b (o.openOp c.i) h M
  have ht : rho l E b Y h ((SpTowerShriek.F l E b o c).obj M) ≫
      (SpTowerShriek.Fcomparison l E b o c m).hom.app M =
    (scalarExtensionFunctor (quotientMap l E h) Y).map
      ((SpTowerShriek.Fcomparison l E b o c n).hom.app M) ≫ word l E b c h M := by
    have ht0 := compose_transition
        (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) c.i)
        (sfIntrinsicDerivedOpen (SpTowerShriek.R l E m) c.i)
        (directImageConstantPush (SpTowerShriek.R l E n) c.g)
        (directImageConstantPush (SpTowerShriek.R l E m) c.g)
        (scalarExtensionFunctor (quotientMap l E h) X)
        (scalarExtensionFunctor (quotientMap l E h) c.Z)
        (scalarExtensionFunctor (quotientMap l E h) Y)
        (directImageScalarComparison (quotientMap l E h) c.g)
        (reductionOpenScalarIso (quotientMap l E h) c.i).hom
        (((o.geometry c.g).pushEvaluation n).hom.app
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj M))
        (((o.geometry c.g).pushEvaluation m).hom.app
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj M))
        ((SpTowerShriek.openEvaluation l E b (o.openOp c.i) n).hom.app M)
        ((SpTowerShriek.openEvaluation l E b (o.openOp c.i) m).hom.app M)
        (rho l E b X h M)
        (rho l E b c.Z h ((SpTowerShriek.openD l E b (o.openOp c.i)).obj M))
        (rho l E b Y h ((SpTowerShriek.F l E b o c).obj M)) hp ho
    simp only [SpTowerShriek.Fcomparison, SpTowerShriek.F, Functor.comp_obj,
      Iso.symm_hom, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, word, reductionDirectImageComparison,
      SpTowerShriek.finiteF, Category.assoc,
      scalarExtensionFunctor, scalarExtension, directImageScalarExtension,
      directImageConstantPush, proEtaleRingDerivedDirectImage,
      proEtaleConstantRingPushforward, sfIntrinsicDerivedOpen, SpTowerShriek.push] at ht0 ⊢
    simpa only [CategoryTheory.Functor.comp_map] using ht0
  dsimp only [actual, conjugateReduction]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [ht, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem conjugate_cocycle
    {A B C : Type*} [categoryA : Category A] [categoryB : Category B]
    [categoryC : Category C]
    (S : A ⥤ B) (T : B ⥤ C) (R : A ⥤ C) (a : S ⋙ T ≅ R)
    {K K' : A} {L L' : B} {M M' : C}
    (i : K ≅ K') (j : L ≅ L') (k : M ≅ M')
    (f : S.obj K ⟶ L) (g : T.obj L ⟶ M) (h : R.obj K ⟶ M)
    (w : T.map f ≫ g = a.hom.app K ≫ h) :
    T.map (conjugateReduction S i j f) ≫ conjugateReduction T j k g =
      a.hom.app K' ≫ conjugateReduction R i k h := by
  simp only [conjugateReduction, Functor.map_comp, Category.assoc]
  rw [← T.map_comp_assoc j.hom j.inv, j.hom_inv_id,
    T.map_id, Category.id_comp]
  rw [← Category.assoc (T.map f) g, w, Category.assoc]
  exact a.hom.naturality_assoc i.inv (h ≫ k.hom)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem conjugate_cocycle_values
    {A B C : Type*} [categoryA : Category A] [categoryB : Category B]
    [categoryC : Category C]
    (S : A ⥤ B) (T : B ⥤ C) (R : A ⥤ C) (a : S ⋙ T ≅ R)
    {K K' : A} {L L' : B} {M M' : C}
    (i : K ≅ K') (j : L ≅ L') (k : M ≅ M')
    (f : S.obj K ⟶ L) (g : T.obj L ⟶ M) (h : R.obj K ⟶ M)
    (f' : S.obj K' ⟶ L') (g' : T.obj L' ⟶ M') (h' : R.obj K' ⟶ M')
    (ef : f' = conjugateReduction S i j f)
    (eg : g' = conjugateReduction T j k g)
    (eh : h' = conjugateReduction R i k h)
    (w : T.map f ≫ g = a.hom.app K ≫ h) :
    T.map f' ≫ g' = a.hom.app K' ≫ h' := by
  rw [ef, eg, eh]
  exact conjugate_cocycle S T R a i j k f g h w

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem actual_cocycle {r m n : ℕ} (h : r ≤ m) (k : m ≤ n)
    (M : SpTowerShriek.D l E X) :
    (scalarExtensionFunctor (quotientMap l E h) Y).map (actual l E b o c k M) ≫
        actual l E b o c h M =
      (alpha l E b Y h k).hom.app
        ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj M)) ≫
        actual l E b o c (h.trans k) M := by
  exact conjugate_cocycle_values
    (A := proEtaleDerivedCategory Y (SpTowerShriek.R l E n))
    (B := proEtaleDerivedCategory Y (SpTowerShriek.R l E m))
    (C := proEtaleDerivedCategory Y (SpTowerShriek.R l E r))
    (categoryA := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryB := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryC := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (scalarExtensionFunctor (quotientMap l E k) Y)
    (scalarExtensionFunctor (quotientMap l E h) Y)
    (scalarExtensionFunctor (quotientMap l E (h.trans k)) Y)
    (alpha l E b Y h k)
    (K := (SpTowerShriek.Ev l E Y n).obj ((SpTowerShriek.F l E b o c).obj M))
    (L := (SpTowerShriek.Ev l E Y m).obj ((SpTowerShriek.F l E b o c).obj M))
    (M := (SpTowerShriek.Ev l E Y r).obj ((SpTowerShriek.F l E b o c).obj M))
    (K' := (SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj M))
    (L' := (SpTowerShriek.finiteF l E b c m).obj ((SpTowerShriek.Ev l E X m).obj M))
    (M' := (SpTowerShriek.finiteF l E b c r).obj ((SpTowerShriek.Ev l E X r).obj M))
    ((SpTowerShriek.Fcomparison l E b o c n).app M)
    ((SpTowerShriek.Fcomparison l E b o c m).app M)
    ((SpTowerShriek.Fcomparison l E b o c r).app M)
    (rho l E b Y k ((SpTowerShriek.F l E b o c).obj M))
    (rho l E b Y h ((SpTowerShriek.F l E b o c).obj M))
    (rho l E b Y (h.trans k) ((SpTowerShriek.F l E b o c).obj M))
    (actual l E b o c k M) (actual l E b o c h M) (actual l E b o c (h.trans k) M)
    rfl rfl rfl (rho_cocycle l E b Y h k ((SpTowerShriek.F l E b o c).obj M))

-- Preserve the original finite-level hypotheses in the public theorem's signature.
set_option linter.unusedVariables false in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The actual compact-support transition is precisely the specified coefficient word,
naturally in the bounded-below input, and its successive words satisfy the scalar cocycle.
Source: blueprint latest, sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraph (1) (blueprint: lem-sp-shriek-normalized-transition-comparison).

Proof:
1. Use def-sp-reduction-direct-image-comparison to write b as gamma followed by Rp_*(e).
   Gamma is the transpose of the scalar-extended proper counit, and e is the normalized
   comparison of the composite open/scalar left adjoints. These exist on ambient D.
2. Exact extension by zero and scalar restriction commute. The open scalar-adjoint is
   j_!(rho) after e: restrict to the open, use lem-sf-open-tensor-normalization to identify
   its unit and tensor map with the identity, and use full faithfulness to identify the
   maps. This is done on the strict derived system model, before level evaluation.
3. Apply lem-coef-semilinear-derived-sections to p and j_!C. Its actual direct-image
   transition is Rp_*(the open transition) after gamma, preserving the same counit.
   Substitute step 2 and use def-sp-tower-shriek-data's canonical Fcomparison to obtain
   actual = word. The scalarCoordinates comparisons merely change normalized adjunction
   coordinates; evaluations are never used as a faithfulness test.
4. Naturality of rho and of b gives the displayed naturality square for every input map.
5. Expand successive actual reductions and cancel the middle evaluation comparison.
   Apply the normalized scalar cocycle to the single output system F(C), and use
   naturality of alpha at the inverse nth evaluation comparison. Rewrite actual=word
   to obtain word coherence. Equal indices use the same calculation. No coefficient
   flatness or projective dimension is assumed, and input transitions need not be
   invertible. -/
theorem shriek_normalized_transition_comparison
    (pchar : ℕ) (hp : 0 < pchar) (hpl : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    (C : DerivedCategory.Plus (SpTowerShriek.S l E X))
    (hC : ∀ n : ℕ, SpTowerShriek.GoodLevel l E b X n C.obj) :
    (∀ {m n : ℕ} (h : m ≤ n), actual l E b o c h C.obj = word l E b c h C.obj) ∧
    (∀ (C' : DerivedCategory.Plus (SpTowerShriek.S l E X))
      (_hC' : ∀ n : ℕ, SpTowerShriek.GoodLevel l E b X n C'.obj)
      (v : C.obj ⟶ C'.obj) {m n : ℕ} (h : m ≤ n),
      (scalarExtensionFunctor (quotientMap l E h) Y).map
          ((SpTowerShriek.finiteF l E b c n).map ((SpTowerShriek.Ev l E X n).map v)) ≫
          word l E b c h C'.obj =
        word l E b c h C.obj ≫
          (SpTowerShriek.finiteF l E b c m).map ((SpTowerShriek.Ev l E X m).map v)) ∧
    (∀ {r m n : ℕ} (h : r ≤ m) (k : m ≤ n),
      (scalarExtensionFunctor (quotientMap l E h) Y).map (word l E b c k C.obj) ≫
          word l E b c h C.obj =
        (alpha l E b Y h k).hom.app
            ((SpTowerShriek.finiteF l E b c n).obj ((SpTowerShriek.Ev l E X n).obj C.obj)) ≫
          word l E b c (h.trans k) C.obj) := by
  constructor
  · intro m n h
    exact actual_eq_word l E b o c h C.obj
  constructor
  · intro C' hC' v m n h
    let := b.finite n
    let := b.finite m
    dsimp only [word]
    have hn := (reductionDirectImageComparison (quotientMap l E h) c.i c.g).naturality
      ((SpTowerShriek.Ev l E X n).map v)
    dsimp only [CategoryTheory.Functor.comp_map] at hn
    rw [← Category.assoc]
    erw [hn]
    simpa only [Functor.map_comp, Category.assoc, SpTowerShriek.finiteF,
      CategoryTheory.Functor.comp_map] using
      congrArg (fun a ↦ (reductionDirectImageComparison (quotientMap l E h) c.i c.g).app
        ((SpTowerShriek.Ev l E X n).obj C.obj) ≫
        (SpTowerShriek.finiteF l E b c m).map a) (rho_naturality l E b X h v)
  · intro r m n h k
    simpa only [actual_eq_word] using actual_cocycle l E b o c h k C.obj

end AlgebraicGeometry.ProEtale.SpShriekTransition
