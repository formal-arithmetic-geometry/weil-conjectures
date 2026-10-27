/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.SemilinearDerivedCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Mates and tensor-Hom transposes on ordinary derived coefficient systems

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
prop-coef-integral-exceptional-adjoint.proof.md, final paragraph, ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence).

The Boolean selector is false for etale and true for proetale. Index n denotes exponent n+1.
All operations belong to the recorded ordinary derived category of strict systems on the
ringed sequence site. The assertions are made before any inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u c v r k d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.TwoSquare

namespace WeilConjectures

/-- The existing small site category, with its two independent site universes.
Source: blueprint final ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def adjunctionSystemSiteCategory (W : Scheme.{t}) : Bool → Type (t + 1)
  | false => W.Etale
  | true => W.ProEt

/-- The category structure of the selected existing site.
Source: blueprint final ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
instance adjunctionSystemSiteCategoryCategory (W : Scheme.{t}) (proet : Bool) :
    Category.{t} (adjunctionSystemSiteCategory W proet) :=
  match proet with
  | false => inferInstanceAs (Category W.Etale)
  | true => inferInstanceAs (Category W.ProEt)

/-- The selected existing topology, without a new definition of covers.
Source: blueprint final ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def adjunctionSystemSite (W : Scheme.{t}) (proet : Bool) :
    GrothendieckTopology (adjunctionSystemSiteCategory W proet) :=
  match proet with
  | false => W.smallEtaleTopology
  | true => Scheme.ProEt.topology W

/-- The selected site fits in the coefficient universe.
Source: blueprint size convention in the final ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
instance adjunctionSystemSiteSmall (W : Scheme.{t}) (proet : Bool) :
    EssentiallySmall.{max u (t + 1)} (adjunctionSystemSiteCategory W proet) :=
  essentiallySmallSelf _

/-- Ring sheafification transported through a small model of the selected site.
Source: blueprint size convention in the final ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
instance adjunctionSystemSiteSheafify (W : Scheme.{t}) (proet : Bool) :
    HasSheafify (adjunctionSystemSite W proet) CommRingCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (adjunctionSystemSiteCategory W proet) :=
    essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual constant finite coefficient sheaves at positive exponents.
Source: blueprint final ordinary-system refinement; coefficient-extension definition
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def adjunctionSystemRings (W : Scheme.{t}) (proet : Bool) (n : ℕ) :
    Sheaf (adjunctionSystemSite W proet) CommRingCat.{max u (t + 1)} :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The quotient-induced coefficient transitions, used as semilinear transitions.
Source: blueprint final ordinary-system refinement; coefficient-extension definition
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def adjunctionSystemRingTransition (W : Scheme.{t}) (proet : Bool) (n : ℕ) :
    adjunctionSystemRings l E W proet (n + 1) ⟶ adjunctionSystemRings l E W proet n :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).map
    (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift)

/-- The existing ordinary unbounded derived category on the ringed sequence site.
Source: blueprint final ordinary-system refinement; Zheng Construction 4.1
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
abbrev adjunctionSystemDerived (W : Scheme.{t}) (proet : Bool) :=
  SemilinearSections.DS.{t + 1, t, max u (t + 1)} (adjunctionSystemSite W proet)
    (adjunctionSystemRings l E W proet) (adjunctionSystemRingTransition l E W proet)

/-- The recorded closed tensor, scalar-adjunction and evaluation calculus on this site.
Source: blueprint final ordinary-system refinement; Zheng Construction 4.1 and Lemma 4.10
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
abbrev adjunctionSystemData (W : Scheme.{t}) (proet : Bool) :=
  SemilinearSections.Data.{t + 1, t, u} (adjunctionSystemSite W proet)
    (adjunctionSystemRings l E W proet) (adjunctionSystemRingTransition l E W proet)

section CategoricalFormulas
variable {X Y Z U V W x y : Type k}
  [Category.{k} X] [Category.{k} Y] [Category.{k} Z]
  [Category.{k} U] [Category.{k} V] [Category.{k} W]
  [Category.{k} x] [Category.{k} y]

/-- Mate evaluation, inverse identities, composition, and counit-compatible uniqueness.
These are formulas for actual adjunctions, to be used on full system subcategories below.
Source: blueprint final ordinary-system refinement; Mathlib Adjunction.Mates and Unique
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def SystemMateCoherence (E₀ : X ⥤ x) (E₁ : Y ⥤ y) : Prop :=
  ∀ (L L' : X ⥤ Y) (R R' : Y ⥤ X) (a : L ⊣ R) (a' : L' ⊣ R')
    (l₀ l₁ : x ⥤ y) (r₀ r₁ : y ⥤ x) (b : l₀ ⊣ r₀) (b' : l₁ ⊣ r₁)
    (A : SemilinearSections.AdjunctionEvaluation E₀ E₁ a b)
    (A' : SemilinearSections.AdjunctionEvaluation E₀ E₁ a' b')
    (α : L ⟶ L') (αn : l₀ ⟶ l₁),
    (∀ M : X, E₁.map (α.app M) ≫ A'.left.hom.app M =
      A.left.hom.app M ≫ αn.app (E₀.obj M)) →
    (∀ N : Y,
      E₀.map ((conjugateEquiv a' a α).app N) ≫ A.right.hom.app N =
        A'.right.hom.app N ≫
          (conjugateEquiv b' b αn).app (E₁.obj N)) ∧
    ((conjugateEquiv a' a).symm (conjugateEquiv a' a α) = α) ∧
    (∀ β : R' ⟶ R, conjugateEquiv a' a ((conjugateEquiv a' a).symm β) = β) ∧
    (∀ (L'' : X ⥤ Y) (R'' : Y ⥤ X) (a'' : L'' ⊣ R'') (β : L' ⟶ L''),
      conjugateEquiv a'' a (α ≫ β) =
        conjugateEquiv a'' a' β ≫ conjugateEquiv a' a α) ∧
    (∀ (J J' : Y ⥤ X) (j : L ⊣ J) (j' : L' ⊣ J'),
      conjugateEquiv a' a α ≫ (a.rightAdjointUniq j).hom =
        (a'.rightAdjointUniq j').hom ≫ conjugateEquiv j' j α)

/-- Both ordinary mate-pasting equations, including composite adjunctions.
Source: blueprint final ordinary-system refinement; Stacks 0E46, 0E47
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def SystemMatePasting : Prop :=
  (∀ (L₁ : X ⥤ Y) (R₁ : Y ⥤ X) (L₂ : Z ⥤ U) (R₂ : U ⥤ Z)
    (L₃ : V ⥤ W) (R₃ : W ⥤ V) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (G₁ : X ⥤ Z) (G₂ : Z ⥤ V) (H₁ : Y ⥤ U) (H₂ : U ⥤ W)
    (α : TwoSquare G₁ L₁ L₂ H₁) (β : TwoSquare G₂ L₂ L₃ H₂),
    mateEquiv a₁ a₃ (α ≫ₕ β) = mateEquiv a₁ a₂ α ≫ᵥ mateEquiv a₂ a₃ β) ∧
  (∀ (L₁ : X ⥤ Y) (R₁ : Y ⥤ X) (L₂ : U ⥤ V) (R₂ : V ⥤ U)
    (L₃ : Y ⥤ Z) (R₃ : Z ⥤ Y) (L₄ : V ⥤ W) (R₄ : W ⥤ V)
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (G : X ⥤ U) (H : Y ⥤ V) (K : Z ⥤ W)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K),
    mateEquiv (a₁.comp a₃) (a₂.comp a₄) (α ≫ᵥ β) =
      mateEquiv a₃ a₄ β ≫ₕ mateEquiv a₁ a₂ α)

end CategoricalFormulas

namespace SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- The explicit tensor, transpose and transition coherence assertion for this ringed system.
Source: blueprint final ordinary-system refinement; Stacks 06YS, 07A4 and 08J9
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def SystemTensorTransposeCoherence (A : Data.{c, v, r} J B τ) : Prop :=
  (∀ (K L M : DS.{c, v, max c v r} J B τ)
    (hL : Normalized.{c, v, max c v r} J B τ A.scalar L)
    (h : A.closed.tensor.obj (K, L) ⟶ M) (n : ℕ),
    (e.{c, v, max c v r} J B τ n).map (A.closed.transpose K L M h) ≫
        (A.homEvaluation L hL n).hom.app M =
      (A.levelClosed n).transpose _ _ _
        ((A.tensorEvaluation n).inv.app (K, L) ≫ (e.{c, v, max c v r} J B τ n).map h)) ∧
  (∀ (K L M : DS.{c, v, max c v r} J B τ),
    (∀ h : A.closed.tensor.obj (K, L) ⟶ M,
      (A.closed.transpose K L M).symm (A.closed.transpose K L M h) = h) ∧
    (∀ h : K ⟶ (internalHom.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ)).obj (op L, M),
      A.closed.transpose K L M ((A.closed.transpose K L M).symm h) = h)) ∧
  (∀ (K L : DS.{c, v, max c v r} J B τ) (f : K ⟶ L) (m n : ℕ) (h : n ≤ m),
    (A.scalar h).T.map ((e.{c, v, max c v r} J B τ m).map f) ≫ reduction J B τ h (A.scalar h) L =
      reduction J B τ h (A.scalar h) K ≫ (e.{c, v, max c v r} J B τ n).map f) ∧
  (∀ (P Q P' Q' : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients Q')
    (_flatP : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P)
    (_flatQ : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) Q)
    (_flatP' : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) P')
    (_flatQ' : flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) Q')
    (f : P ⟶ P') (g : Q ⟶ Q'),
    DerivedCategory.Q.map ((totalTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).map (f, g)) ≫
        (tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)
          A.closed A.tensorModels P' Q' hP' hQ').hom =
      (tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)
          A.closed A.tensorModels P Q hP hQ).hom ≫
        A.closed.tensor.map (DerivedCategory.Q.map f, DerivedCategory.Q.map g)) ∧
  (∀ (K K' L L' M : DS.{c, v, max c v r} J B τ) (f : K ⟶ K') (g : L' ⟶ L)
    (h : A.closed.tensor.obj (K, L) ⟶ M) (h' : A.closed.tensor.obj (K', L') ⟶ M),
    A.closed.tensor.map (X := (K, L')) (Y := (K', L')) (f, 𝟙 L') ≫ h' =
      A.closed.tensor.map (X := (K, L')) (Y := (K, L)) (𝟙 K, g) ≫ h →
      f ≫ A.closed.transpose K' L' M h' =
        A.closed.transpose K L M h ≫
          (internalHom.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, max c v r} J B τ)).map
            (g.op, 𝟙 M))

end SemilinearSections

/-- Finite mate evaluation for actual adjunctions between arbitrary full subcategories
of the two specified ordinary system categories. The finite comparison data include units
and counits, and an evaluated transformation is required to be the given system transformation.
Source: blueprint final ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def SystemAdjunctionCoherenceAt (X Y : Scheme.{t}) (sx sy : Bool) : Prop :=
  ∀ (P : ObjectProperty (adjunctionSystemDerived l E X sx))
    (Q : ObjectProperty (adjunctionSystemDerived l E Y sy)) (n : ℕ),
    SystemMateCoherence
      (P.ι ⋙ SemilinearSections.e (adjunctionSystemSite X sx)
        (adjunctionSystemRings l E X sx) (adjunctionSystemRingTransition l E X sx) n)
      (Q.ι ⋙ SemilinearSections.e (adjunctionSystemSite Y sy)
        (adjunctionSystemRings l E Y sy) (adjunctionSystemRingTransition l E Y sy) n)

/-- Both mate-pasting identities on any six full subcategories of the indicated actual
ordinary derived-system categories, with the actual composite adjunctions.
Source: blueprint final ordinary-system refinement; Stacks 0E46 and 0E47
(blueprint: lem-coef-system-adjunction-transpose-coherence). -/
def SystemAdjunctionPastingAt (W : Fin 6 → Scheme.{t}) (s : Fin 6 → Bool) : Prop :=
  ∀ P : ∀ i : Fin 6, ObjectProperty (adjunctionSystemDerived l E (W i) (s i)),
    SystemMatePasting (X := (P 0).FullSubcategory) (Y := (P 1).FullSubcategory)
      (Z := (P 2).FullSubcategory) (U := (P 3).FullSubcategory)
      (V := (P 4).FullSubcategory) (W := (P 5).FullSubcategory)

section CoherenceProofs

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors

private theorem uncurry_formula
    {D : Type d} [Category.{k} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L M : D) (u : K ⟶ H.obj (op L, M)) :
    (S.transpose K L M).symm u =
      S.tensor.map (Prod.mkHom u (𝟙 L)) ≫ S.evaluation L M := by
  let := S.monoidal
  simp only [CoefficientClosedStructure.transpose,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id]
  rfl

private theorem tensor_right_map
    {D : Type d} [Category.{k} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {K K' : D} (f : K ⟶ K') (L : D) :
    (@MonoidalCategory.tensorRight D _ S.monoidal L).map f =
      S.tensor.map (Prod.mkHom f (𝟙 L)) := by
  let := S.monoidal
  exact (MonoidalCategory.tensorHom_id f L).symm

private theorem tensor_left_map
    {D : Type d} [Category.{k} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K : D) {L L' : D} (f : L ⟶ L') :
    (@MonoidalCategory.tensorLeft D _ S.monoidal K).map f =
      S.tensor.map (Prod.mkHom (𝟙 K) f) := by
  let := S.monoidal
  exact (MonoidalCategory.id_tensorHom K f).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem transpose_naturality
    {D : Type d} [Category.{k} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K K' L L' M : D)
    (f : K ⟶ K') (g : L' ⟶ L)
    (h : S.tensor.obj (K, L) ⟶ M) (h' : S.tensor.obj (K', L') ⟶ M)
    (hh : S.tensor.map (Prod.mkHom f (𝟙 L')) ≫ h' =
      S.tensor.map (Prod.mkHom (𝟙 K) g) ≫ h) :
    f ≫ S.transpose K' L' M h' = S.transpose K L M h ≫ H.map (Prod.mkHom g.op (𝟙 M)) := by
  apply (S.transpose K L' M).symm.injective
  change ((S.adjunction L').homEquiv _ _).symm
      (f ≫ (S.adjunction L').homEquiv _ _ h') = _
  erw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  erw [tensor_right_map, uncurry_formula]
  erw [hh]
  have hm : S.tensor.map
      (Prod.mkHom (S.transpose K L M h ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) =
      S.tensor.map (Prod.mkHom (S.transpose K L M h) (𝟙 L')) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) := by
    erw [← S.tensor.map_comp]
    simp
  erw [hm, Category.assoc]
  erw [← tensor_right_map S (H.map (Prod.mkHom g.op (𝟙 M))) L']
  change _ = S.tensor.map (Prod.mkHom (S.transpose K L M h) (𝟙 L')) ≫
    ((@MonoidalCategory.tensorRight D _ S.monoidal L').map
      (H.map (Prod.mkHom g.op (𝟙 M))) ≫ (S.adjunction L').counit.app M)
  erw [S.evaluation_naturality L L' M g, tensor_left_map]
  have hi : S.tensor.map (Prod.mkHom (S.transpose K L M h) (𝟙 L')) ≫
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op L, M))) g) =
      S.tensor.map (Prod.mkHom (𝟙 K) g) ≫
        S.tensor.map (Prod.mkHom (S.transpose K L M h) (𝟙 L)) := by
    simp only [← S.tensor.map_comp]
    congr 1
    ext <;> simp
  change _ = S.tensor.map (Prod.mkHom (S.transpose K L M h) (𝟙 L')) ≫
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op L, M))) g) ≫ S.evaluation L M
  erw [← Category.assoc, hi, Category.assoc]
  congr 1
  erw [← uncurry_formula, Equiv.symm_apply_apply]

namespace SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem tensorModelIso_naturality (R : Sheaf J CommRingCat.{max c v r})
    (A : Closed.{c, v, r} J R) (T : Models.{c, v, r} J R A)
    (P P' Q Q' : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P')
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((totalTensor.{c, v, r} J R).map (Prod.mkHom f g)) ≫
      (tensorModelIso.{c, v, r} J R A T P' Q' hP' hQ').hom =
    (tensorModelIso.{c, v, r} J R A T P Q hP hQ).hom ≫
      A.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  let ρ : ObjectProperty (CochainComplex (Mod.{c, v, max c v r} J R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
  let f' : (⟨P, hP⟩ : ρ.FullSubcategory) ⟶ ⟨P', hP'⟩ := ObjectProperty.homMk f
  let g' : (⟨Q, hQ⟩ : ρ.FullSubcategory) ⟶ ⟨Q', hQ'⟩ := ObjectProperty.homMk g
  exact T.comparison.hom.naturality (Prod.mkHom f' g')

end SemilinearSections

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem tensor_transpose_coherence
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (A : SemilinearSections.Data.{c, v, r} J B τ) :
    SemilinearSections.SystemTensorTransposeCoherence.{c, v, r} J B τ A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K L M hL h n
    let e := SemilinearSections.e.{c, v, max c v r} J B τ n
    let T := (A.levelClosed n).tensor
    let u := A.closed.transpose K L M h
    apply ((A.levelClosed n).transpose (e.obj K) (e.obj L) (e.obj M)).symm.injective
    erw [Equiv.symm_apply_apply, uncurry_formula]
    change T.map (Prod.mkHom (e.map u ≫ (A.homEvaluation L hL n).hom.app M)
        (𝟙 (e.obj L))) ≫ (A.levelClosed n).evaluation (e.obj L) (e.obj M) = _
    have hf :
        T.map (Prod.mkHom (e.map u ≫ (A.homEvaluation L hL n).hom.app M)
          (𝟙 (e.obj L))) =
        T.map (Prod.mkHom (e.map u) (𝟙 (e.obj L))) ≫
          T.map (Prod.mkHom ((A.homEvaluation L hL n).hom.app M) (𝟙 (e.obj L))) := by
      erw [← T.map_comp]
      simp
    erw [hf, Category.assoc, A.homEvaluation_evaluation L M hL n]
    have hn := (A.tensorEvaluation n).inv.naturality (Prod.mkHom u (𝟙 L))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [CategoryTheory.Functor.map_id] at hn
    erw [← Category.assoc, hn, Category.assoc, ← e.map_comp]
    congr 1
    erw [← uncurry_formula, Equiv.symm_apply_apply]
  · intro K L M
    exact ⟨(A.closed.transpose K L M).symm_apply_apply,
      (A.closed.transpose K L M).apply_symm_apply⟩
  · intro K L f m n h
    apply ((A.scalar h).adjunction.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [SemilinearSections.reduction, Equiv.apply_symm_apply]
    exact (SemilinearSections.derivedTransition.{c, v, max c v r} _ _ _ h).naturality f
  · intro P Q P' Q' hP hQ hP' hQ' _ _ _ _ f g
    exact SemilinearSections.tensorModelIso_naturality.{c, v, r}
      (coefficientSequenceTopology J) (SemilinearSections.systemRing J B τ)
      A.closed A.tensorModels P P' Q Q' hP hP' hQ hQ' f g
  · intro K K' L L' M f g h h' hh
    exact transpose_naturality A.closed K K' L L' M f g h h' hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
/-- Actual system adjunction mates, their pasting and closed tensor-Hom transposes commute
with finite evaluation, independently of representatives, before taking an inverse limit.

Source: main-20261015 blueprint, sec-six-functors/sk-thm-sf-package,
prop-coef-integral-exceptional-adjoint.proof.md, final paragraph, ordinary-system refinement
(blueprint: lem-coef-system-adjunction-transpose-coherence).

Proof plan:
1. `strictSystemSequenceEquivalence` identifies strict systems with module sheaves on
   the small ringed sequence site. Apply `exists_isKFlatResolutionIndependentCoefficients`
   simultaneously to the tensor inputs. `kFlat_total_tensor_model` gives a flat-term K-flat
   total tensor, and `ringedDerived_closed_symmetric_monoidal` descends tensor, evaluation
   and the closed bijection to the ordinary unbounded derived category. Naturality of the
   simultaneous K-flat comparison gives representative independence.
2. `semilinearDerivedSections` supplies the canonical tensor-evaluation comparison and,
   precisely for normalized first Hom input, Hom evaluation preserving tensor evaluation.
   No flatness of the quotient coefficient maps is assumed.
3. Expand each actual mate into unit, transformation and counit. The specified adjunction
   evaluation equations identify its image with the finite mate word. The inverse mate
   identities already hold in the same system-category bijection.
4. Apply `mateEquiv_vcomp` and `mateEquiv_hcomp` to actual system squares and composite
   adjunctions; this proves both pasting equations on systems, and hence after evaluation.
5. A counit-compatible `rightAdjointUniq` identification gives equal left transposes of
   the two right mates. Injectivity of the adjunction Hom bijection identifies the maps.
6. Uncurry a system tensor-Hom transpose. Apply evaluation and the normalized Hom
   evaluation equation to obtain the finite uncurrying equation. Its unique solution is
   the finite transpose. This includes maps composed with units and counits since they
   are actual system maps. Both inverse identities hold in the system closed bijection.
   Naturality of the actual derived transitions, transposed through scalar adjunction,
   gives the reduction equation for every constructed map. No system equality is
   deduced from equality of evaluated morphisms and no total inverse limit is used.
-/
theorem systemAdjunctionTransposeCoherence
    (D₀ : FiniteFieldDatum.{t}) (hl : l ≠ D₀.p)
    (X Y : Over (Spec (CommRingCat.of D₀.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] [QuasiCompact f.left] [IsSeparated f.left]
    (compactification : Compactification f.left) :
    (∀ (W : Scheme.{t}) (_hW : W = X.left ∨ W = Y.left ∨ W = compactification.Z)
        (s : Bool),
      ∀ A : adjunctionSystemData l E W s,
        SemilinearSections.SystemTensorTransposeCoherence.{t + 1, t, u}
          (adjunctionSystemSite W s) (adjunctionSystemRings l E W s)
          (adjunctionSystemRingTransition l E W s) A) ∧
    (∀ (W W' : Scheme.{t}) (_hW : W = X.left ∨ W = Y.left ∨ W = compactification.Z)
      (_hW' : W' = X.left ∨ W' = Y.left ∨ W' = compactification.Z) (s s' : Bool),
      SystemAdjunctionCoherenceAt l E W W' s s') ∧
    (∀ (W : Fin 6 → Scheme.{t})
      (_hW : ∀ i : Fin 6, W i = X.left ∨ W i = Y.left ∨ W i = compactification.Z)
      (s : Fin 6 → Bool), SystemAdjunctionPastingAt l E W s) := by
  have _ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro W _ s A
    exact tensor_transpose_coherence (adjunctionSystemSite W s)
      (adjunctionSystemRings l E W s) (adjunctionSystemRingTransition l E W s) A
  · intro W W' _ _ s s' P Q n L L' R R' a a' l₀ l₁ r₀ r₁ b b' A A' α αn hα
    refine ⟨?_, (conjugateEquiv a' a).symm_apply_apply α,
      (conjugateEquiv a' a).apply_symm_apply, ?_, ?_⟩
    · have hm := SemilinearSections.evaluation_mate a' a b' b A' A
        (Iso.refl _) (Iso.refl _)
        (TwoSquare.mk _ _ _ _ (L.leftUnitor.hom ≫ α ≫ L'.rightUnitor.inv))
        (TwoSquare.mk _ _ _ _ (l₀.leftUnitor.hom ≫ αn ≫ l₁.rightUnitor.inv))
        (by simpa using hα)
      intro N
      simpa [conjugateEquiv] using hm N
    · intro L'' R'' a'' β
      exact (conjugateEquiv_comp a'' a' a β α).symm
    · intro J J' j j'
      simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, Iso.refl_hom,
        conjugateEquiv_comp, Category.comp_id, Category.id_comp]
  · intro W _ s P
    constructor
    · intros
      apply mateEquiv_vcomp
    · intros
      apply mateEquiv_hcomp

end CoherenceProofs

end WeilConjectures
