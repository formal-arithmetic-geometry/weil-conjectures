/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Sheaf.Paper.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Paper.NormalizedOriginScalarComparisons
public import Sheaf.Paper.PurEtaleScalarMateProjection
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleScalarFlatModel
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.Paper.FiniteConstructibleHom

/-! # Finite coefficient domains and evaluation transposition

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-finite-hom, opening proof paragraph; Stacks 03TT, 0GKB, 06YY, 07A4 and 08J9
(blueprint: lem-coef-finite-hom-domain-calculus).

The index n denotes exponent n + 1, as in the recorded finite-Hom arrow.
Thus all positive exponents and all identity quotients are included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a₁ a₂ a₃ b₁ b₂ b₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local implicit_reducible] CategoryTheory.uniformProd

attribute [local implicit_reducible] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Etale.upperStar
  Etale.scalarGeometricRepresentative

/-- The two unique-transpose laws, the reduced-evaluation characterization, and naturality.
The four clauses are kept behind one predicate so the coefficient categories and their
ring instances are shared before specialization. The comparison is the actual closed
transpose `coefficientBaseChangeHom`, not an additional field or a chosen witness.
Source: blueprint opening proof paragraph; Stacks 08J9
(blueprint: lem-coef-finite-hom-domain-calculus). -/
def FiniteHomDomainTransposeLaws
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    {H : Cᵒᵖ × C ⥤ C} {H' : C'ᵒᵖ × C' ⥤ C'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : C ⥤ C') (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor) : Prop :=
    (∀ (U K M : C) (t : S.tensor.obj (U, K) ⟶ M),
      ∃! g : U ⟶ H.obj (op K, M),
        S.tensor.map (Prod.mkHom g (𝟙 K)) ≫ S.evaluation K M = t) ∧
    (∀ (U K M : C') (t : S'.tensor.obj (U, K) ⟶ M),
      ∃! g : U ⟶ H'.obj (op K, M),
        S'.tensor.map (Prod.mkHom g (𝟙 K)) ≫ S'.evaluation K M = t) ∧
    (∀ (K M : C) (v : F.obj (H.obj (op K, M)) ⟶ H'.obj (op (F.obj K), F.obj M)),
      S'.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫ S'.evaluation (F.obj K) (F.obj M) =
          μ.inv.app (H.obj (op K, M), K) ≫ F.map (S.evaluation K M) ↔
        v = coefficientBaseChangeHom S S' F μ K M) ∧
    (∀ (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M'),
      F.map (H.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom S S' F μ K' M' =
        coefficientBaseChangeHom S S' F μ K M ≫
          H'.map (Prod.mkHom (F.map f).op (F.map g)))

namespace FiniteHomDomainClosedCalculus

section ClosedCalculus


attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  CoefficientClosedStructure.tensor
  CoefficientClosedStructure.evaluation CoefficientClosedStructure.transpose

private theorem domainUncurry
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (U K M : C) (g : U ⟶ H.obj (op K, M)) :
    (S.transpose U K M).symm g =
      S.tensor.map (Prod.mkHom g (𝟙 K)) ≫ S.evaluation K M := by
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, Equiv.symm]
  let := S.monoidal
  change S.monoidal.whiskerRight g K ≫ _ = S.monoidal.tensorHom g (𝟙 K) ≫ _
  rw [MonoidalCategory.tensorHom_id]


private theorem domainEvaluation_natural
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 K')) ≫
      S.evaluation K' M' =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M ≫ g := by
  let := S.monoidal
  have hf : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K')) ≫
      S.evaluation K' M =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op K, M))) f) ≫ S.evaluation K M := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫ _ =
      S.monoidal.tensorHom (𝟙 (H.obj (op K, M))) f ≫ _
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    exact S.evaluation_naturality K K' M f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K')) ≫
      S.evaluation K' M' = S.evaluation K' M ≫ g := by
    change S.monoidal.tensorHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') ≫ _ = _
    rw [MonoidalCategory.tensorHom_id]
    exact (S.adjunction K').counit.naturality g
  have hh : Prod.mkHom f.op g =
      Prod.mkHom f.op (𝟙 M) ≫ Prod.mkHom (𝟙 (op K')) g := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [hh, H.map_comp]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 M)) ≫ H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 M))) (𝟙 K') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K')) g)) (𝟙 K') := by
    ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]


private theorem domainUncurry_pre
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) {U V K M : C}
    (f : U ⟶ V) (g : V ⟶ H.obj (op K, M)) :
    (S.transpose U K M).symm (f ≫ g) =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ (S.transpose V K M).symm g := by
  rw [domainUncurry, domainUncurry, ← S.tensor.map_comp_assoc]
  simp only [CategoryTheory.prod_comp, Category.comp_id, Category.id_comp]


private theorem domainUncurry_post
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) {U K K' M M' : C}
    (v : U ⟶ H.obj (op K, M)) (f : K' ⟶ K) (g : M ⟶ M') :
    (S.transpose U K' M').symm (v ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 U) f) ≫ (S.transpose U K M).symm v ≫ g := by
  rw [domainUncurry_pre, domainUncurry, domainEvaluation_natural, domainUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp only [prod_comp_fst, prod_comp_snd, Category.comp_id, Category.id_comp]


private theorem domainBaseChange_uncurry
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    {H : Cᵒᵖ × C ⥤ C} {H' : C'ᵒᵖ × C' ⥤ C'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : C ⥤ C') (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor) (K M : C) :
    (S'.transpose (F.obj (H.obj (op K, M))) (F.obj K) (F.obj M)).symm
        (coefficientBaseChangeHom S S' F μ K M) =
      μ.inv.app (H.obj (op K, M), K) ≫ F.map (S.evaluation K M) := by
  unfold coefficientBaseChangeHom
  exact (S'.transpose _ _ _).symm_apply_apply _


attribute [local irreducible] coefficientBaseChangeHom

private theorem domainBaseChange_natural
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    {H : Cᵒᵖ × C ⥤ C} {H' : C'ᵒᵖ × C' ⥤ C'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : C ⥤ C') (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    F.map (H.map (Prod.mkHom f.op g)) ≫ coefficientBaseChangeHom S S' F μ K' M' =
      coefficientBaseChangeHom S S' F μ K M ≫
        H'.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply (S'.transpose (F.obj (H.obj (op K, M))) (F.obj K') (F.obj M')).symm.injective
  rw [domainUncurry_pre S', domainUncurry_post S']
  simp only [domainBaseChange_uncurry]
  have hμ₁ := μ.inv.naturality
    (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 K'))
  have hμ₂ := μ.inv.naturality (Prod.mkHom (𝟙 (H.obj (op K, M))) f)
  simp only [Functor.comp_map, Functor.prod_map, F.map_id] at hμ₁ hμ₂
  rw [← Category.assoc, hμ₁, Category.assoc, ← F.map_comp,
    domainEvaluation_natural S, F.map_comp, F.map_comp, ← Category.assoc,
    ← Category.assoc, ← hμ₂]
  simp only [Category.assoc]


private theorem domainTranspose_unique
    {C : Type a₁} [Category.{b₁} C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (U K M : C) (t : S.tensor.obj (U, K) ⟶ M) :
    ∃! g : U ⟶ H.obj (op K, M),
      S.tensor.map (Prod.mkHom g (𝟙 K)) ≫ S.evaluation K M = t := by
  exact ⟨S.transpose U K M t,
    (domainUncurry S U K M (S.transpose U K M t)).symm.trans
      ((S.transpose U K M).symm_apply_apply t),
    fun g hg ↦ (S.transpose U K M).symm.injective
      ((domainUncurry S U K M g).trans
        (hg.trans ((S.transpose U K M).symm_apply_apply t).symm))⟩


private theorem domainBaseChange_iff
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    {H : Cᵒᵖ × C ⥤ C} {H' : C'ᵒᵖ × C' ⥤ C'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : C ⥤ C') (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor)
    (K M : C) (v : F.obj (H.obj (op K, M)) ⟶ H'.obj (op (F.obj K), F.obj M)) :
    S'.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫ S'.evaluation (F.obj K) (F.obj M) =
        μ.inv.app (H.obj (op K, M), K) ≫ F.map (S.evaluation K M) ↔
      v = coefficientBaseChangeHom S S' F μ K M := by
  constructor
  · intro hv
    apply (S'.transpose (F.obj (H.obj (op K, M))) (F.obj K) (F.obj M)).symm.injective
    exact (domainUncurry S' _ _ _ v).trans
      (hv.trans (domainBaseChange_uncurry S S' F μ K M).symm)
  · intro hv
    subst v
    exact (domainUncurry S' _ _ _ (coefficientBaseChangeHom S S' F μ K M)).symm.trans
      (domainBaseChange_uncurry S S' F μ K M)


private theorem domainCalculus
    {C : Type a₁} {C' : Type a₂} [Category.{b₁} C] [Category.{b₂} C']
    {H : Cᵒᵖ × C ⥤ C} {H' : C'ᵒᵖ × C' ⥤ C'}
    (S : CoefficientClosedStructure H) (S' : CoefficientClosedStructure H')
    (F : C ⥤ C') (μ : S.tensor ⋙ F ≅ F.prod F ⋙ S'.tensor) :
    FiniteHomDomainTransposeLaws S S' F μ := by
  exact ⟨domainTranspose_unique S, domainTranspose_unique S',
    domainBaseChange_iff S S' F μ, domainBaseChange_natural S S' F μ⟩


end ClosedCalculus

end FiniteHomDomainClosedCalculus

/-- The existing coefficient ring, lifted to the ordinary small-etale coefficient universe.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
abbrev finiteHomDomainCoeff (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))

/-- Positive coefficient levels are finite, by the recorded coefficient-ring theorem.
Source: blueprint finite coefficient convention
(blueprint: lem-coef-finite-hom-domain-calculus). -/
instance finiteHomDomainCoeffFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (finiteHomDomainCoeff l E n) :=
  @Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))) Equiv.ulift.symm

/-- Strong monoidality for fixed tensor, unit and signed symmetry components.
Heterogeneous equalities identify the components without changing their data.
Source: blueprint ambient monoidality clause; Stacks 07A4 and 0FPT
(blueprint: lem-coef-finite-hom-domain-calculus). -/
def FiniteHomDomainMonoidal {C : Type a₁} {C' : Type a₂}
    [Category.{b₁} C] [Category.{b₂} C'] [MonoidalCategory C] [MonoidalCategory C']
    (F : C ⥤ C') {V : C → C → Type b₂} (δ : ∀ U V', V U V')
    {W : Type b₂} (e : W)
    {B : C → C → Type b₁} (σ : ∀ U V, B U V)
    {B' : C' → C' → Type b₂} (σ' : ∀ U V, B' U V) : Prop :=
  ∃ S : F.CoreMonoidal,
    HEq S.εIso.symm e ∧
    (∀ U V, HEq (S.μIso U V).symm (δ U V)) ∧
    (∃ β : ∀ U V : C, U ⊗ V ≅ V ⊗ U,
      ∃ β' : ∀ U V : C', U ⊗ V ≅ V ⊗ U,
      (∀ U V, HEq (β U V) (σ U V)) ∧
      (∀ U V, HEq (β' U V) (σ' U V)) ∧
      ∀ U V, (β' (F.obj U) (F.obj V)).hom ≫ (S.μIso V U).hom =
        (S.μIso U V).hom ≫ F.map (β U V).hom)

/-- The tensor and unit squares for a specified scalar composition comparison.
Source: blueprint successive-coefficient clause; Stacks 0D6D and 07A4
(blueprint: lem-coef-finite-hom-domain-calculus). -/
def FiniteHomDomainScalarComposition
    {C : Type a₁} {C' : Type a₂} {C'' : Type a₃}
    [Category.{b₁} C] [Category.{b₂} C'] [Category.{b₃} C'']
    (T : C × C ⥤ C) (T' : C' × C' ⥤ C') (T'' : C'' × C'' ⥤ C'')
    (I : C) (I' : C') (I'' : C'') (F : C ⥤ C') (G : C' ⥤ C'') (H : C ⥤ C'')
    (α : F ⋙ G ≅ H)
    {D₀ : C → C → Type b₂} (d₀ : ∀ U V, D₀ U V)
    {D₁ : C' → C' → Type b₃} (d₁ : ∀ U V, D₁ U V)
    {D₂ : C → C → Type b₃} (d₂ : ∀ U V, D₂ U V)
    {V : Type b₂} (e₀ : V) {V' : Type b₃} (e₁ : V') {V'' : Type b₃} (e₂ : V'') :
    Prop :=
  ∃ δ : ∀ U V : C, F.obj (T.obj (U, V)) ≅ T'.obj (F.obj U, F.obj V),
  ∃ δ' : ∀ U V : C', G.obj (T'.obj (U, V)) ≅ T''.obj (G.obj U, G.obj V),
  ∃ δ'' : ∀ U V : C, H.obj (T.obj (U, V)) ≅ T''.obj (H.obj U, H.obj V),
  ∃ e : F.obj I ≅ I', ∃ e' : G.obj I' ≅ I'', ∃ e'' : H.obj I ≅ I'',
  (∀ U V, HEq (δ U V) (d₀ U V)) ∧
  (∀ U V, HEq (δ' U V) (d₁ U V)) ∧
  (∀ U V, HEq (δ'' U V) (d₂ U V)) ∧
  HEq e e₀ ∧ HEq e' e₁ ∧ HEq e'' e₂ ∧
  (∀ U V : C,
    α.hom.app (T.obj (U, V)) ≫ (δ'' U V).hom =
      G.map (δ U V).hom ≫ (δ' (F.obj U) (F.obj V)).hom ≫
        T''.map (Prod.mkHom (α.hom.app U) (α.hom.app V))) ∧
  α.hom.app I ≫ e''.hom = G.map e.hom ≫ e'.hom

/-- The tensor and unit squares for the specified identity scalar comparison.
Source: blueprint identity-coefficient clause; Stacks 07A4
(blueprint: lem-coef-finite-hom-domain-calculus). -/
def FiniteHomDomainScalarIdentity {C : Type a₁} [Category.{b₁} C]
    (T : C × C ⥤ C) (I : C) (F : C ⥤ C)
    {D₀ : C → C → Type b₁} (d₀ : ∀ U V, D₀ U V)
    {V : Type b₁} (e₀ : V) (z : F ≅ 𝟭 C) : Prop :=
  ∃ δ : ∀ U V : C, F.obj (T.obj (U, V)) ≅ T.obj (F.obj U, F.obj V),
  ∃ e : F.obj I ≅ I,
  (∀ U V, HEq (δ U V) (d₀ U V)) ∧ HEq e e₀ ∧
  (∀ U V : C, (δ U V).hom ≫
    T.map (Prod.mkHom (z.hom.app U) (z.hom.app V)) = z.hom.app (T.obj (U, V))) ∧
  e.hom = z.hom.app I

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [hXover : X.Over (Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [hXqc : QuasiCompact (X ↘ Spec (.of D.k))]

include D hl hXover hXsep hXft hXqc in
/-- Noetherianity and the flat constructible model in the original Tor interval, including
its actual scalar extension with its target coefficient action.
Source: blueprint opening proof paragraph; Stacks 01T6, 03TT, 0GKB, 06YQ and 06YY
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: the structure morphism is of finite type over the Noetherian field D.k, so X
is Noetherian (lem-weil-pbc-finite-type-over-noetherian). Apply
lem-sp-etale-scalar-flat-model to the actual finite-ring quotient. Its model is flat
constructible and supported in [a,b]. Bounded flatness gives K-flatness, and
lem-pur-kflat-change-of-rings preserves flat terms and K-flatness. Constructibility
of the scalar-extended terms is 0GKB. The universal K-flat counit of
lem-pur-derived-change-of-rings computes F_X on this model. Tensoring the reduced
bounded flat complex with any degree-zero B-module sheaf proves the same Tor bound.
No flatness of B over A is used. -/
theorem finiteHomDomain_flatModel {n m : ℕ} (h : m ≤ n) (a b : ℤ) (hab : a ≤ b)
    (T : finiteHomEtale l E X n)
    (hT : Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E n) X T)
    (hTor : Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E n) X a b T) :
    IsNoetherian X ∧
    (∃ P : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))) ℤ,
      Etale.IsBoundedFlatComplex (finiteHomDomainCoeff l E n) a b P ∧
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (P.X i)) ∧
      Nonempty (T ≅ _root_.DerivedCategory.Q.obj P) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      Etale.IsBoundedFlatComplex (finiteHomDomainCoeff l E m) a b
        (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P) ∧
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        ((((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P).X i)) ∧
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
        (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P) ∧
      Nonempty ((finiteHomEtaleReduction l E X h).obj T ≅ _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex (.up
          ℤ)).obj P))) ∧
    Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E m) X
      ((finiteHomEtaleReduction l E X h).obj T) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E m) X a b
      ((finiteHomEtaleReduction l E X h).obj T) := by
  have : IsNoetherian X := by
    have : IsLocallyNoetherian X :=
      @LocallyOfFiniteType.isLocallyNoetherian X (Spec (.of D.k))
        (X ↘ Spec (.of D.k)) hXft inferInstance
    have : CompactSpace X :=
      @QuasiCompact.compactSpace_of_compactSpace X (Spec (.of D.k))
        (X ↘ Spec (.of D.k)) hXqc inferInstance
    exact ⟨⟩
  let J : _root_.DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))) :=
    ⟨T, by
      obtain ⟨c, d, _, hv⟩ := hT.2
      exact ⟨⟨c, (_root_.DerivedCategory.isGE_iff T c).2
        (fun i hi ↦ hv i (.inl hi))⟩,
        ⟨d, (_root_.DerivedCategory.isLE_iff T d).2
          (fun i hi ↦ hv i (.inr hi))⟩⟩⟩
  obtain ⟨⟨P, hf, hc, hz, he⟩, models, ⟨L, ⟨eL⟩⟩, hcons, ht⟩ :=
    Etale.exists_etaleScalarFlatModel X (finiteHomDomainCoeff l E n)
      (finiteHomDomainCoeff l E m) (finiteHomQuotient l E h) a b hab J hT.1 hTor
  obtain ⟨hk, hQk, hQf, hQc, hQz, hQe⟩ := models P hf hc hz he
  have flat (q : ℤ) : ObjectProperty.flat (P.X q) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X q)).symm (hf q), hf q⟩
  refine ⟨inferInstance, ⟨P, ⟨hz, flat⟩, hc, ⟨he.some.symm⟩, hk,
    ⟨hQz, fun q ↦ ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm (hQf q), hQf q⟩⟩,
    hQc, hQk, hQe⟩, ⟨hcons, ?_⟩, ht⟩
  obtain ⟨c, hge⟩ := L.property.1
  obtain ⟨d, hle⟩ := L.property.2
  refine ⟨min c d, d, min_le_right _ _, fun i hi ↦ ?_⟩
  apply IsZero.of_iso _ ((_root_.DerivedCategory.homologyFunctor _ i).mapIso eL).symm
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff L.obj c).1 hge i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff L.obj d).1 hle i hi


attribute [local irreducible] ProEtale.pbcFixedScalarExtension
  Etale.scalarExtensionRepresentative Etale.scalarSheafPullbackComplexIso

section PullbackCompatibility

attribute [local instance 2000] CommRing.toRing

private theorem finiteHomDomain_boundedConstructible_iff
    (R : Type (u + 1)) [CommRing R] [Finite R] (W : Scheme.{u})
    (M : Etale.DerivedCategoryModule R W) :
    Etale.DerivedCategory.isBoundedConstructible R W M ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) W M := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff M a).mpr fun i hi ↦ hz i (.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff M b).mpr fun i hi ↦ hz i (.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff M a).mp ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff M b).mp hb i hi

section Pullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

include D hl hXover hXsep hXft hXqc in
/-- Exact inverse image preserves bounded constructibility and the given Tor interval;
the specified scalar/pullback isomorphism is a morphism of B-module derived categories.
Source: blueprint opening proof paragraph; Stacks 04JC, 05VD, 095G, 07A4 and 0G7E
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: prop-weil-pbc-inverse-image-modules-exact identifies pullback with exact inverse
image. Its homology is the inverse image of homology; prop-constructible-pullback
preserves constructibility. Pull the preceding bounded flat constructible model back
termwise. Flatness is preserved by lem-weil-pbc-ringed-topos-flat-module-pullback,
and the same support and lem-kun-kflat-criteria give the Tor interval. The comparison
is the canonical normalized scalarPullbackIso of def-pur-etale-scalar-pullback-iso;
lem-pur-etale-scalar-pullback-existence gives its existence. The exact/derived
identification is lem-pur-exact-pullback-signed-comparison. -/
theorem finiteHomDomain_pullback (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : Y ⟶ X) [f.IsOver (Spec (.of D.k))] {n m : ℕ} (h : m ≤ n) :
    exactFunctor _ _ (Etale.upperStar (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n)) f) ∧
    (∀ (a b : ℤ), a ≤ b → ∀ T : finiteHomEtale l E X n,
      Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E n) X T →
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E n) X a b T →
      Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E n) Y
        ((Etale.upperStar (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n)) f).leftDerivedFunctor.obj
          T) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E n) Y a b
        ((Etale.upperStar (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n)) f).leftDerivedFunctor.obj
          T)) ∧
    (∀ P : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (Etale.scalarPullbackIso (finiteHomQuotient l E h) f).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫
        (finiteHomEtaleReduction l E Y h).map
          (Etale.scalarGeometricRepresentative (finiteHomDomainCoeff l E n) f P) ≫
        Etale.scalarExtensionRepresentative (finiteHomQuotient l E h) Y
          (((Etale.upperStar (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))
            f).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (Etale.upperStar (ModuleCat.{u + 1} (finiteHomDomainCoeff l E m)) f).leftDerivedFunctor.map
        (Etale.scalarExtensionRepresentative
            (finiteHomQuotient l E h) X P) ≫
        Etale.scalarGeometricRepresentative (finiteHomDomainCoeff l E m) f
          (((ProEtale.etaleSheafExtendScalars (finiteHomQuotient l E h) X).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        _root_.DerivedCategory.Q.map
          ((Etale.scalarSheafPullbackComplexIso (finiteHomQuotient l E h) f).hom.app P)) := by
  refine ⟨(exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro a b _ T hT ht
    refine ⟨(finiteHomDomain_boundedConstructible_iff _ Y _).mpr
      (Etale.boundedConstructible_leftDerivedUpperStar _ f
        ((finiteHomDomain_boundedConstructible_iff _ X _).mp hT)), ?_⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (Etale.torAmplitudeIn_leftDerivedUpperStar _ f a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht))
  · exact (Etale.scalarPullbackIso_existsUnique (finiteHomQuotient l E h) f).choose_spec.1

end Pullback
end PullbackCompatibility

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include D hl hXover hXsep hXft hXqc in
/-- Both endpoints of the ambient evaluation transpose are finite-Tor constructible.
Source: blueprint opening proof paragraph and cor-weil-finite-constructible-hom
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: lem-kun-dimension-finite-type bounds the dimension of X, also for empty X.
Apply cor-weil-finite-constructible-hom at level n+1 to K,M, and then the scalar-domain
assertion to their internal Hom. Apply the scalar-domain assertion separately to
K and M, and the same internal-Hom corollary at level m+1 to the resulting pair.
These give bounded constructibility and finite Tor amplitude of the two endpoints.
This argument asserts no invertibility of their comparison. -/
theorem finiteHomDomain_endpoints {n m : ℕ} (h : m ≤ n)
    (K M : finiteHomEtale l E X n)
    (hK : Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E n) X K)
    (hM : Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E n) X M)
    (hKt : ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E n) X a b K)
    (hMt : ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E n) X a b M) :
    (Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E m) X
        ((finiteHomEtaleReduction l E X h).obj
          ((finiteHomEtaleInternalHom l E X n).obj (op K, M))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E m) X a b
          ((finiteHomEtaleReduction l E X h).obj
            ((finiteHomEtaleInternalHom l E X n).obj (op K, M)))) ∧
    (Etale.DerivedCategory.isBoundedConstructible (finiteHomDomainCoeff l E m) X
        ((finiteHomEtaleInternalHom l E X m).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)) ∧
      ∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (finiteHomDomainCoeff l E m) X a b
          ((finiteHomEtaleInternalHom l E X m).obj
            (op ((finiteHomEtaleReduction l E X h).obj K),
              (finiteHomEtaleReduction l E X h).obj M))) := by
  obtain ⟨a, b, hab, htK⟩ := hKt
  obtain ⟨c, e, hce, htM⟩ := hMt
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  have hH := finite_constructible_derivedHom_etale D l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) X d hd a b c e hab hce K M hK hM
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htK)
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 htM)
  have hinterval : c - b - 2 * (d : ℤ) ≤ e - a + 2 * (d : ℤ) := by omega
  have hs := finiteHomDomain_flatModel D l hl E X h _ _ hinterval _ hH.1
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hH.2)
  have hsK := finiteHomDomain_flatModel D l hl E X h a b hab K hK htK
  have hsM := finiteHomDomain_flatModel D l hl E X h c e hce M hM htM
  have hH' := finite_constructible_derivedHom_etale D l hl E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m)) X d hd a b c e hab hce _ _
    hsK.2.2.1 hsM.2.2.1
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hsK.2.2.2)
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hsM.2.2.2)
  exact ⟨⟨hs.2.2.1, _, _, hinterval, hs.2.2.2⟩,
    ⟨hH'.1, _, _, hinterval,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hH'.2⟩⟩


/-- The actual self-quotient is the identity homomorphism.
Source: blueprint identity-coefficient clause
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: quotient induction reduces the equality to the residue class of an element
of the valuation ring. Both homomorphisms send it to that same residue class. -/
theorem finiteHomDomain_quotient_id (n : ℕ) :
    finiteHomQuotient l E (le_refl n) = RingHom.id (finiteHomDomainCoeff l E n) := by
  ext x
  change Ideal.Quotient.factor (le_refl (Padic.coefficientExtensionIdeal l E (n + 1)))
    x.down = x.down
  rw [Ideal.Quotient.factor_eq]
  rfl

/-- The canonical identity scalar comparison, the mate of identity on restriction.
Its action on flat models is multiplication, not an arbitrary automorphism.
Source: blueprint identity-coefficient clause; Stacks 06YY
(blueprint: lem-coef-finite-hom-domain-calculus). -/
def finiteHomDomainUnit (n : ℕ) :
    finiteHomEtaleReduction l E X (le_refl n) ≅ 𝟭 (finiteHomEtale l E X n) :=
  ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
    (finiteHomQuotient l E (le_refl n)) (finiteHomDomain_quotient_id l E n)

include D hl hXover hXsep hXft hXqc in
/-- The canonical tensor and constant-unit comparisons make ambient coefficient change
strong symmetric monoidal, for the actual signed tensor and Koszul braiding.
Source: blueprint opening proof paragraph; Stacks 07A4 and 0FPT
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: apply lem-weil-pbc-ringed-topoi-derived-tensor-pullback to the identity topos
with the actual quotient ring map. The representative normalization and both unit
constraints are lem-weil-pbc-pullback-tensor-canonical-shift-unit. On flat-term
K-flat models from lem-pc-kflat-resolution, the comparison is the ordinary balancing
map (x tensor y) tensor b to (x tensor b) tensor (y tensor 1). Its inverse multiplies
the two scalars. lem-pur-cochain-pullback-tensor-coherence proves associativity,
unitality and compatibility with the signed symmetry before localization;
lem-sfb-ringed-derived-monoidal-comparisons descends precisely these equations.
The normalized closed and tensor witnesses in def-sf-etale-finite-coefficient-hom-arrow
identify these comparisons with the published finiteHomEtaleTensor. -/
theorem finiteHomDomain_monoidal {n m : ℕ} (h : m ≤ n) :
    FiniteHomDomainMonoidal (finiteHomEtaleReduction l E X h)
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso
        (finiteHomQuotient l E h) X).app (U, V))
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X)
      (finiteHomKoszulIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n))))
      (finiteHomKoszulIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (finiteHomDomainCoeff l E m)))) ∧
    HEq (finiteHomEtaleTensor l E X h)
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) ∧
    Etale.ExceptionalCoefficients.UnitNormalization (finiteHomQuotient l E h) X
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X) ∧
    Etale.ExceptionalCoefficients.TensorNormalization (finiteHomQuotient l E h) X
      (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X) := by
  sorry

include D hl hXover hXsep hXft hXqc in
/-- Tensor and unit comparisons agree with actual successive scalar extension and
with the identity quotient, on the ambient unbounded categories.
Source: blueprint successive-quotient and identity clauses; Stacks 0D6D and 07A4
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: lem-pur-system-scalar-model and lem-pur-system-scalar-coherence compute the
scalar associator on flat-term K-flat models as (x tensor b) tensor c to x tensor bc.
The tensor composition equation of lem-pur-cochain-pullback-tensor-coherence sends
both routes to (x tensor bc) tensor (y tensor 1); the unit square multiplies the
same scalars. lem-sfb-ringed-derived-monoidal-comparisons makes the canonical
composition comparison monoidal, and its identity clause gives the final two
identities. K-flat change of rings allows every nonflat quotient tower. -/
theorem finiteHomDomain_scalarCoherence {n m r : ℕ} (h : m ≤ n) (k : r ≤ m) :
    FiniteHomDomainScalarComposition
      (Functor.uncurry.obj (Etale.derivedTensor
        (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n)) X))
      (Functor.uncurry.obj (Etale.derivedTensor
        (ModuleCat.{u + 1} (finiteHomDomainCoeff l E m)) X))
      (Functor.uncurry.obj (Etale.derivedTensor
        (ModuleCat.{u + 1} (finiteHomDomainCoeff l E r)) X))
      (𝟙_ (finiteHomEtale l E X n)) (𝟙_ (finiteHomEtale l E X m))
      (𝟙_ (finiteHomEtale l E X r))
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleReduction l E X k)
      (finiteHomEtaleReduction l E X (k.trans h)) (finiteHomEtaleAssoc l E X h k)
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E h) X).app (U, V))
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso (finiteHomQuotient l E k) X).app (U, V))
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso
        (finiteHomQuotient l E (k.trans h)) X).app (U, V))
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E h) X)
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E k) X)
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E (k.trans h)) X) ∧
    FiniteHomDomainScalarIdentity
      (Functor.uncurry.obj (Etale.derivedTensor
        (ModuleCat.{u + 1} (finiteHomDomainCoeff l E n)) X))
      (𝟙_ (finiteHomEtale l E X n)) (finiteHomEtaleReduction l E X (le_refl n))
      (fun U V ↦ (Etale.ExceptionalCoefficients.tensorIso
        (finiteHomQuotient l E (le_refl n)) X).app (U, V))
      (Etale.ExceptionalCoefficients.unitIso (finiteHomQuotient l E (le_refl n)) X)
      (finiteHomDomainUnit l E X n) := by
  sorry

attribute [local implicit_reducible] CategoryTheory.catToReflQuiver

attribute [local irreducible] finiteHomEtaleData finiteHomEtaleClosed finiteHomEtaleTensor
  Etale.derivedHom coefficientBaseChangeHom
  CoefficientClosedStructure.tensor CoefficientClosedStructure.evaluation
  CoefficientClosedStructure.transpose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include D hl hXover hXsep hXft hXqc in
/-- The two ambient tensor-Hom adjunctions have counit evaluation, and reduced
evaluation has exactly the canonical transpose, naturally in both inputs.
Source: blueprint opening proof paragraph; Stacks 08J9
(blueprint: lem-coef-finite-hom-domain-calculus).

Proof: the existing normalized closed records supply the ambient adjunctions,
with the Hom object first. Their Hom equivalences and counits give the first two
unique-transpose assertions. For reduced evaluation use
the inverse tensor comparison followed by F_X of the A-evaluation. Its unique
B-transpose is exactly etaleFiniteHomCanonical by
def-sf-etale-finite-coefficient-hom-arrow. The adjunction's naturality and the
tensor comparison's naturality give naturality in both K and M. This argument
uses arbitrary unbounded objects and makes no assertion of invertibility. -/
theorem finiteHomDomain_transpose {n m : ℕ} (h : m ≤ n) :
    FiniteHomDomainTransposeLaws
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) := by
  exact FiniteHomDomainClosedCalculus.domainCalculus
    (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
    (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h)


end WeilConjectures
