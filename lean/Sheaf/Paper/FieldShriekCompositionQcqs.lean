/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.FieldShriekCompositionNormalization
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportFiniteFieldIndependence
public import WeilConjectures.Compactification.Comp
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.FieldShriekCompositionCoefficientSquare
import Sheaf.Paper.FieldShriekCompositionIntegralComponent
import Sheaf.Paper.FieldShriekCompositionIntegralNaturality
import Sheaf.Paper.PbcRationalTransport

/-! # Canonical compact-support composition with field coefficients on qcqs schemes

Source: Stacks Project, Tag 0F7J, lemma-shriek-composition; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7 and 6.1.13, followed by raw rationalization
and common finite-stage descent (blueprint: lem-zl-field-shriek-composition-qcqs).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
open PurCompactSupport
open GeneralAlgebraicallyClosedCoefficients

private def rationalCompositionIso
    {R : Type*} [CommRing R] (t : R)
    {C D B : Type*} [Category C] [Category D] [Category B]
    [Preadditive C] [Preadditive D] [Preadditive B]
    [Linear R C] [Linear R D] [Linear R B]
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive]
    [F.Linear R] [G.Linear R] [H.Linear R] (α : F ⋙ G ≅ H) :
    ScalarLocalization.transport R t F ⋙ ScalarLocalization.transport R t G ≅
      ScalarLocalization.transport R t H :=
  NatIso.ofComponents
    (fun K ↦ (ScalarLocalization.localization R B t).mapIso (α.app K.obj)) (by
      intro K L a
      change ScalarLocalization.composition R B t _ _ _ (1 ⊗ₜ[R] α.hom.app L.obj)
          (ScalarLocalization.transportHom R t G _ _
            (ScalarLocalization.transportHom R t F _ _ a)) =
        ScalarLocalization.composition R B t _ _ _
          (ScalarLocalization.transportHom R t H _ _ a) (1 ⊗ₜ[R] α.hom.app K.obj)
      induction a using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        rfl
      | tmul a f =>
        simp only [ScalarLocalization.transportHom, LinearMap.baseChange_tmul,
          Functor.mapLinearMap_apply, ScalarLocalization.composition_tmul,
          mul_one, one_mul]
        exact congrArg (fun h ↦ a ⊗ₜ[R] h) (α.hom.naturality f)
      | add a b ha hb =>
        simp only [map_add]
        exact congrArg₂
          (fun x y : Localization.Away t ⊗[R] (G.obj (F.obj K.obj) ⟶ H.obj L.obj) ↦ x + y)
          ha hb)

private theorem map_relabel_iso_heq
    {C D B : Type*} [Category C] [Category D] [Category B]
    (L : D ⥤ B) {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G')
    (a : F' ≅ G') (K : C) :
    HEq (L.map ((eqToIso hF ≪≫ a ≪≫ (eqToIso hG).symm).hom.app K))
      (L.map (a.hom.app K)) := by
  subst F'
  subst G'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.trans_refl, Iso.refl_trans]
  exact HEq.rfl

section Field
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- Existence and canonicity of the actual integral compactification compositor.
Source: Stacks 0F7J; Bhatt--Scholze, Definition 6.7.6 and Lemmas 6.7.7, 6.1.13
(blueprint: lem-zl-field-shriek-composition-qcqs).

Proof (steps 1--5 of the DAG, before field-coefficient passage):
1. Finite-type schemes over the field are Noetherian and qcqs. Apply Nagata and
compatible-compactification-triangle to obtain d,e,V and the proper/open square.
Properness, quasi-compact opens and finite-type composition keep every ambient
scheme finite type and qcqs, without imposing separated structure morphisms.
2. Take strict derived reductions of each integral input. Constructible-origin
supplies finite-level etale origins; integral-residue-tor supplies uniform finite
Tor bounds. Integral compact-support constructibility and operation-reduction give
the same bounds and normalization for all intermediate proper/open expressions.
3. Construct the proper/open adjunction mate on actual semilinear systems, with its
unit normalization. Strict-tower-proper-open-calculus identifies its finite maps
and proves them invertible on these inputs. Conservativity tests invertibility of
this constructed system map; it does not lift a family of finite derived arrows.
4. Whisker by q and c and insert the canonical proper and open compositors. Apply
the total-limit functor and the natural Roos realization comparisons. The result
is the displayed completed-coefficient composite and the actual recorded nested
integral functor, on maps as well as objects.
5. Proper/open pasting and compactification-refinement-coherence commute with all
common refinements and compatible towers. Their normalized open adjoints give the
refinement isomorphisms in the predicate. Common refining towers and equalizers
make the map independent of choices and uniquely determine it. This argument takes
place before total limit; it never infers equality of system maps from evaluations. -/
theorem sfFieldShriekCompositionIntegral_existsUnique
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃! α : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E,
      SfIntegralCompositionSpec l E D.k (coefficientPrimeUnit l D hl) cf cg cfg α := by
  let a : ∀ K : sfIntegralConstructibleCategory l E X,
      (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (coefficientPrimeUnit l D hl) cf E).obj K) ≅
        (sfCompactSupportFiniteIntegralFunctor l D.k
          (coefficientPrimeUnit l D hl) cfg E).obj K :=
    fun K ↦ (sfFieldShriekCompositionIntegral_component D l hl cf cg cfg E K).exists.choose
  have ha (K : sfIntegralConstructibleCategory l E X) :
      SfIntegralCompositionComponentSpec D l hl cf cg cfg E K (a K).hom :=
    (sfFieldShriekCompositionIntegral_component D l hl cf cg cfg E K).exists.choose_spec
  let α := NatIso.ofComponents
    (F := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E)
    (G := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E)
    a (fun v ↦
    sfFieldShriekCompositionIntegral_component_naturality D l hl cf cg cfg E
      (a _).hom (a _).hom (ha _) (ha _) v)
  refine ⟨α, ?_, ?_⟩
  · intro d e rf rg rfg K
    exact ha K d e rf rg rfg
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext K
    have hb : SfIntegralCompositionComponentSpec D l hl cf cg cfg E K (β.hom.app K) := by
      intro d e rf rg rfg
      exact hβ d e rf rg rfg K
    have hb' : SfIntegralCompositionComponentSpec D l hl cf cg cfg E K
        (asIso (β.hom.app K)).hom := by
      simpa using hb
    have h := (sfFieldShriekCompositionIntegral_component D l hl cf cg cfg E K).unique
      hb' (ha K)
    simpa [α] using congrArg Iso.hom h

/-- The canonical integral compositor, selected only from its uniquely determining
proper/open and common-refinement normalization. Source: Stacks 0F7J
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfFieldShriekCompositionIntegral
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E :=
  (sfFieldShriekCompositionIntegral_existsUnique D l hl cf cg cfg E).exists.choose

/-- Raw rationalization gives exactly the field-coefficient composition comparison.
Its component is the localization of the actual integral component, so the
proper/open and common-refinement normalization is retained.
Source: Stacks 0F7J, with the Bhatt--Scholze integral construction and raw localization
(blueprint: lem-zl-field-shriek-composition-qcqs).

Proof (step 6 of the DAG): the recorded integral functors are exact and integral
linear. Rational-transport extends them uniquely on localized Hom groups, with
component alpha tensor one. The localized inverse is its inverse. The fixed
finite functors use precisely this pure-tensor extension. Uniqueness transports
the integral proper/open formula and all its common-refinement equalities.
No Karoubi completion and no change of integral representative is used. -/
theorem sfFieldShriekCompositionRational_existsUnique
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃! β : sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cfg E,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (β.hom.app K)
          ((sfRationalConstructibleLocalization l E Z).map
            ((sfFieldShriekCompositionIntegral D l hl cf cg cfg E).hom.app K.obj)) := by
  let t := Padic.coefficientExtensionUniformizer l E
  let F := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E
  let G := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E
  let H := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E
  let α := sfFieldShriekCompositionIntegral D l hl cf cg cfg E
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cf E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cf E).2
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cg E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cg E).2
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cfg E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) cfg E).2
  let β := rationalCompositionIso t F G H α
  refine ⟨β, fun K ↦ HEq.rfl, ?_⟩
  intro γ hγ
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq (hγ K)

/-- The canonical composition isomorphism at a finite coefficient field.
Source: Stacks 0F7J and raw rational passage
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfFieldShriekCompositionRational
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cfg E :=
  (sfFieldShriekCompositionRational_existsUnique D l hl cf cg cfg E).exists.choose

/-- On the common finite-stage category the component at (E,K) is the class of the
finite-field compositor. The three actions have the fixed finite functors and
normalized coefficient mates of the dependency definition. They are arbitrary
choices of that normalized construction; no geometric or coefficient hypothesis
is imposed on an input object.
Source: Stacks 0F7J with common finite-stage descent
(blueprint: lem-zl-field-shriek-composition-qcqs).

Proof (steps 7--8 of the DAG): coefficient extension preserves the actual units,
counits and tensor associators in the normalized proper/open mate. Operation-
reduction and scalar-extension-composition therefore identify the E compositor
with the F compositor after the canonical coefficient comparisons; tensor
associativity gives the identity and tower equations. Coherent-pair-functor-descent
then descends these transformations to arbitrary common-stage representatives.
The component is [E,alpha_E]; [E,alpha_E inverse] is its inverse. Equality after
further extension gives independence of representatives and of the common field.
The descent preserves composition and equations, hence also the compactification
formula and its common-refinement independence. This proves both field cases. -/
theorem sfFieldShriekCompositionQbar_existsUnique
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Sf : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cf)
    (Sg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cg)
    (Sfg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cfg) :
    ∃! γ : Sf.system.functor ⋙ Sg.system.functor ≅ Sfg.system.functor,
      ∀ (E₀ : Padic.FiniteCoefficientFields l Ω) (K : Stage l Ω X E₀),
        HEq (γ.hom.app ⟨E₀, K⟩)
          ((inclusion (l := l) (Ω := Ω) (Y := Z) E₀).map
            ((sfFieldShriekCompositionRational D l hl cf cg cfg
              (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)).hom.app K)) := by
  let A := fun E₀ : Padic.FiniteCoefficientFields l Ω ↦
    sfFieldShriekCompositionIntegral D l hl cf cg cfg
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)
  let B := fun E₀ : Padic.FiniteCoefficientFields l Ω ↦
    sfFieldShriekCompositionRational D l hl cf cg cfg
      (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)
  let e := sfCompositionOnCoefficientStage D l hl cf cg cfg Ω Sf Sg Sfg B
  let τ : (Sf.system.comp Sg.system).Hom Sfg.system :=
    { τ := fun E₀ ↦ (e E₀).hom
      comm := sfCompositionOnCoefficientStage_comm D l hl cf cg cfg Ω Sf Sg Sfg B A
        (fun E₀ ↦ (sfFieldShriekCompositionIntegral_existsUnique D l hl cf cg cfg
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)).exists.choose_spec)
        (fun E₀ ↦ (sfFieldShriekCompositionRational_existsUnique D l hl cf cg cfg
          (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)).exists.choose_spec) }
  have : IsIso (StageSystem.Morphism.descNatTrans τ) :=
    StageSystem.Morphism.isIso_descNatTrans τ (fun E₀ ↦ inferInstance)
  let γ := (StageSystem.Morphism.functorCompIso Sf.system Sg.system).symm ≪≫
    asIso (StageSystem.Morphism.descNatTrans τ)
  have hγ (E₀ : Padic.FiniteCoefficientFields l Ω) (K : Stage l Ω X E₀) :
      HEq (γ.hom.app ⟨E₀, K⟩) ((inclusion (l := l) (Ω := Ω) (Y := Z) E₀).map
        ((B E₀).hom.app K)) := by
    dsimp only [γ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      StageSystem.Morphism.functorCompIso_inv_app, asIso_hom]
    rw [Category.id_comp, StageSystem.Morphism.descNatTrans_app]
    exact map_relabel_iso_heq ((stageSystem l Ω Z).ι E₀)
      (congrArg₂ (fun F G ↦ F ⋙ G) (Sf.finite_eq E₀) (Sg.finite_eq E₀))
      (Sfg.finite_eq E₀) (B E₀) K
  refine ⟨γ, hγ, ?_⟩
  intro γ' hγ'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  obtain ⟨E₀, K⟩ := P
  exact eq_of_heq ((hγ' E₀ K).trans (hγ E₀ K).symm)

end Field
end WeilConjectures
