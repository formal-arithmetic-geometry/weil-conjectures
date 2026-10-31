/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.FiniteOpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleAllStages
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.Algebra.Homology.DerivedScalarExtensionCounitShift

/-! # Reduction of the recollement connecting map

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (3)
(blueprint: lem-sf-recollement-reduction-boundary).

The comparison components are composites of the operation datum's specified
reduction comparisons. All triangles and shift comparisons live in the ambient
ordinary derived categories. The positive coefficient exponent is `m + 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
  {Z U X : SixFunctorSpace D} (i : Z ⟶ X) (j : U ⟶ X)
  (hj : IsOpenImmersion j.hom.left)

/-- The integral open vertex, using the datum's operations and ambient inclusion.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary). -/
def sfReductionIntegralOpen :=
  S.higher.integral.pull j ⋙ S.higher.integral.openExtension j hj ⋙
    (sfIntegralConstructible C.l E X.obj.left).ι

/-- The integral closed vertex with its ambient inclusion.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary). -/
def sfReductionIntegralClosed :=
  S.higher.integral.pull i ⋙ S.higher.integral.direct i ⋙
    (sfIntegralConstructible C.l E X.obj.left).ι

/-- The finite open vertex evaluated on the actual reduction of the integral input.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary). -/
def sfReductionFiniteOpen (m : ℕ) :=
  sixFunctorIntegralReduction D C E m X ⋙
    (S.integralNormalization.finiteLevels m).finite.pull j ⋙
    (S.integralNormalization.finiteLevels m).finite.openExtension j hj ⋙
    (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι

/-- The finite closed vertex evaluated on the actual reduction of the integral input.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary). -/
def sfReductionFiniteClosed (m : ℕ) :=
  sixFunctorIntegralReduction D C E m X ⋙
    (S.integralNormalization.finiteLevels m).finite.pull i ⋙
    (S.integralNormalization.finiteLevels m).finite.direct i ⋙
    (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι

/-- The specified open reduction comparison: first reduce open extension, then pullback.
Source: operation reduction and package clause (3)
(blueprint: lem-sf-recollement-reduction-boundary). -/
def sfRecollementReductionOpenIso (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (scalarReductionDerivedExtension C.l E X.obj.left m).obj
        ((sfReductionIntegralOpen S j hj).obj K) ≅
      (sfReductionFiniteOpen S j hj m).obj K :=
  (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι.mapIso
      (((S.integralNormalization.reduction m).openExtension j hj).app
        ((S.higher.integral.pull j).obj K)) ≪≫
    (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι.mapIso
      ((S.integralNormalization.finiteLevels m).finite.openExtension j hj |>.mapIso
        (((S.integralNormalization.reduction m).directAdjunction j).left.app K))

/-- The specified closed reduction comparison: first reduce direct image, then pullback.
Source: operation reduction and package clause (3)
(blueprint: lem-sf-recollement-reduction-boundary). -/
def sfRecollementReductionClosedIso (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (scalarReductionDerivedExtension C.l E X.obj.left m).obj
        ((sfReductionIntegralClosed S i).obj K) ≅
      (sfReductionFiniteClosed S i m).obj K :=
  (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι.mapIso
      (((S.integralNormalization.reduction m).directAdjunction i).right.app
        ((S.higher.integral.pull i).obj K)) ≪≫
    (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι.mapIso
      ((S.integralNormalization.finiteLevels m).finite.direct i |>.mapIso
        (((S.integralNormalization.reduction m).directAdjunction i).left.app K))

/-- The integral triangle with the prescribed counit and unit and any connecting arrow.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary). -/
def sfReductionIntegralTriangle (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (δ : (sfReductionIntegralClosed S i).obj K ⟶
      ((sfReductionIntegralOpen S j hj).obj K)⟦(1 : ℤ)⟧) :=
  Triangle.mk
    ((sfIntegralConstructible C.l E X.obj.left).ι.map
      ((S.higher.integral.openAdjunction j hj).counit.app K))
    ((sfIntegralConstructible C.l E X.obj.left).ι.map
      ((S.higher.integral.pullDirectAdjunction i).unit.app K)) δ

/-- The finite triangle with the datum's finite counit and unit, normalized by its
finite adjunction realization to the ordinary finite recollement definition.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary). -/
def sfReductionFiniteTriangle (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (δ : (sfReductionFiniteClosed S i m).obj K ⟶
      ((sfReductionFiniteOpen S j hj m).obj K)⟦(1 : ℤ)⟧) :=
  Triangle.mk
    ((intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι.map
      (((S.integralNormalization.finiteLevels m).finite.openAdjunction j hj).counit.app
        ((sixFunctorIntegralReduction D C E m X).obj K)))
    ((intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι.map
      (((S.integralNormalization.finiteLevels m).finite.pullDirectAdjunction i).unit.app
        ((sixFunctorIntegralReduction D C E m X).obj K))) δ

/-- Apply the actual derived reduction, with the tensor shift structure transported
along its canonical finite-reduction identification. No shift structure is assumed.
Source: Stacks 06YY and package clause (3)
(blueprint: lem-sf-recollement-reduction-boundary). -/
def sfRecollementReducedTriangle (m : ℕ)
    (T : Triangle (DerivedCategory (scalarReductionSource C.l E X.obj.left))) :=
  (@Functor.mapTriangle _ _ _ _ _ _ (scalarReductionDerivedExtension C.l E X.obj.left m)
    (Functor.CommShift.ofIso (PurCompactSupport.finiteReductionIso C.l E X.obj.left m)
      ℤ)).obj T

private theorem sfReduction_counit_unit (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (δ : (sfReductionIntegralClosed S i).obj K ⟶
      ((sfReductionIntegralOpen S j hj).obj K)⟦(1 : ℤ)⟧)
    (δn : (sfReductionFiniteClosed S i m).obj K ⟶
      ((sfReductionFiniteOpen S j hj m).obj K)⟦(1 : ℤ)⟧) :
    (scalarReductionDerivedExtension.{u, u} C.l E X.obj.left m).map
        (sfReductionIntegralTriangle S i j hj K δ).mor₁ =
      (sfRecollementReductionOpenIso S j hj m K).hom ≫
        (sfReductionFiniteTriangle S i j hj m K δn).mor₁ ∧
    (scalarReductionDerivedExtension.{u, u} C.l E X.obj.left m).map
        (sfReductionIntegralTriangle S i j hj K δ).mor₂ ≫
        (sfRecollementReductionClosedIso S i m K).hom =
      (sfReductionFiniteTriangle S i j hj m K δn).mor₂ := by
  let R := S.integralNormalization.reduction m
  let T := (S.integralNormalization.finiteLevels m).finite
  let F : sixFunctorFiniteCategory D C E (m + 1) (Nat.succ_pos m) X ⥤
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (m + 1)) :=
    (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι
  constructor
  · have hc := (R.openAdjunction j hj).counit K
    rw [R.openAdjunction_left j hj, R.openAdjunction_right j hj] at hc
    have hc' := congrArg (fun f ↦ (R.openExtension j hj).hom.app
      ((S.higher.integral.pull j).obj K) ≫ f) hc
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hc'
    exact (congrArg F.map hc').symm.trans (by
      simp only [Functor.map_comp, sfRecollementReductionOpenIso, Iso.trans_hom,
        Functor.mapIso_hom, sfReductionFiniteTriangle, Triangle.mk_mor₁,
        Iso.app_hom, F, R, Category.assoc])
  · have hu := congrArg F.map ((R.directAdjunction i).unit K)
    change F.map ((sixFunctorIntegralReduction D C E m X).map
        ((S.higher.integral.pullDirectAdjunction i).unit.app K)) ≫
      F.map ((R.directAdjunction i).right.hom.app
        ((S.higher.integral.pull i).obj K)) ≫
      F.map ((T.direct i).map ((R.directAdjunction i).left.hom.app K)) =
      F.map ((T.pullDirectAdjunction i).unit.app
        ((sixFunctorIntegralReduction D C E m X).obj K))
    simpa only [Functor.map_comp, Category.assoc, sfRecollementReductionClosedIso,
      Iso.trans_hom, Functor.mapIso_hom, sfReductionIntegralTriangle,
      sfReductionFiniteTriangle, Triangle.mk_mor₂, Iso.app_hom, F, R, T] using hu

private theorem sfReduction_distinguished (m : ℕ)
    (T : Triangle (DerivedCategory (scalarReductionSource.{u, u} C.l E X.obj.left)))
    (hT : T ∈ distTriang _) :
    sfRecollementReducedTriangle (C := C) (E := E) (X := X) m T ∈ distTriang _ := by
  let φ := PurCompactSupport.projection C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left
  have := pbcDerivedExtension_universal φ
  let : HasSheafify (ProEt.topology X.obj.left) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} X.obj.left
  let : (ProEt.topology X.obj.left).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} X.obj.left
  let : EssentiallySmall.{u + 1} X.obj.left.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨σ, _, huniq, _, htri⟩ :=
    SheafOfModules.derivedScalarExtension_counitShift.{u + 1, u, u + 1, u + 2, u + 2}
      φ (pbcExtend φ)
      (pbcExtensionExistence φ).choose_spec.choose
      (pbcExtensionExistence φ).choose_spec.choose_spec.choose
      (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  have : NatTrans.CommShift (pbcExtensionCounit φ) ℤ :=
    (PurCompactSupport.scalarCommShift_existsUnique φ).exists.choose_spec
  have he : (pbcDerivedExtend φ).commShiftIso (1 : ℤ) = σ := by
    apply huniq
    intro P
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm (pbcExtensionCounit φ) (1 : ℤ) P
  have : (pbcDerivedExtend φ).IsTriangulated := by
    constructor
    intro Δ hΔ
    simpa only [Functor.mapTriangle_obj, he] using htri Δ hΔ
  let e := PurCompactSupport.finiteReductionIso C.l E X.obj.left m
  let := Functor.CommShift.ofIso e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  have : (scalarReductionDerivedExtension.{u, u} C.l E X.obj.left m).IsTriangulated :=
    Functor.isTriangulated_of_iso e
  exact (scalarReductionDerivedExtension.{u, u} C.l E X.obj.left m).map_distinguished T hT

private theorem sfReduction_finite_orthogonality
    [IsSeparated X.obj.hom] [IsClosedImmersion i.hom.left]
    (hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ)
    (m : ℕ) (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    Subsingleton (((sfReductionFiniteOpen S j hj m).obj K)⟦(1 : ℤ)⟧ ⟶
      (sfReductionFiniteClosed S i m).obj K) := by
  let := hj
  let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) := ‹IsSeparated X.obj.hom›
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.succ_pos m)
  let T := S.integralNormalization.finiteLevels m
  let Kn := (sixFunctorIntegralReduction D C E m X).obj K
  let a := (T.finiteOpenExtension j hj).app ((T.finite.pull j).obj Kn) ≪≫
    (sfIntrinsicDerivedOpen A j.hom.left).mapIso ((T.finitePullback j).app Kn)
  let b := (T.finiteDirectImage i).app ((T.finite.pull i).obj Kn) ≪≫
    (proEtaleConstantDerivedDirectImage i.hom.left A).mapIso ((T.finitePullback i).app Kn)
  have ho := ((sfOpenClosedTriangle_finite C.l E D.k (by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    let : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ C.different
        ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : C.l.Prime)).1 h).symm))
      i.hom.left j.hom.left hij (m + 1) (Nat.succ_pos m)).1
      Kn.obj Kn.property).2.2.2 (1 : ℤ)
  let e := Iso.homCongr ((shiftFunctor _ (1 : ℤ)).mapIso a) b
  exact ⟨fun f g ↦ e.injective (@Subsingleton.elim _ ho (e f) (e g))⟩

/-- Reduction identifies the entire distinguished recollement triangle, including its
connecting arrow, through the specified operation comparisons. The identity middle
component is on the actual derived reduction. Neither stratum is required nonempty.

Source: current blueprint, prop-functor-package.proof.md, clause (3)
(blueprint: lem-sf-recollement-reduction-boundary).
Proof:
1. The counit-normalized derived scalar-extension theorem gives preservation of
triangles with its unique compatible shift. Transport along `finiteReductionIso`
to obtain distinguishedness for exactly the shift used in the reduced triangle.
2. The datum's adjunction comparisons preserve the open counit and closed unit.
Applying the finite ambient inclusion gives the first two squares.
3. Finite all-stages recollement gives shifted orthogonality for the canonical
finite vertices. Transport through the datum's finite operation normalization
isomorphisms, and through the shifted open reduction comparison.
4. BBD triangle-morphism extension supplies the third square for the prescribed
outer maps and identity middle map. Package their isomorphisms by `Triangle.isoMk`;
unfolding the third square gives the displayed boundary equation.
5. The naturality theorem below follows from naturality of the two comparison
factors. No step assumes that either stratum is nonempty. -/
theorem sfRecollementReductionBoundary
    [IsSeparated X.obj.hom] [IsClosedImmersion i.hom.left]
    (_hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ)
    (m : ℕ) (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (δ : (sfReductionIntegralClosed S i).obj K ⟶
      ((sfReductionIntegralOpen S j hj).obj K)⟦(1 : ℤ)⟧)
    (_hδ : sfReductionIntegralTriangle S i j hj K δ ∈ distTriang _)
    (δn : (sfReductionFiniteClosed S i m).obj K ⟶
      ((sfReductionFiniteOpen S j hj m).obj K)⟦(1 : ℤ)⟧)
    (_hδn : sfReductionFiniteTriangle S i j hj m K δn ∈ distTriang _) :
    (∃ e : sfRecollementReducedTriangle (C := C) (E := E) (X := X) m
          (sfReductionIntegralTriangle S i j hj K δ) ≅
        sfReductionFiniteTriangle S i j hj m K δn,
      e.hom.hom₁ = (sfRecollementReductionOpenIso S j hj m K).hom ∧
      e.hom.hom₂ = 𝟙 _ ∧
      e.hom.hom₃ = (sfRecollementReductionClosedIso S i m K).hom) ∧
    (scalarReductionDerivedExtension C.l E X.obj.left m).map δ ≫
        (Functor.commShiftIso (scalarReductionDerivedExtension C.l E X.obj.left m)
          (self := Functor.CommShift.ofIso
            (PurCompactSupport.finiteReductionIso C.l E X.obj.left m) ℤ) (1 : ℤ)).hom.app
              ((sfReductionIntegralOpen S j hj).obj K) ≫
        (shiftFunctor _ (1 : ℤ)).map (sfRecollementReductionOpenIso S j hj m K).hom =
      (sfRecollementReductionClosedIso S i m K).hom ≫ δn := by
  let a := sfRecollementReductionOpenIso S j hj m K
  let b := sfRecollementReductionClosedIso S i m K
  let T := sfRecollementReducedTriangle (C := C) (E := E) (X := X) m
    (sfReductionIntegralTriangle S i j hj K δ)
  let Tn := sfReductionFiniteTriangle S i j hj m K δn
  have hT : T ∈ distTriang _ := sfReduction_distinguished m _ _hδ
  have hs := sfReduction_counit_unit S i j hj m K δ δn
  have hc₁ : a.hom ≫ Tn.mor₁ = T.mor₁ ≫ 𝟙 Tn.obj₂ := by
    exact hs.1.symm.trans (Category.comp_id _).symm
  have hc₂ : T.mor₂ ≫ b.hom = 𝟙 Tn.obj₂ ≫ Tn.mor₂ := by
    simpa only [b, Tn, T, sfRecollementReducedTriangle, Functor.mapTriangle,
      Triangle.mk_mor₂, Category.id_comp] using hs.2
  have ho := sfReduction_finite_orthogonality S i j hj _hij m K
  let e := Iso.homCongr ((shiftFunctor _ (1 : ℤ)).mapIso a) (Iso.refl Tn.obj₃)
  have ho' : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ Tn.obj₃) :=
    ⟨fun f g ↦ e.injective (@Subsingleton.elim _ ho (e f) (e g))⟩
  obtain ⟨_, _, _, _, hc₃⟩ :=
    ((triangle_morphism_extension T Tn hT _hδn (𝟙 _)).2.1 ho').2.2
      a.hom b.hom hc₁ hc₂
  refine ⟨⟨Triangle.isoMk T Tn a (Iso.refl _) b hc₁.symm hc₂ hc₃,
    rfl, rfl, rfl⟩, ?_⟩
  simpa only [T, Tn, a, b, sfRecollementReducedTriangle, Functor.mapTriangle,
    sfReductionIntegralTriangle, sfReductionFiniteTriangle, sfReductionIntegralOpen,
    sfReductionIntegralClosed, sfReductionFiniteOpen, sfReductionFiniteClosed,
    Triangle.mk, Functor.comp_obj, Category.assoc]
    using hc₃

/-- Naturality of the three components of the recollement reduction isomorphism.
The middle component is identity; these are exactly the other two naturality squares.
Together with uniqueness and functoriality of the prescribed triangles, they express
naturality of the whole triangle comparison for any chosen distinguished completions.
Source: package clause (3) (blueprint: lem-sf-recollement-reduction-boundary).
Proof: each comparison is the composite of the open/direct-image reduction
comparison and that operation applied to the pullback reduction comparison.
Naturality of the two factors and functoriality of reduction give both squares.
The componentwise composition law for triangle morphisms then gives naturality
of the triangle isomorphism. This is step 5 of the node's proof. -/
theorem sfRecollementReductionBoundary_naturality (m : ℕ)
    (K L : sfIntegralConstructibleCategory C.l E X.obj.left) (f : K ⟶ L) :
    ((scalarReductionDerivedExtension C.l E X.obj.left m).map
        ((sfReductionIntegralOpen S j hj).map f) ≫
        (sfRecollementReductionOpenIso S j hj m L).hom =
      (sfRecollementReductionOpenIso S j hj m K).hom ≫
        (sfReductionFiniteOpen S j hj m).map f) ∧
    ((scalarReductionDerivedExtension C.l E X.obj.left m).map
        ((sfReductionIntegralClosed S i).map f) ≫
        (sfRecollementReductionClosedIso S i m L).hom =
      (sfRecollementReductionClosedIso S i m K).hom ≫
        (sfReductionFiniteClosed S i m).map f) := by
  let R := S.integralNormalization.reduction m
  let T := (S.integralNormalization.finiteLevels m).finite
  let F : sixFunctorFiniteCategory D C E (m + 1) (Nat.succ_pos m) X ⥤
      proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (m + 1)) :=
    (intrinsicFiniteTorsionConstructible C.l E (m + 1) (Nat.succ_pos m) X.obj.left).ι
  let a : sfReductionIntegralOpen S j hj ⋙
        scalarReductionDerivedExtension C.l E X.obj.left m ≅ sfReductionFiniteOpen S j hj m :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (S.higher.integral.pull j) (R.openExtension j hj)) F ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (R.directAdjunction j).left (T.openExtension j hj)) F
  let b : sfReductionIntegralClosed S i ⋙
        scalarReductionDerivedExtension C.l E X.obj.left m ≅ sfReductionFiniteClosed S i m :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (S.higher.integral.pull i) (R.directAdjunction i).right) F ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (R.directAdjunction i).left (T.direct i)) F
  exact ⟨a.hom.naturality f, b.hom.naturality f⟩

end WeilConjectures
