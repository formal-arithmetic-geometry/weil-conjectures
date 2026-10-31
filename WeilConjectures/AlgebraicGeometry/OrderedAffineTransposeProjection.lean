/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurityComparison
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import WeilConjectures.AlgebraicGeometry.OrderedAffineTransposeData
import WeilConjectures.AlgebraicGeometry.OrderedAffineComparisonNaturality
import WeilConjectures.AlgebraicGeometry.OrderedAffineTransposeSuccessor
import WeilConjectures.AlgebraicGeometry.OrderedAffineLineTransposeNormalization

/-! # Projection and pasted-counit formulas for ordered affine purity

Source: current blueprint sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof.md, Steps 2--4, and the DAG's expanded
pasted-counit and coefficient-extraction argument
(blueprint: lem-pur-ordered-affine-transpose-projection).

All objects and maps use the published ordered comparison, the ordinary finite-coefficient
pro-etale derived category, and the bounded-below etale-origin exceptional adjunction.
Zero-dimensional operations are normalized identities, as in the comparison definition.
`BlockLaw` expands the inverse-conjugate transpose through its defining pasted counit;
thus its equation lives directly on Rg_! Rf_! F_f F_g K. It does not identify different
coordinate orders. The source of `integration` is transported from F_d(A_Y) to T_d by
canonical pullback of the coefficient unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrderedAffineTranspose
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

section ZeroCalculations

private theorem transpose_zero
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    HEq (transpose P Y aY K Ke hKe eK 0) (𝟙 K.obj) := by
  unfold transpose compact affineSpacePurityComparison orderedRec comparisonZero
    counit orderedSource exceptional
  dsimp +instances only [iteratedAffineLine, Functor.id, id]
  simp only [Category.id_comp, heq_self_iff_true]

private theorem integration_zero
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] :
    HEq (integration P Y aY 0) (𝟙 (unit (Ring P) Y)) := by
  unfold integration
  with_unfolding_all
    change HEq (𝟙 (unit (Ring P) Y) ≫
      transpose P Y aY (unitPlus (Ring P) Y) _ _ _ 0) (𝟙 (unit (Ring P) Y))
    exact (heq_of_eq (Category.id_comp _)).trans
      (transpose_zero P Y aY _ _ _ _)

private theorem counit_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) [CompactSpace Y]
    (K L : Plus (Ring P) Y) (v : K.obj ⟶ L.obj) (d : ℕ) :
    (compact P Y d).map ((exceptional P Y d).map v) ≫ counit P Y L d =
      counit P Y K d ≫ v := by
  cases d with
  | zero =>
    unfold compact exceptional counit
    dsimp +instances only [iteratedAffineLine, Functor.id, id]
    simp only [Category.id_comp, Category.comp_id]
  | succ d =>
    let := (projection_geometry Y (d + 1)).2
    unfold compact exceptional counit
    exact rightDerivedUpperShriekCounit_naturality
      (iteratedAffineLineProj Y (d + 1)) K.property L.property v

end ZeroCalculations

attribute [local irreducible] affineSpacePurityComparison stageEtale stageComparison

private theorem transpose_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj)
    (L : Plus (Ring P) Y) (Le : Etale.DerivedCategoryModule (Ring P) Y)
    (hLe : etaleFiniteTor (Ring P) Y Le)
    (eL : (comparison (Ring P) Y).obj Le ≅ L.obj) (v : K.obj ⟶ L.obj) (d : ℕ) :
    (compact P Y d).map ((orderedSource P Y d).map v) ≫
        transpose P Y aY L Le hLe eL d =
      transpose P Y aY K Ke hKe eK d ≫ v := by
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have hn := orderedAffineComparison_natural P Y aY K Ke hKe eK L Le hLe eL v d
  have hc := counit_natural P Y K L v d
  unfold transpose
  calc
    _ = (compact P Y d).map
        ((orderedSource P Y d).map v ≫ affineSpacePurityComparison P Y aY L Le hLe eL d) ≫
        counit P Y L d := by rw [Functor.map_comp, Category.assoc]
    _ = (compact P Y d).map
        (affineSpacePurityComparison P Y aY K Ke hKe eK d ≫ (exceptional P Y d).map v) ≫
        counit P Y L d := congrArg (fun t ↦ (compact P Y d).map t ≫ counit P Y L d) hn
    _ = (compact P Y d).map (affineSpacePurityComparison P Y aY K Ke hKe eK d) ≫
        ((compact P Y d).map ((exceptional P Y d).map v) ≫ counit P Y L d) :=
      (congrArg (fun t ↦ t ≫ counit P Y L d) ((compact P Y d).map_comp _ _)).trans
        (Category.assoc _ _ _)
    _ = (compact P Y d).map (affineSpacePurityComparison P Y aY K Ke hKe eK d) ≫
        (counit P Y K d ≫ v) :=
      congrArg (fun t ↦
        (compact P Y d).map (affineSpacePurityComparison P Y aY K Ke hKe eK d) ≫ t) hc
    _ = _ := (Category.assoc _ _ _).symm

private theorem block_law
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (a b : ℕ) :
    BlockLaw P Y aY K Ke hKe eK a b := by
  unfold BlockLaw
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : LocallyOfFiniteType (towerBase aY b) := (tower_geometry aY b).1
  let : QuasiCompact (towerBase aY b) := (tower_geometry aY b).2.1
  let : IsSeparated (towerBase aY b) := (tower_geometry aY b).2.2
  let : IsNoetherian (iteratedAffineLine Y b) := tower_noetherian P Y aY b
  intro B hB Be hBe eB
  let L : Plus (Ring P) (iteratedAffineLine Y b) :=
    ⟨_, (stage_applicability P Y aY K Ke hKe eK b).1⟩
  let v : B.obj ⟶ L.obj :=
    eqToHom hB ≫ affineSpacePurityComparison P Y aY K Ke hKe eK b
  have hn := transpose_natural P (iteratedAffineLine Y b) (towerBase aY b)
    B Be hBe eB L (stageEtale P Y K.obj Ke b)
    (stage_applicability P Y aY K Ke hKe eK b).2
    (stageComparison P Y K.obj Ke eK b) v a
  have hn' : (compact P (iteratedAffineLine Y b) a).map
      ((orderedSource P (iteratedAffineLine Y b) a).map v ≫
        affineSpacePurityComparison P (iteratedAffineLine Y b) (towerBase aY b)
          L (stageEtale P Y K.obj Ke b)
          (stage_applicability P Y aY K Ke hKe eK b).2
          (stageComparison P Y K.obj Ke eK b) a) ≫
      counit P (iteratedAffineLine Y b) L a =
        transpose P (iteratedAffineLine Y b) (towerBase aY b) B Be hBe eB a ≫ v := by
    simpa only [transpose, Functor.map_comp, Category.assoc] using hn
  change (compact P Y b).map _ ≫ counit P Y K b = _
  rw [hn']
  simp only [v, Functor.map_comp, Category.assoc, transpose]

section Assembly

/-- Projection formula for the actual ordered transpose, its zero/line normalizations,
and the consecutive-block pasted-counit equation.
Source: current blueprint sec-smooth-purity/sk-prop-sp-composition, ordered-composite proof
Steps 2--4; DAG expanded Steps 1--6
(blueprint: lem-pur-ordered-affine-transpose-projection).

Proof:
1. Polynomial projections and all tower bases are separated and finite type. The Tate
lines are locally free of rank one. PullbackTorAmplitude and FiniteCoefficientTensorCtf
put F_d K in the finite-Tor constructible class; SfPreservationClass and
ProEtaleConstructibleOrigin supply bounded etale origins for all exceptional inputs.
FiniteCompactSupportConstructibility supplies the compact-support bounds.
FiniteCompactProjectionFormula makes each specified projection component invertible.
2. Naturality of the line comparison, and induction, give naturality of Gamma_f.
For u=Gamma_g,K, rewrite Gamma_f,Rg!K F_f(u) as Rf!(u) Gamma_f,F_gK.
The definition of compositionInverse transposes through the pasted counit. Counit
naturality and functoriality give precisely BlockLaw, including identity blocks.
This uses mate pasting, adjunction conjugation and the adjunct-counit identity.
3. ProjectionFormulaCoefficientCoherence supplies the unit law and two-coefficient
associativity for the two-symmetry inverse projection. CompositionProjectionMate and
ProjectionCompatibleTriangleAssembly supply the composition law for exactly the chosen
canonical compositor; CompatibleCompactificationTriangle supplies its geometric domain.
All these identities apply on the constructible inputs checked in Step 1.
4. At zero the comparison and adjunction are identities. At one, transposing the actual
line comparison recovers its defining augmentation, by the adjunct-counit identity.
The projection unit law identifies its value at A with normalized line integration.
5. Induct on d over every finite-type base. For the successor f=q_d,g=p_d use Step 2,
insert the line formula and the induction hypothesis, then use coefficient associativity
and projection naturality to move 1 tensor I_f through the projection for g.
The composition projection law gives tau_(d+1),K = (1 tensor J) Pi_(d+1),K,
where J=I_g Rg_!((1 tensor I_f) pi_f,T_g,T_f), in the specified source coordinates.
6. Evaluate this equation at A. The projection unit law identifies J with I_(d+1).
This proves the coefficient formula; Steps 2 and 4 give the remaining conjuncts.
No coordinate permutation or general ambient pro-etale adjoint is invoked.
-/
theorem orderedAffineTranspose_projection
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    (∀ d : ℕ, ∃ h : IsIso (projection P Y K.obj d),
      transpose P Y aY K Ke hKe eK d = projectionInverse P Y K.obj d h ≫
        ((tensor (Ring P) Y).obj K.obj).map (integration P Y aY d) ≫
          (moduleRightUnit (Ring P) Y K.obj).hom) ∧
    HEq (integration P Y aY 0) (𝟙 (unit (Ring P) Y)) ∧
    integration P Y aY 1 = lineNormalizedIntegration P Y aY ∧
    ∀ a b : ℕ, BlockLaw P Y aY K Ke hKe eK a b := by
  have coefficient : ∀ (d : ℕ) (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of P.field.k))
      [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
      (M : Plus (Ring P) Z) (Me : Etale.DerivedCategoryModule (Ring P) Z)
      (hMe : etaleFiniteTor (Ring P) Z Me)
      (eM : (comparison (Ring P) Z).obj Me ≅ M.obj),
      ∃ h : IsIso (projection P Z M.obj d),
        transpose P Z aZ M Me hMe eM d = projectionInverse P Z M.obj d h ≫
          ((tensor (Ring P) Z).obj M.obj).map (integration P Z aZ d) ≫
            (moduleRightUnit (Ring P) Z M.obj).hom := by
    intro d
    induction d with
    | zero =>
      intro Z aZ _ _ _ M Me hMe eM
      have hp : IsIso (projection P Z M.obj 0) := by
        with_unfolding_all exact (moduleRightUnit (Ring P) Z M.obj).isIso_hom
      refine ⟨hp, ?_⟩
      with_unfolding_all
        have hi : integration P Z aZ 0 = 𝟙 (unit (Ring P) Z) :=
          eq_of_heq (integration_zero P Z aZ)
        have ht : transpose P Z aZ M Me hMe eM 0 = 𝟙 M.obj :=
          eq_of_heq (transpose_zero P Z aZ M Me hMe eM)
        let e := moduleRightUnit (Ring P) Z M.obj
        let := e.isIso_hom
        have hmap := ((tensor (Ring P) Z).obj M.obj).map_id (unit (Ring P) Z)
        have htrace := congrArg (fun t ↦ ((tensor (Ring P) Z).obj M.obj).map t) hi
        have hcomp := congrArg (fun t ↦ inv e.hom ≫ t ≫ e.hom) (htrace.trans hmap)
        exact ht.trans ((IsIso.inv_hom_id e.hom).symm.trans
          ((congrArg (fun t ↦ inv e.hom ≫ t) (Category.id_comp e.hom)).symm.trans
            hcomp.symm))
    | succ d ih => exact orderedAffineTranspose_successor P d ih
  exact ⟨fun d ↦ coefficient d Y aY K Ke hKe eK, integration_zero P Y aY,
    orderedAffineTranspose_line P Y aY, block_law P Y aY K Ke hKe eK⟩

end Assembly

end AlgebraicGeometry.ProEtale.OrderedAffineTranspose
