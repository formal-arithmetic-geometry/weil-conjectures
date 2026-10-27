/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.TowerP1CoefficientCoordinates
public import Sheaf.Paper.TowerP1GeometricCoordinates
import Sheaf.Paper.OrderedTowerOrientation
import Sheaf.Paper.FiniteGammaEvaluationIsIso
import Sheaf.Paper.TowerNormalizationPreservation
import Sheaf.Paper.TwistedPullbackTowerDomain
import Sheaf.Paper.TowerTensorTransposeEvaluation

/-! # Tower orientation and smooth purity

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.md
(blueprint: det-sp-tower-gamma).

All natural indices are predecessors of positive exponents. The section-preserving
realization changes coordinates in the ordinary derived category of strict towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerGamma

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Smooth tower orientation, the actual natural purity isomorphism on all uniform
constructible finite-Tor towers, and preservation of normalized towers by both adjoints.
Finite-level indices are n+1, including the first coefficient quotient at n=0.
Source: latest blueprint tower-geometric gamma, clauses (1)--(3)
(blueprint: det-sp-tower-gamma).

Proof plan:
1. lem-sp-finite-orientation-reduction supplies the diagonal orientations with their
actual quotient compatibility. det-sp-scalar-extension-functor gives invertible Tate
reductions. lem-sp-strict-line-heart-assembly assembles their strict-heart isomorphism.
2. lem-sp-twisted-pullback-tower-domain gives common cohomological and Tor intervals for
both tensor sources and invertibility of the specified projection map. Apply
lem-sp-tower-tensor-transpose-evaluation to the actual transpose defined above. It gives
naturality and the finite purity equations with the fixed unit, root, tensor and site
comparisons. The coefficient-unit equation identifies the orientation itself.
3. thm-pur-finite-coefficient-smooth-purity makes every evaluation of gamma invertible.
Conservativity in det-sp-tower-shriek-levels makes gamma invertible in the ordinary tower
derived category. Both endpoints belong to its full uniform constructible subcategory;
normalization of the input is not used.
4. lem-sp-compact-support-tower-reduction factors each output reduction through the
input reduction and det-sp-reduction-direct-image. Each factor is invertible on a
normalized input, proving preservation by compact support.
5. lem-sp-purity-conjugates-tower-reduction conjugates exceptional reduction by finite
gamma to pullback of input reduction, with the positive twist and even shift. Its
factors are invertible on normalized input; the uniform output bounds are already
supplied by gluing. This proves preservation by the exceptional adjoint. -/
theorem tower_gamma (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj) :
    Nonempty (Purity l E b o q j p d w hF G adj lv) := by
  classical
  let : SpTowerShriek.Base l E := b
  let orient := Classical.choice
    (ordered_tower_orientation l E b o q D hne j p d w hF G adj lv)
  let hU := orient.unit_mem
  let tx := orient.tensorX
  let ty := orient.tensorY
  let roots := orient.roots
  let ux := orient.unitsX
  let uy := orient.unitsY
  let cx := orient.coefficientsX
  let cy := orient.coefficientsY
  let tc := orient.tensors
  let gc := orient.geometry
  let a := orient.orientation
  let ha := orient.diagonal_levels
  let f : Over.mk (X ↘ Spec (.of D.k)) ⟶ Over.mk (Y ↘ Spec (.of D.k)) :=
    Over.homMk (j ≫ p) (by change (j ≫ p) ≫ (Y ↘ Spec (.of D.k)) = _; simp)
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (X ↘ Spec (.of D.k))
    infer_instance
  have : IsSeparated (Over.mk (X ↘ Spec (.of D.k))).hom := by
    change IsSeparated (X ↘ Spec (.of D.k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of D.k))
    infer_instance
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change QuasiCompact (Y ↘ Spec (.of D.k))
    infer_instance
  have : IsSeparated (Over.mk (Y ↘ Spec (.of D.k))).hom := by
    change IsSeparated (Y ↘ Spec (.of D.k))
    infer_instance
  have : IsSeparated f.left := by
    change IsSeparated (j ≫ p)
    infer_instance
  have : SmoothOfRelativeDimension d f.left := by
    change SmoothOfRelativeDimension d (j ≫ p)
    infer_instance
  have domain (K : SpTowerCalculus.C l E b q Y) :
      ∃ r s : ℤ, SpTwistedTowerDomain.Conclusion l E b o q D
        (Over.mk (X ↘ Spec (.of D.k))) (Over.mk (Y ↘ Spec (.of D.k))) f
        (factorization j p) d w G hU K r s a := by
    obtain ⟨r, s, t, z, hrs, htz, hb⟩ := K.property.2
    refine ⟨t, z, SpTwistedTowerDomain.twisted_pullback_tower_domain
      l E b o q D _ _ f (factorization j p) d w hF G adj lv hU hne
      roots ux cx tc uy cy a ha K t z htz ?_⟩
    intro n
    have ht := (hb n).2
    refine ⟨ht.1, ?_⟩
    intro L P hL v hv hP M i hi
    apply ht.2 L P _ v hv hP M i hi
    obtain ⟨e⟩ := hL
    exact ⟨e ≪≫ (SpTowerCalculus.levelComparison l E b q Y n).app K.obj⟩
  have hQ (K : SpTowerCalculus.C l E b q Y) :
      spConstructibleTorTowers l E X (q.abelian X)
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
          ((tensorSource l E b o q (j ≫ p)
            ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)).obj K)) :=
    (domain K).choose_spec.choose_spec.Q_mem
  have hpf (K : SpTowerCalculus.C l E b q Y) :
      IsIso (SpTowerShriek.projection l E b o (factorization j p)
        ((exceptional l E b q G).obj ⟨originalUnit l E b q Y, hU⟩)
        ((realization l E b q Y).obj K)) :=
    (domain K).choose_spec.choose_spec.projection_iso
  have hP (K : SpTowerCalculus.C l E b q Y) :
      spConstructibleTorTowers l E X (q.abelian X)
        ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
          ((source l E b o q (j ≫ p) w d).obj K)) :=
    (domain K).choose_spec.choose_spec.P_mem
  have evdata (n : ℕ) := ha n
  have nat_and_levels (n : ℕ) :
      (∀ (K L : SpTowerCalculus.C l E b q Y) (v : K ⟶ L),
        (source l E b o q (j ≫ p) w d).map v ≫
            gamma l E b o q (factorization j p) w d tx ty hF G adj hU a L (hQ L) (hpf L) =
          gamma l E b o q (factorization j p) w d tx ty hF G adj hU a K (hQ K) (hpf K) ≫
            (exceptional l E b q G).map v) ∧
      (∀ K : SpTowerCalculus.C l E b q Y,
        IsIso ((SpTowerShriek.Ev l E X n).map
          (gamma l E b o q (factorization j p) w d tx ty hF G adj hU a K
            (hQ K) (hpf K)))) := by
    obtain ⟨dg, alpha, halpha, ui, hui, hwa⟩ := evdata n
    have he := SpTensorTranspose.tensor_transpose_evaluation l E b o q j p hF G adj lv
      hU tx ty n ui (tc n) (gc n) w d roots (ux n) (uy n) (cx n) (cy n) a hQ hpf
      D hne dg alpha halpha hui hwa
    refine ⟨he.2.2.1, ?_⟩
    intro K
    have hw := (he.2.2.2 K).choose_spec.2.2
    have := hw.1
    have := hw.2.1
    have hi : IsIso ((SpTowerP1.nu l E n X).map
        (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
          (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
            (SpTowerP1.levelAnnihilates l E n) X d) alpha
          ((lv.realization n).origin.obj ((SpTowerGluing.level l E b q Y n).obj K)) ≫
          (finiteRightComparison (SpTowerShriek.R l E n) j p
            (lv.finite_closed n) (lv.right n) (lv.adjunction n)
            (lv.realization n)).inv.app _)) := by
      exact finite_gamma_evaluation_isIso l E b o q D hne j p d hF G adj lv
        n dg alpha (ux n) halpha K
    have hiWord : IsIso ((SpTowerP1.nu l E n X).map
        (Etale.FiniteSmoothPurity.gamma (SpTowerP1.levelRing l E n) (j ≫ p)
          (Etale.FiniteSmoothPurity.line (SpTowerP1.levelRing l E n) (l ^ (n + 1))
            (SpTowerP1.levelAnnihilates l E n) X d) alpha
          (inputWord l E b o q (factorization j p) hF G adj lv n K).etale ≫
          (finiteRightComparison (SpTowerShriek.R l E n) j p
            (lv.finite_closed n) (lv.right n) (lv.adjunction n)
            (lv.realization n)).inv.app _)) := hi
    have hic := (congrArg (fun z ↦ IsIso z) hw.2.2).mpr
      (IsIso.comp_isIso' hiWord hw.2.1)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hw.1 hic
  have hnat := nat_and_levels
  have norm := tower_normalization_preservation l E b o q D hne j p d w hF G adj lv
    roots ux cx tc gc
  refine ⟨{
    unit_mem := hU, tensorX := tx, tensorY := ty, roots := roots,
    unitsX := ux, unitsY := uy, coefficientsX := cx, coefficientsY := cy,
    tensors := tc, geometry := gc, orientation := a, tensor_mem := hQ,
    projection_iso := hpf, source_mem := hP, purity_iso := ?_,
    naturality := (hnat 0).1, support_normalized := norm.1,
    exceptional_normalized := norm.2, finite_levels := ?_ }⟩
  · intro K
    exact (b.calculus X).detects _ (fun n ↦ (hnat n).2 K)
  · intro n
    obtain ⟨dg, alpha, halpha, ui, hui, hwa⟩ := evdata n
    refine ⟨dg, alpha, halpha, ui, hui, hwa, ?_⟩
    have he := SpTensorTranspose.tensor_transpose_evaluation l E b o q j p hF G adj lv
      hU tx ty n ui (tc n) (gc n) w d roots (ux n) (uy n) (cx n) (cy n) a hQ hpf
      D hne dg alpha halpha hui hwa
    intro K
    exact (he.2.2.2 K).choose_spec.2.2

end AlgebraicGeometry.ProEtale.SpTowerGamma

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
