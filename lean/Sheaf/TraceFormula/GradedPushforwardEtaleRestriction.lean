/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.TraceFormula.EtalePowerProductNormalization
public import Sheaf.TraceFormula.EtaleGradedModuleAlgebra
public import Sheaf.TraceFormula.EtaleModuleEvaluationTensorPowers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.TraceFormula.CanonicalEtaleLinePowerAlgebra
import Sheaf.TraceFormula.EtaleLinePowerComparison

/-!
# Étale restriction of graded direct images and their evaluation

Source: Stacks Project, spaces-properties.tex, Tag 03LX and its tensor-pullback footnote;
spaces-descent.tex, Tag 0D3C, the maps psi_d and psi; sites-modules.tex, Tag 03EL
(blueprint: lem-trf-graded-pushforward-etale-restriction).

The comparisons are fixed on every compatible chart projection. Total objects are
colimit cofans in module sheaves, and evaluation is the descent of the actual counits.
Étale tensor pullbacks are written in their restriction presentation, via the normalized
isomorphism `moduleTensorPullback_etale_restriction`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/-- Restriction of the homogeneous products and unit on unchanged chart schemes.
These equations determine the restricted algebra structure, without selecting it from
an unconstrained existence statement.
Source: Stacks, Tags 03LX and 0D3C
(blueprint: lem-trf-graded-pushforward-etale-restriction). -/
def IsGradedEtaleRestriction (h : X' ⟶ X) (hh : IsEtale h.hom.hom)
    {B : ℕ → X.Modules} (A : EtaleGradedModuleAlgebra B)
    (A' : EtaleGradedModuleAlgebra (fun d ↦ (pullback h hh).obj (B d))) : Prop :=
  (∀ (m n : ℕ) (V : X'.EtaleSite)
    (s : ((pullback h hh).obj (B m)).val.obj (op V))
    (t : ((pullback h hh).obj (B n)).val.obj (op V)),
    A'.mul m n V s t = A.mul m n ((etaleMap h hh).obj V) s t) ∧
  (∀ (V : X'.EtaleSite) (a : X'.structureSheaf.obj.obj (op V)),
    A'.unit.val.app (op V) a = A.unit.val.app (op ((etaleMap h hh).obj V)) a)

/-- The products of compatible sections, including the scalar-valued unit.
Every projection is retained; hence this specifies the homogeneous operations uniquely.
Source: Stacks, Tags 03LX and 0D3C
(blueprint: lem-trf-graded-pushforward-etale-restriction). -/
def HasChartwiseGradedDirectImage (f : X ⟶ Y) {B : ℕ → X.Modules}
    (A : EtaleGradedModuleAlgebra B)
    (C : EtaleGradedModuleAlgebra (fun d ↦ (moduleDirectImage f).obj (B d))) : Prop :=
  (∀ (m n : ℕ) (V : Y.EtaleSite) (q : ModuleChart f V)
    (s : ((moduleDirectImage f).obj (B m)).val.obj (op V))
    (t : ((moduleDirectImage f).obj (B n)).val.obj (op V)),
    ((moduleDirectImageModel f).projection (B (m + n)) V).app (op q)
        (C.mul m n V s t) =
      A.mul m n q.left
        (((moduleDirectImageModel f).projection (B m) V).app (op q) s)
        (((moduleDirectImageModel f).projection (B n) V).app (op q) t)) ∧
  (∀ (V : Y.EtaleSite) (q : ModuleChart f V) (a : Y.structureSheaf.obj.obj (op V)),
    ((moduleDirectImageModel f).projection (B 0) V).app (op q)
        (C.unit.val.app (op V) a) =
      A.unit.val.app (op q.left) (moduleChartScalar f V q a))

/-- Restrict a cofan with its actual homogeneous inclusions.
Source: Stacks, Tags 0038 and 0D3C
(blueprint: lem-trf-graded-pushforward-etale-restriction). -/
def gradedEtaleCofan (h : X' ⟶ X) (hh : IsEtale h.hom.hom)
    (B : ℕ → X.Modules) (b : Cofan B) :
    Cofan (fun d ↦ (pullback h hh).obj (B d)) :=
  Cofan.mk ((pullback h hh).obj b.pt) (fun d ↦ (pullback h hh).map (b.inj d))

/-- All normalized comparisons in the graded étale base-change assertion. The algebra
homomorphism has invertible homogeneous components; its sum is the displayed total iso.
The two evaluations below are definitions from the adjunction counits, rather than
additional maps chosen to make the square commute.
Source: Stacks, Tags 03LX, 0D3C and 03EL
(blueprint: lem-trf-graded-pushforward-etale-restriction). -/
structure GradedPushforwardEtaleRestriction
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom)
    (B : ℕ → X.Modules) (A : EtaleGradedModuleAlgebra B) where
  hh : IsEtale h.hom.hom
  directAlgebra : EtaleGradedModuleAlgebra (fun d ↦ (moduleDirectImage f).obj (B d))
  directProducts : HasChartwiseGradedDirectImage f A directAlgebra
  restrictedAlgebra : EtaleGradedModuleAlgebra (fun d ↦ (pullback h hh).obj (B d))
  restrictedProducts : IsGradedEtaleRestriction h hh A restrictedAlgebra
  directAlgebra' : EtaleGradedModuleAlgebra
    (fun d ↦ (moduleDirectImage f').obj ((pullback h hh).obj (B d)))
  directProducts' : HasChartwiseGradedDirectImage f'
    restrictedAlgebra directAlgebra'
  beta (d : ℕ) : (pullback g hg).obj ((moduleDirectImage f).obj (B d)) ≅
    (moduleDirectImage f').obj ((pullback h hh).obj (B d))
  sections (d : ℕ) (V : Y'.EtaleSite) (q : ModuleChart f' V)
      (s : ((moduleDirectImage f).obj (B d)).val.obj (op ((etaleMap g hg).obj V))) :
    ((moduleDirectImageModel f').projection ((pullback h hh).obj (B d)) V).app (op q)
        ((beta d).hom.val.app (op V) s) =
      ((moduleDirectImageModel f).projection (B d) ((etaleMap g hg).obj V)).app
        (op (moduleChartBaseChange f g h f' hg hh hp.w V q)) s
  restrictedDirectAlgebra : EtaleGradedModuleAlgebra
    (fun d ↦ (pullback g hg).obj ((moduleDirectImage f).obj (B d)))
  restrictedDirectProducts : IsGradedEtaleRestriction g hg directAlgebra restrictedDirectAlgebra
  algebraHom : restrictedDirectAlgebra.Hom directAlgebra'
  algebraHom_degree (d : ℕ) : algebraHom.degree d = (beta d).hom
  lambda : moduleTensorPullback f ⋙ pullback h hh ≅
    pullback g hg ⋙ moduleTensorPullback f'
  lambda_tensor (M : Y.Modules) (V : Y'.EtaleSite) (q : ModuleChart f' V)
      (a b : X'.structureSheaf.obj.obj (op q.left))
      (s : M.val.obj (op ((etaleMap g hg).obj V))) :
    (lambda.hom.app M).val.app (op q.left)
        (a • moduleTensorSection f M ((etaleMap g hg).obj V)
          (moduleChartBaseChange f g h f' hg hh hp.w V q) b s) =
      moduleTensorSection f' ((pullback g hg).obj M) V q (a * b) s
  source : Cofan B
  source_colimit : IsColimit source
  target : Cofan (fun d ↦ (pullback h hh).obj (B d))
  target_colimit : IsColimit target
  direct : Cofan (fun d ↦ (moduleDirectImage f).obj (B d))
  direct_colimit : IsColimit direct
  direct' : Cofan (fun d ↦ (moduleDirectImage f').obj ((pullback h hh).obj (B d)))
  direct_colimit' : IsColimit direct'
  restriction_colimit : IsColimit (gradedEtaleCofan g hg _ direct)
  source_restriction_colimit : IsColimit (gradedEtaleCofan h hh _ source)
  evaluation_colimit : IsColimit (evaluationPullbackCofan f _ direct)
  evaluation_colimit' : IsColimit (evaluationPullbackCofan f' _ direct')
  total : (pullback g hg).obj direct.pt ≅ direct'.pt
  total_degree (d : ℕ) :
    (pullback g hg).map (direct.inj d) ≫ total.hom = (beta d).hom ≫ direct'.inj d
  sourceTotal : (pullback h hh).obj source.pt ≅ target.pt
  sourceTotal_degree (d : ℕ) :
    (pullback h hh).map (source.inj d) ≫ sourceTotal.hom = target.inj d
  evaluation :
    (pullback h hh).map (evaluationTotal f B direct source evaluation_colimit) ≫
        sourceTotal.hom =
      lambda.hom.app direct.pt ≫ (moduleTensorPullback f').map total.hom ≫
        evaluationTotal f' _ direct' target evaluation_colimit'
  counit_tensor (d : ℕ) (V : Y.EtaleSite) (q : ModuleChart f V)
      (a : X.structureSheaf.obj.obj (op q.left))
      (s : ((moduleDirectImage f).obj (B d)).val.obj (op V)) :
    (evaluationCounit f (B d)).val.app (op q.left)
        (moduleTensorSection f ((moduleDirectImage f).obj (B d)) V q a s) =
      a • @id ((B d).val.obj (op q.left))
        (((moduleDirectImageModel f).projection (B d) V).app (op q) s)
  counit_tensor' (d : ℕ) (V : Y'.EtaleSite) (q : ModuleChart f' V)
      (a : X'.structureSheaf.obj.obj (op q.left))
      (s : ((moduleDirectImage f').obj ((pullback h hh).obj (B d))).val.obj (op V)) :
    (evaluationCounit f' ((pullback h hh).obj (B d))).val.app (op q.left)
        (moduleTensorSection f'
          ((moduleDirectImage f').obj ((pullback h hh).obj (B d))) V q a s) =
      a • @id (((pullback h hh).obj (B d)).val.obj (op q.left))
        (((moduleDirectImageModel f').projection ((pullback h hh).obj (B d)) V).app (op q) s)

/-- Étale base change preserves arbitrary homogeneous direct images, their ordinary
commutative unital algebra structure, their coproducts, and their evaluation counits.
Source: Stacks, Tags 03LX (including its footnote), 0D3C and 03EL
(blueprint: lem-trf-graded-pushforward-etale-restriction).

Proof:
1. Apply lem-trf-space-etale-module-pushforward-restriction in each degree. Its chart
projection identity fixes beta by the identity on compatible sections, and its tensor
identity supplies lambda with the arbitrary-scalar normalization.
2. Apply lem-sfb-localized-site-tensor-restriction on scheme charts. The comparisons
agree on overlaps by lem-pc-sites-sheaf-tensor-bilinear-universal, since they keep pure
tensors unchanged. The unit comparison is multiplication, by
lem-trf-space-chart-adjunction-tensor-realization. Associativity and symmetry follow
from their identical formulas on triples and pairs of local sections.
3. Products and units of compatible families are componentwise. Their projections are
the formulas in directProducts and directProducts'. Beta keeps these projections, so
preserves all homogeneous products and the unit; uniqueness in the sheaf tensor
universal property gives algebraHom.
4. Tensor pullback is left adjoint, so lem-weil-pbc-left-adjoint-preserves-colimits gives
all four pulled coproduct cofans. The sum of beta and its degreewise inverse give total;
the same comparison for the original B gives sourceTotal. Homogeneous inclusions and
algebraHom say that total is an isomorphism of graded algebras.
5. For one degree, apply the chart projection to the adjunction unit and then counit.
Naturality and the triangle identity reduce the result to the original chart section.
Multiplication by any local scalar a gives a times that section. The tensor realization
identifies these generators with actual local tensors. Both base-change paths therefore
have that formula. Linearity and module sheafification uniqueness extend equality to
all sections; the coproduct universal property extends it to the displayed evaluation.
This uses no quasi-coherence or quasi-compactness assumption, or assertion that sections
of infinite coproducts are sums of global homogeneous sections. -/
theorem graded_pushforward_etale_restriction
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom)
    (B : ℕ → X.Modules) (A : EtaleGradedModuleAlgebra B) :
    Nonempty (GradedPushforwardEtaleRestriction f g h f' hg hp B A) := by
  sorry

/-- The line-module specialization uses the actual tensor powers of the restricted line
module. The product and unit normalizations, together with the first-power equation,
characterize the canonical tensor comparisons; the unit equation includes degree zero.
The base-change data specialize the preceding theorem to these powers, so their algebra
and evaluation comparisons transport along theta to the actual restricted powers.
Source: Stacks, Tags 03EL, 03LX and 0D3C
(blueprint: lem-trf-graded-pushforward-etale-restriction).

Proof:
6. Use the normalized structure-ring comparison in degree zero and the identity of the
restricted line module in degree one. Iterate the localized tensor comparison of
lem-sfb-localized-site-tensor-restriction to identify every higher tensor power.
On an affine chart its map keeps every factor and multiplies the scalar coefficients.
The inverse inserts 1, and balancing proves both inverse identities. The equivalence
with the small affine model preserves this tensor construction (039Z), giving theta for
the existing evaluationLinePower objects, rather than introducing new tensor powers.
Concatenating m and n factors on either side gives the same tensor and coefficient.
Tensor and sheafification uniqueness prove product compatibility, and multiplication of
functions proves the unit equation, also when m or n is zero. The first-power equation
is the unitor normalization. Apply graded_pushforward_etale_restriction to these powers.
Transport the resulting homogeneous comparisons through theta and its direct image.
Naturality of the actual counits identifies their evaluations with evaluations into the
actual powers of the restricted line module; the coproduct universal property gives the
same assertion for their sums. No assertion about global pure-tensor representations or
global homogeneous decompositions of sections is required. -/
theorem graded_pushforward_etale_restriction_line_powers
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom)
    (L : X.Modules) (_hL : X.IsLineModule L) :
    ∃ (A : EtaleGradedModuleAlgebra (evaluationLinePower X L))
      (R : GradedPushforwardEtaleRestriction f g h f' hg hp (evaluationLinePower X L) A)
      (A' : EtaleGradedModuleAlgebra
        (evaluationLinePower X' ((pullback h R.hh).obj L)))
      (theta : ∀ d : ℕ, (pullback h R.hh).obj (evaluationLinePower X L d) ≅
        evaluationLinePower X' ((pullback h R.hh).obj L) d)
      (thetaHom : R.restrictedAlgebra.Hom A'),
      HasCanonicalEtalePowerProducts X L A ∧
      HasCanonicalEtalePowerProducts X' ((pullback h R.hh).obj L) A' ∧
      (∀ d, thetaHom.degree d = (theta d).hom) ∧
      ((theta 1).hom ≫ (gradedPowerOneIso X' ((pullback h R.hh).obj L)).hom =
        (pullback h R.hh).map (gradedPowerOneIso X L).hom) ∧
      (∀ d, (moduleTensorPullback f').map ((moduleDirectImage f').map (theta d).hom) ≫
          evaluationCounit f' (evaluationLinePower X' ((pullback h R.hh).obj L) d) =
        evaluationCounit f' ((pullback h R.hh).obj (evaluationLinePower X L d)) ≫
          (theta d).hom) := by
  obtain ⟨A, hA⟩ := canonical_etale_line_power_algebra X L _hL
  obtain ⟨R⟩ := graded_pushforward_etale_restriction f g h f' hg hp _ A
  obtain ⟨A', theta, thetaHom, hA', hdegree, hone⟩ :=
    etale_line_power_comparison h R.hh L A hA R.restrictedAlgebra
      R.restrictedProducts.1 R.restrictedProducts.2
  refine ⟨A, R, A', theta, thetaHom, hA, hA', hdegree, hone, ?_⟩
  intro d
  exact (moduleTensorAdjunction f').counit_naturality (theta d).hom

end AlgebraicGeometry.AlgebraicSpace
