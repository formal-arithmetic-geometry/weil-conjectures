module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexStalkCondition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.RingedSitePointExact
import Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion
import Sheaf.Algebra.Homology.RingedSitePointTensor
import Sheaf.SecSmoothPurity.CochainInverseComparison
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.RingedTopoiTensorComparisonData
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyAction
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonInheritance

/-! # Tensor inheritance of geometric-stalk base change

Source: Stacks Project, spaces-perfect.tex, Tag 0DKI(1), and equation-bc before 0DKG.
(blueprint: lem-sfb-space-single-complex-tensor-inheritance).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace.SingleComplex

/-- Tensoring by any unbounded quasi-coherent derived object preserves the canonical
geometric-stalk single-complex base-change condition.
Source: Stacks Project, spaces-perfect.tex, Tag 0DKI(1), equation-bc before 0DKG.
(blueprint: lem-sfb-space-single-complex-tensor-inheritance).

Proof:
1. Derived pullback and derived tensor preserve quasi-coherent cohomology
   (lem-sfb-space-derived-qcoh-pullback-tensor). The canonical tensor comparison is
   computed on flat-term K-flat representatives (07A4 and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
2. Choose flat-term K-flat representatives P,Q of E,K (lem-pc-kflat-resolution)
   and a K-injective representative I of K' (prop-pur-kinjective-resolutions-exist).
   The K-injective Hom bijection (lem-weil-pbc-kinjective-hom-derived) represents
   phi by a chain map a:g'^*Q to I; a need not be a quasi-isomorphism.
3. Fix a geometric point. Exact module stalks and the K-flat stalk criterion
   (lem-sfb-ringed-site-point-exact, lem-sfb-ringed-site-kflat-stalk-criterion)
   give K-flat A-complexes U=P_x and Q_x. The geometric stalk tensor calculus
   (lem-sfb-space-geometric-stalk-tensor-calculus) gives C flat over D=A tensor_R B
   and the representative t:C tensor_A Q_x to I_x'. Neither A nor B need be R-flat.
4. The total tensor model (lem-pur-kflat-total-tensor-model) represents E tensor K.
   Its pullback comparison, normalized by the recorded local unit tensors
   (def-weil-pbc-canonical-ringed-tensor-comparison and
   lem-pur-independent-inverse-image-tensor-comparison), has stalk
   c tensor (u tensor q) mapped to (c tensor u) tensor (1 tensor q).
   The signed stalk tensor identification (lem-sfb-ringed-site-point-tensor)
   therefore identifies psi with this map followed by 1 tensor t.
   Each (p,q) summand retains the order u,q and the sign (-1)^p on its second
   differential. Pullback preserves flat-term K-flat representatives.
5. Use the canonical D-linear cohomology action and model
   (lem-pc-base-derived-tensor-cohomology-action,
   def-pc-base-derived-tensor-cohomology-model) for Q_x and U tensor_A Q_x.
   The localized counit sends h tensor c to c times the image of h.
   Following it by H(t) is exactly beta_phi, with its canonical D-action.
6. Apply lem-pc-localized-tensor-comparison-inheritance to U,Q_x,I_x',t.
   Its flatness and K-flatness hypotheses are supplied in step 3, and its
   all-degree invertibility hypothesis is exactly h_stalk by step 5.
7. The normalized map in step 4 identifies the resulting localized tensor
   comparison with beta_psi in every degree at the chosen point. This proves
   the assertion for all points and all integer degrees, without degree bounds
   or any flatness assumption on the original cartesian square. -/
theorem singleComplexTensorInheritance {S : Scheme.{u}}
    [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]
    {X X' Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : X.DerivedQCoh) (K' : X'.DerivedQCoh)
    (φ : (derivedPullback g').obj K.obj ⟶ K'.obj)
    (h_stalk : StalkCondition f f' g g' sq K.obj K'.obj φ) :
    ∀ E : X.DerivedQCoh,
      StalkCondition f f' g g' sq
        ((tensor X).obj (E.obj, K.obj))
        ((tensor X').obj ((derivedPullback g').obj E.obj, K'.obj))
        ((derivedTensorComparison g').hom.app (E.obj, K.obj) ≫
          (tensor X').map (Prod.mkHom (𝟙 ((derivedPullback g').obj E.obj)) φ)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.SingleComplex
