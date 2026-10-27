/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexStalkCondition
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Sheaf.Paper.StrictPerfectRingedPullbackModel
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentRHomQuasiCoherent
import Sheaf.SixFunctors.RingedPerfectInternalHomPullback
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexTensorInheritance
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Perfect-source internal Hom inherits geometric-stalk base change

Source: Stacks Project, spaces-perfect.tex, Tag 0DKI(2), with Tag 0A8A;
sites-cohomology.tex, Tag 08JF for the evaluation-transpose comparison.
(blueprint: lem-sfb-space-single-complex-rhom-inheritance).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.SingleComplex

variable {S : Scheme.{u}}
variable [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]

/-- The internal-Hom pullback map is the transpose of pulled-back evaluation, using
the inverse of the already normalized K-flat tensor comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 08JF, used in spaces-perfect.tex, 0DKI(2)
(blueprint: lem-sfb-space-single-complex-rhom-inheritance). -/
def rhomPullbackComparison {X X' : AlgebraicSpace S} (h : X' ⟶ X)
    (P K : X.DerivedModules) :
    (derivedPullback h).obj (X.derivedHom.obj (op P, K)) ⟶
      X'.derivedHom.obj (op ((derivedPullback h).obj P), (derivedPullback h).obj K) :=
  X'.derivedDualityModel.closed.transpose _ ((derivedPullback h).obj P)
    ((derivedPullback h).obj K)
    ((derivedTensorComparison h).inv.app (X.derivedHom.obj (op P, K), P) ≫
      (derivedPullback h).map (X.derivedDualityModel.closed.evaluation P K))

/-- The coefficient map is the evaluation-transpose pullback comparison followed by
internal Hom applied to the given coefficient arrow in its second variable.
Source: Stacks Project, spaces-perfect.tex, Tag 0DKI(2), its displayed composite
(blueprint: lem-sfb-space-single-complex-rhom-inheritance). -/
def rhomCoefficientMap {X X' : AlgebraicSpace S} (h : X' ⟶ X)
    (P K : X.DerivedModules) (K' : X'.DerivedModules)
    (φ : (derivedPullback h).obj K ⟶ K') :
    (derivedPullback h).obj (X.derivedHom.obj (op P, K)) ⟶
      X'.derivedHom.obj (op ((derivedPullback h).obj P), K') :=
  rhomPullbackComparison h P K ≫
    X'.derivedHom.map (Prod.mkHom (𝟙 (op ((derivedPullback h).obj P))) φ)

/-- Perfect-source internal Hom has quasi-coherent cohomology on both sides and
inherits the canonical single-complex geometric-stalk condition.
Source: Stacks Project, spaces-perfect.tex, Tags 0DKI(2), 0DKG and 0A8A;
sites-cohomology.tex, Tags 08JF and 08JJ
(blueprint: lem-sfb-space-single-complex-rhom-inheritance).

Proof:
1. Pull back an etale cover carrying strict-perfect representatives of P.
   Composition and 2-isomorphism compatibility from
   lem-sfb-ringed-derived-monoidal-comparisons identify restriction of Lh*P with
   pullback of the restricted P. Apply
   lem-weil-pbc-strict-perfect-ringed-pullback-model on each chart: the pulled-back
   bounded finite-free retracts show Lh*P is perfect, with the same local bounds.
   Put E = RHom(P,O). By lem-sfb-ringed-site-perfect-duality, E is perfect.
   Apply lem-sfb-space-pseudocoherent-rhom-quasicoherent in its perfect-source case
   to (P,O), (P,K), and (Lh*P,K'). This gives quasi-coherence of E, J, and J'.
   There is no lower bound on either coefficient complex.
2. Perfect duality gives a: E tensor K isomorphic to J. The perfect-source
   pullback comparison at (P,O), followed by the unit comparison, identifies
   Lh*E with RHom(Lh*P,O). Its evaluation pairing is pulled-back evaluation
   preceded by the inverse tensor comparison. Perfect duality for Lh*P gives
   b: Lh*E tensor K' isomorphic to J'. These are the canonical comparisons of
   lem-sfb-ringed-site-perfect-duality,
   lem-sfb-ringed-perfect-internal-hom-pullback and
   lem-sfb-ringed-derived-monoidal-comparisons.
3. Apply lem-sfb-space-single-complex-tensor-inheritance to E, K, K', phi.
   It gives the stalk condition for lambda: Lh*(E tensor K) to Lh*E tensor K',
   the tensor comparison followed by 1 tensor phi.
4. Check psi composed with Lh*(a) equals b composed with lambda. Uncurry both
   sides using lem-sf-ringed-derived-closed-symmetric-monoidal. Evaluation of a
   is evaluation of E against P tensored with 1_K. Evaluation of b is the
   pulled-back pairing tensored with 1_K'. The definition of
   rhomPullbackComparison and the strong symmetric monoidal identities identify
   both uncurried composites with that pulled-back pairing tensored with phi.
   The fixed associators and Koszul symmetries agree on both sides. Injectivity
   of transposition gives the equality of the coefficient maps.
5. Fix a geometric point and integer i. Naturality of the canonical comparison
   in def-sfb-space-single-complex-stalk-condition applied to this equality gives
   beta_psi composed with H^i(a_x tensor_R^L B) tensor_D C equals
   H^i(b_z) composed with beta_lambda, where D = A tensor_R B.
   The two vertical maps are isomorphisms because a and b are isomorphisms;
   beta_lambda is an isomorphism by step 3. Cancel the first vertical map to
   obtain invertibility of beta_psi in every degree at every geometric point. -/
theorem singleComplexRHomInheritance {X X' Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (h : X' ⟶ X)
    (sq : IsPullback h f' f g)
    (K : X.DerivedQCoh) (K' : X'.DerivedQCoh)
    (φ : (derivedPullback h).obj K.obj ⟶ K'.obj)
    (h_stalk : StalkCondition f f' g h sq K.obj K'.obj φ)
    (P : X.DerivedModules)
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf P) :
    X.derivedQCohProperty (X.derivedHom.obj (op P, K.obj)) ∧
      X'.derivedQCohProperty
        (X'.derivedHom.obj (op ((derivedPullback h).obj P), K'.obj)) ∧
      StalkCondition f f' g h sq
        (X.derivedHom.obj (op P, K.obj))
        (X'.derivedHom.obj (op ((derivedPullback h).obj P), K'.obj))
        (rhomCoefficientMap h P K.obj K'.obj φ) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.SingleComplex
