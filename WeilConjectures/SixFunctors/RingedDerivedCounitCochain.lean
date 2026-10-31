/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RingedDerivedAdjointLift
public import WeilConjectures.SixFunctors.RingedDerivedComparisonData
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependentSupplement
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions

/-!
# The ringed-topos derived counit on cochain representatives

Source: Stacks Project, Cohomology on Sites, Tag 0FPI, lemma-adjoints-push-pull-compatibility
(blueprint: lem-sf-ringed-derived-counit-cochain).

The theorem records the commutative square between the derived counit and the
degreewise module counit for an arbitrary unbounded complex.  The comparison on
the pullback side is the canonical comparison attached to the left-derived
functor, and the right-derived comparison is required to satisfy its universal
property; hence no resolution condition is imposed on the displayed complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.RingedDerivedComparisons

private theorem comparison_naturality
    {A B : SheafOfModules.RingedTensorCorner.{u, w}}
    (e : SheafOfModules.RingedTensorEdge A B)
    {P Q : CochainComplex A.mateModules ℤ} (a : P ⟶ Q) :
    e.left.map (DerivedCategory.Q.map a) ≫
        derivedPullbackComplexComparison e.pullback e.left e.epsilon Q =
      derivedPullbackComplexComparison e.pullback e.left e.epsilon P ≫
        DerivedCategory.Q.map ((e.pullback.mapHomologicalComplex (.up ℤ)).map a) := by
  let G := e.pullback.mapHomologicalComplex (.up ℤ)
  let eps : DerivedCategory.Q ⋙ e.left ⟶ G ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A.mateModules).inv e.left ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A.mateModules (.up ℤ)) e.epsilon ≫
      Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft G (DerivedCategory.quotientCompQhIso B.mateModules).hom
  simpa only [eps, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map,
    derivedPullbackComplexComparison, Category.assoc] using eps.naturality a

set_option maxHeartbeats 1000000 in
-- The two resolutions require conversions between the site and tensor-corner module types.
/-- The canonical ringed-topos derived counit agrees with the ordinary cochain counit.

Source: Stacks Project, Cohomology on Sites, Tag 0FPI, lemma-adjoints-push-pull-compatibility,
statement and K-flat/K-injective comparison diagram
(blueprint: lem-sf-ringed-derived-counit-cochain).

Proof. Fix a K-injective target I and a map b : M → f_*I. Choose a K-flat
resolution p : P → M with flat terms. Apply the lift's canonical adjunction
formula to p followed by b. Naturality of the two inverse Hom equivalences and
of the left-derived comparison identifies both sides with composites whose
first map is L(Q(p)). Cancel this isomorphism to obtain the formula for every M.
For arbitrary N, choose a K-injective resolution i : N → I and apply that formula
to M = f_*N and b = f_*i. Naturality of the right-derived comparison and the
inverse derived Hom equivalence rewrites the left side as the transpose of
eta_N followed by Q(i). The ordinary inverse Hom formula and counit naturality
rewrite the right side as the ordinary counit followed by Q(i). Cancel Q(i),
then expand the inverse derived Hom formula to obtain the asserted square.
This uses the supplied normalization `def-sf-ringed-derived-adjoint-lift`,
`lem-pc-kflat-resolution`, and `prop-pur-kinjective-resolutions-exist`.
-/
theorem ringedDerivedCounitCochain
    {X Y : Site.{u, w}} {f : Morphism X Y} (l : AdjointLift f)
    (N : CochainComplex X.modules ℤ) :
    l.edge.left.map (l.eta.app N) ≫
        l.edge.derivedAdjunction.counit.app (DerivedCategory.Q.obj N) =
      derivedPullbackComplexComparison
          l.edge.pullback l.edge.left l.edge.epsilon
          ((l.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Q.map
          ((l.edge.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app N) := by
  let F := l.edge.pushforward.mapHomologicalComplex (.up ℤ)
  let d := l.edge.derivedAdjunction
  let c := l.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)
  let α := derivedPullbackComplexComparison l.edge.pullback l.edge.left l.edge.epsilon
  have h (M : CochainComplex Y.modules ℤ) (I : CochainComplex X.modules ℤ)
      (hI : I.IsKInjective) (b : M ⟶ F.obj I) :
      (d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map b ≫ l.eta.app I) =
        α M ≫ DerivedCategory.Q.map ((c.homEquiv M I).symm b) := by
    obtain ⟨P, p, hP, hf, hp, _⟩ := CochainComplex.exists_isKFlatResolution M
    have : QuasiIso p := hp
    have : IsIso (DerivedCategory.Q.map p) := inferInstance
    apply (cancel_epi (l.edge.left.map (DerivedCategory.Q.map p))).1
    calc
      _ = (d.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map (p ≫ b) ≫ l.eta.app I) := by
        simp only [Functor.map_comp, Category.assoc,
          Adjunction.homEquiv_naturality_left_symm]
      _ = α P ≫ DerivedCategory.Q.map ((c.homEquiv P I).symm (p ≫ b)) :=
        l.canonical_adjunction P I ⟨hP, hf⟩ hI (p ≫ b)
      _ = _ := by
        rw [Adjunction.homEquiv_naturality_left_symm, Functor.map_comp,
          ← Category.assoc, ← comparison_naturality l.edge p, Category.assoc]
  obtain ⟨_, _, R, ι, hR⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions X.J X.A
  let i := ι.app N
  have : QuasiIso i := (hR N).1
  have : IsIso (DerivedCategory.Q.map i) := inferInstance
  apply (cancel_mono (DerivedCategory.Q.map i)).1
  have hi := h (F.obj N) (R.obj N) (hR N).2.1 (F.map i)
  have hn := l.eta.naturality i
  dsimp only [Functor.comp_map] at hn
  rw [hn, Adjunction.homEquiv_naturality_right_symm] at hi
  simp only [Adjunction.homEquiv_counit] at hi
  have hc := c.counit.naturality i
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  erw [hc] at hi
  dsimp only [Functor.id_obj, Functor.comp_obj, F, d, c, α, Site.corner] at hi ⊢
  simpa only [Functor.map_comp, Category.assoc] using hi

end CategoryTheory.RingedDerivedComparisons
