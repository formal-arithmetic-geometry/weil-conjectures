/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.EtaleSumStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Supported étale generators for cohomological support filtrations

Source: ILO, Travaux de Gabber, XVII 5.2, and the agent-formulated supported-generator
argument recorded in the DAG (blueprint: lem-per-etale-support-aisle-generators).
ILO motivates the filtration; the unbounded generator equality is the separate argument below.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace AlgebraicGeometry.Etale

/-- The prescribed generator `u_! i_* Λ_Z[-a]`, with the sheaf first placed in degree zero.
The direct image and the étale sum extension are ordinary sheaf functors, since these
particular functors are exact. Source: ILO XVII 5.2, supported-generator argument
(blueprint: lem-per-etale-support-aisle-generators). -/
def supportFiltrationGenerator (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (V : X.Etale) (Z : Scheme.{u}) (i : Z ⟶ V.left) (a : ℤ) :
    DerivedCategoryModule Λ X :=
  ((_root_.DerivedCategory.singleFunctor _ 0).obj
    ((etaleLowerShriek (ModuleCat.{u + 1} Λ) V.hom inferInstance).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) i).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ)))))⟦-a⟧

/-- The ordinary cohomological support class: every nonzero geometric stalk of `H^a K`
lies in `Φ a`. We use the algebraic closure of the residue field at each point, hence
one geometric point over every point, without closing the support topologically.
Source: ILO XVII 5.2, supported-generator argument
(blueprint: lem-per-etale-support-aisle-generators). -/
def supportFiltrationClass (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (Φ : ℤ → Set X) : ObjectProperty (DerivedCategoryModule Λ X) :=
  fun K ↦ ∀ (a : ℤ) (x : X),
    ¬ IsZero (pointedEtaleStalk ((_root_.DerivedCategory.homologyFunctor _ a).obj K)
      (X.algClosurePoint x)) → x ∈ Φ a

/-- The cohomological support class is the smallest strictly full class containing the
supported generators and zero, and closed under small coproducts, retracts, positive
shift and extensions. The affine objects are taken in a small model of the affine
étale category; replacing it by a skeleton gives the same strictly full class.

Source: ILO XVII 5.2 motivates the support condition; the following unbounded argument
is agent-formulated (blueprint: lem-per-etale-support-aisle-generators).

Proof, following the nine steps of the DAG:
1. Exact geometric stalks commute with sums by the module forgetful functor and
   termwise derived coproducts. Thus the support class is closed under coproducts
   and summands. The long exact cohomology sequence gives extension closure, and
   `H^q(K[1]) = H^(q+1)(K)` with the decreasing filtration gives positive-shift closure.
2. Closed pushforward vanishes off the closed subscheme (lem-kun-04ca); the étale
   sum stalk formula (lem-amb-etale-sum-stalks) then puts each generator's support
   in `Φ a`. Hence their closure lies in the support class.
3. Rotate the telescope triangle. Coproducts and positive shifts of its terms give
   closure under sequential homotopy colimits. The complex-colimit comparison
   (lem-kun-complex-colimit-hocolim) applies to actual increasing subcomplexes.
4. For a section over an affine étale object, its zero locus is open by
   lem-sc-etale-section-zero-open. Its closed complement has the reduced induced
   structure. The open-closed exact sequence for the constant sheaf factors the
   section map through the constant sheaf on that closed complement.
5. Transpose this map by the étale sum adjunction. Sum over affine objects and
   sections. Every stalk germ is hit, so exactness and conservativity of geometric
   stalks give an epimorphism from supported generators onto any supported sheaf.
6. Repeat on kernels, whose support remains in the same subset. This gives an
   exact supported resolution, with the n-th term in degree a-n. Its individual
   terms are coproducts of the prescribed generators shifted positively by n.
7. The finite brutal tails are iterated extensions by their single-degree terms,
   using lem-weil-pbc-complex-ses-triangle. Their sequential colimit gives the
   resolution, hence every supported sheaf placed in degree a belongs to the closure.
8. Since `Φ q = univ` for q at most b, all sheaves in degrees at most b belong.
   A representative vanishing above b, its finite brutal tails and their telescope
   put the entire ordinary aisle D^(≤b) in the generated class.
9. Starting at the good truncation in degree b, the successive truncation triangles
   add H^n(K)[-n], already handled by Step 7. Good truncations stabilize termwise;
   their telescope is K, proving the reverse inclusion. Empty X and the zero
   coefficient ring give zero sheaves throughout and require no excluded cases. -/
theorem supportFiltrationClass_isLeast (X : Scheme.{u}) [IsNoetherian X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (Φ : ℤ → Set X)
    (hΦ : ∀ a : ℤ, StableUnderSpecialization (Φ a))
    (hdecr : ∀ a : ℤ, Φ (a + 1) ⊆ Φ a)
    (hbounded : ∃ b : ℤ, ∀ a : ℤ, a ≤ b → Φ a = Set.univ) :
    IsLeast
      {P : ObjectProperty (DerivedCategoryModule Λ X) |
        (∀ (K L : DerivedCategoryModule Λ X), Nonempty (K ≅ L) → P K → P L) ∧
        P (0 : DerivedCategoryModule Λ X) ∧
        (∀ (I : Type (u + 1)) (F : I → DerivedCategoryModule Λ X) (c : Cofan F),
          IsColimit c → (∀ i : I, P (F i)) → P c.pt) ∧
        (∀ (K L : DerivedCategoryModule Λ X), Retract K L → P L → P K) ∧
        (∀ K : DerivedCategoryModule Λ X, P K → P (K⟦(1 : ℤ)⟧)) ∧
        (∀ T : Triangle (DerivedCategoryModule Λ X), T ∈ distTriang _ →
          P T.obj₁ → P T.obj₃ → P T.obj₂) ∧
        (∀ (V : SmallModel.{u} X.AffineEtale) (Z : Scheme.{u})
          (i : Z ⟶ ((Scheme.AffineEtale.Spec X).obj
            ((equivSmallModel.{u} X.AffineEtale).inverse.obj V)).left) (a : ℤ),
          IsReduced Z → IsClosedImmersion i →
          Set.range (fun z : Z ↦
            ((Scheme.AffineEtale.Spec X).obj
              ((equivSmallModel.{u} X.AffineEtale).inverse.obj V)).hom (i z)) ⊆ Φ a →
          P (supportFiltrationGenerator X Λ
            ((Scheme.AffineEtale.Spec X).obj
              ((equivSmallModel.{u} X.AffineEtale).inverse.obj V)) Z i a))}
      (supportFiltrationClass X Λ Φ) := by
  sorry

end AlgebraicGeometry.Etale
