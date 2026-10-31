/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
public import WeilConjectures.CategoryTheory.AlgebraDiagramAmbientSpecialization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.AlgebraDiagramAmbientBalancingResolving
import WeilConjectures.CategoryTheory.AlgebraDiagramAmbientBalancingDescent
/-! # Balanced coefficient specialization of derived tensor pullback

Source: Stacks 03EL and 07A4; scalar refinement of the pullback tensor formula.
(blueprint: lem-pur-algebra-diagram-ambient-balancing).
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u w
open CategoryTheory CategoryTheory.CochainPullback
open SheafOfModules.PullbackTensorCanonical
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
/-- The scalar-association comparison has the independently normalized ambient
coefficient specialization as its underlying map.

Source: Stacks 03EL and 07A4, scalar refinement of the pullback tensor formula;
step 4 of lem-pur-algebra-diagram-pullback-extension-coherence
(blueprint: lem-pur-algebra-diagram-ambient-balancing).

Proof: choose a flat-term K-flat representative P for the variable and a second
flat-term K-flat resolution Q of the coefficient module in degree zero. Cancel
the invertible resolution maps in the two normalized scalar tensor formulas.
The normalization of the ambient comparison on (P,Q) identifies its coefficient
specialization with the ordinary cochain pullback tensor comparison followed by
beta. The restriction square is the localization of b; the extension square
is the localization of scalar association kappa. On generalized pure tensors
both resulting maps send a tensor (p tensor b) to (a tensor p) tensor b: the
restriction and association route first gives (1 tensor p) tensor (a-bar b),
which is equal by balancing. The specified generator equations for b and beta
identify the scalars and all actual horizontal transitions. Tensor and
sheafification universal properties give equality of chain maps. Descent on
the resolving class gives equality on every unbounded derived object. -/
theorem ambient_balancing
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f)
    (d : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    [IsIso f.coefficient] [IsIso d.coefficient']
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
    [ExactPullback f] [ExactPullback (changed f d)]
    [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
    (s : ScalarDerivedPresentation.{u, w} d.sourceMap)
    (t : ScalarDerivedPresentation.{u, w} d.targetMap)
    (b : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
      (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap)
    (hb : ∀ (H : Modules.{u, u, u} d.R') (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} d.R').obj H),
      generator f k x ≫ (underlying.{u, u, u} S).map (b.hom.app H) =
        generator (changed f d) k' x)
    (e : ExtensionComparison f d s t) (he : IsNormalizedExtension f k d k' s t e)
    (beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap)
    (hbeta : ∀ (Z : Sheaf K (Type u))
      (x : Z ⟶ (underlying.{u, u, u} R).obj (coefficient d.sourceMap)),
      generator f k x ≫ (underlying.{u, u, u} S).map beta.hom =
        f.uInv.map x ≫ d.I'.ringUnderlying.hom ≫
          (sheafCompose L (forget CommRingCat.{u})).map d.coefficient')
    (a : Phi f.L.mapDerivedCategory.{w, w} ≅ Psi f.L.mapDerivedCategory.{w, w})
    (ha : IsNormalized f k f.L.mapDerivedCategory f.L.mapDerivedCategoryFactors.hom a.hom)
    (M : DerivedCategory (Modules.{u, u, u} R)) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app (s.model.T.obj M) ≫
        (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.map (e.hom.app M) =
      (ambientSpecialization f d s t a beta).hom.app M := by
  apply ambient_balancing_descent f k d k' s t b e beta a ?_ M
  intro P hp hf
  exact ambient_balancing_resolving f k d k' s t b hb e he beta hbeta a ha P hp hf
end CategoryTheory.AlgebraDiagramPullback
