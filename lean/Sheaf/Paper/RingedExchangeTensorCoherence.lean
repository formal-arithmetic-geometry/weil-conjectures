/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.RingedTensorSquarePresentation
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Projection-formula coherence for a square of ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 0E48, 07A4 and 0D6D
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

/-- The canonical ordinary module square applied termwise to a complex.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.complexComparison
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    g.pullback.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      k.pullback.mapHomologicalComplex (ComplexShape.up ℤ) ≅
    f.pullback.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      h.pullback.mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)

/-- The representative square determines the derived commutation isomorphism uniquely.
Proof: choose a flat K-flat resolution (lem-pc-kflat-resolution). The two successive
pullbacks compute the derived composites and stay flat K-flat by
lem-weil-pbc-ringed-topoi-derived-pullback and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Apply the ordinary square termwise.
The insertion equation says precisely that it multiplies the same nested scalars
as scalar-extension associativity and the given ringed commutation isomorphism.
Descend this natural isomorphism along the equivalence of the resolving subcategory
with the derived category (lem-weil-pbc-site-derived-tensor-descent). Full faithfulness
gives uniqueness and independence of representatives.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
theorem RingedTensorSquare.derivedComparison_existsUnique
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    ∃! theta : g.left ⋙ k.left ≅ f.left ⋙ h.left,
      ∀ (P : CochainComplex (SheafOfModules.{u} ((sheafCompose Y.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj Y.ring)) ℤ),
        P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        theta.hom.app (DerivedCategory.Q.obj P) ≫
          h.left.map (derivedPullbackComplexComparison f.pullback f.left f.epsilon P) ≫
          derivedPullbackComplexComparison h.pullback h.left h.epsilon
            ((f.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        k.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
          derivedPullbackComplexComparison k.pullback k.left k.epsilon
            ((g.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (s.complexComparison.hom.app P) := sorry

/-- The specified derived commutation isomorphism, selected by its unique
K-flat representative characterization. Only a uniqueness-determining proof is postponed.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.derivedComparison
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    g.left ⋙ k.left ≅ f.left ⋙ h.left :=
  Classical.choose s.derivedComparison_existsUnique.exists

/-- The exchange transformation is exactly the mate of the canonical derived square,
using the existing Mathlib mate equivalence (def-weil-pbc-adjunction-mate).
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.exchange
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    f.right ⋙ g.left ⟶ h.left ⋙ k.right :=
  (mateEquiv f.derivedAdjunction k.derivedAdjunction
    (TwoSquare.mk g.left f.left k.left h.left s.derivedComparison.hom)).natTrans

/-- The projection map is the adjunct of tensor comparison followed by counit tensor
identity. In particular no projection-formula isomorphism is assumed.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorEdge.projection
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (a : RingedTensorModel A) (b : RingedTensorModel B)
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose B.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj B.ring))) (Q : DerivedCategory (SheafOfModules.{u} ((sheafCompose
      A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))) :
    A.tensor.obj (e.right.obj E, Q) ⟶ e.right.obj (B.tensor.obj (E, e.left.obj Q)) :=
  e.derivedAdjunction.homEquiv _ _
    ((e.tensorComparison a b).hom.app (e.right.obj E, Q) ≫
      B.tensor.map (CategoryTheory.Prod.mkHom (e.derivedAdjunction.counit.app E)
        (𝟙 (e.left.obj Q))))

/-- The upper/right route, including tensor and composition identifications of its target.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.projectionFirst
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (aX' : RingedTensorModel X')
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose X.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj X.ring))) (Q : DerivedCategory (SheafOfModules.{u} ((sheafCompose
      Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring))) :
    g.left.obj (Y.tensor.obj (f.right.obj E, Q)) ⟶
      k.right.obj (X'.tensor.obj (h.left.obj E, k.left.obj (g.left.obj Q))) :=
  g.left.map (f.projection aY aX E Q) ≫
    s.exchange.app (X.tensor.obj (E, f.left.obj Q)) ≫
    k.right.map ((h.tensorComparison aX aX').hom.app (E, f.left.obj Q) ≫
      X'.tensor.map (CategoryTheory.Prod.mkHom (𝟙 (h.left.obj E))
        (s.derivedComparison.inv.app Q)))

/-- The lower/left route: tensor comparison, exchange tensor identity, then projection.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.exchangeFirst
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (aY : RingedTensorModel Y) (aY' : RingedTensorModel Y')
    (aX' : RingedTensorModel X')
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose X.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj X.ring))) (Q : DerivedCategory (SheafOfModules.{u} ((sheafCompose
      Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring))) :
    g.left.obj (Y.tensor.obj (f.right.obj E, Q)) ⟶
      k.right.obj (X'.tensor.obj (h.left.obj E, k.left.obj (g.left.obj Q))) :=
  (g.tensorComparison aY aY').hom.app (f.right.obj E, Q) ≫
    Y'.tensor.map (CategoryTheory.Prod.mkHom (s.exchange.app E) (𝟙 (g.left.obj Q))) ≫
    k.projection aY' aX' (h.left.obj E) (g.left.obj Q)

/-- Projection and exchange commute for every commutative square of ringed topoi;
the displayed composites are also natural simultaneously in E and Q.
Proof, following the five steps of this node:
(1) The preceding unique representative construction gives theta; it uses flat
K-flat resolutions, ringed pullback preservation, scalar-extension associativity
and descent (lem-pc-kflat-resolution, lem-weil-pbc-ringed-topoi-derived-pullback,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-site-derived-tensor-descent).
(2) On flat K-flat representatives the canonical tensor map splits a pure tensor
as s tensor (v tensor w) mapped to (s tensor v) tensor (1 tensor w).
The module square is fixed on insertions. Its linearity and the balancing relation
show that splitting tensors before or after composition multiplies the same scalars.
Hence theta respects tensor. Termwise maps preserve bidegrees, giving no extra sign.
Descend in both variables by lem-weil-pbc-site-derived-tensor-descent, using
lem-weil-pbc-ringed-topoi-module-pullback-tensor and the recorded canonical tensor theorem.
(3) Transpose under k.derivedAdjunction. By def-weil-pbc-adjunction-mate,
the transpose of exchange is theta followed by h of the f-counit; the transpose
of projection is tensor comparison followed by counit tensor identity. These
identities are the two adjunction triangle identities.
(4) Naturality of theta for the projection map rewrites the transpose of the first
route as (h counit tensor theta inverse) after the tensor comparison for h f.
(5) Rewrite this comparison with (2); theta and its inverse cancel on Q.
The result is the transpose of the second route by (3). Injectivity of the
hom-equivalence proves equality. Naturality of tensor comparisons, theta, counits,
and the hom-equivalence proves the naturality equation for arbitrary pairs of
morphisms. No cartesianness, flatness, boundedness, properness or perfectness is used.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
theorem ringedExchangeTensorCoherence
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (aY' : RingedTensorModel Y') (aX' : RingedTensorModel X') :
    (∀ (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose X.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj X.ring))) (Q : DerivedCategory (SheafOfModules.{u} ((sheafCompose
      Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring))),
      s.projectionFirst aY aX aX' E Q = s.exchangeFirst aY aY' aX' E Q) ∧
    ∀ (E E' : DerivedCategory (SheafOfModules.{u} ((sheafCompose X.topology (forget₂
      CommRingCat.{u} RingCat.{u})).obj X.ring))) (Q Q' : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)))
      (v : E ⟶ E') (z : Q ⟶ Q'),
      g.left.map (Y.tensor.map (CategoryTheory.Prod.mkHom (f.right.map v) z)) ≫
        s.projectionFirst aY aX aX' E' Q' =
      s.projectionFirst aY aX aX' E Q ≫
        k.right.map (X'.tensor.map (CategoryTheory.Prod.mkHom (h.left.map v)
          (k.left.map (g.left.map z)))) := sorry

end SheafOfModules
