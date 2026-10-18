/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.RingedTensorSquarePresentation
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Tensor compatibility of a ringed square on flat K-flat representatives

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D and 0E48
(blueprint: lem-weil-pbc-ringed-square-tensor-compatibility).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory

namespace SheafOfModules

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

/-- The representative characterization of the derived square is compatible with
canonical tensor comparisons on flat K-flat complexes.

Proof: write each module pullback as inverse image followed by scalar extension.
Its canonical tensor map sends s tensor (v tensor w) to
(s tensor v) tensor (1 tensor w). The insertion equation for the square fixes its
module comparison on 1 tensor (1 tensor v). By linearity and balancing it therefore
commutes with the tensor map: both orders split the same two factors and multiply
the same nested scalars. This checks equality on pure tensors, which locally generate the
sheafified scalar extensions and their tensor products, and hence proves equality of module
sheaf maps. Apply this equality in each bidegree of the total tensor complex.
The maps preserve both degrees, so there is no interchange sign. Pullback preserves
flat K-flat complexes. Their total tensor is K-flat: reassociate its tensor with
an acyclic test complex and apply K-flatness of the two factors successively.
Its terms are flat: tensoring with a tensor product is the composition of the two
exact tensor functors, and each total degree is a direct sum of such flat products;
these sums are flat by exactness of direct sums and preservation of sums by tensor.
For the derived transport, write T for the ordinary total tensor, r_A(P,Q) for
the model identification Q(T(P,Q)) ≅ A.tensor(Q(P),Q(Q)), C_e for the edge complex
comparison, and d_e for the inverse of ordinaryTensor.totalIso. The defining
representative equation for the edge tensor comparison is
  e.left.map(r_A) ; t_e ; B.tensor.map(C_e(P),C_e(Q))
    = C_e(T(P,Q)) ; Q.map(d_e) ; r_B(e*P,e*Q).
Precompose the desired identity with (g.left ⋙ k.left).map(r_Y(P,Q).hom).
Postcompose it with X'.tensor applied to the pair
  h.left.map(C_f(P)) ; C_h(f*P), h.left.map(C_f(Q)) ; C_h(f*Q).
These maps are isomorphisms on flat K-flat representatives, so cancellation is valid.
Naturality of theta for r_Y, naturality of the edge tensor comparisons, and the
four edge representative equations reduce the left side to the composite through
C_h(f*T(P,Q)). Apply the assumed equation for theta at T(P,Q). On the right side,
apply the assumed equations at P and Q, followed by the representative equations
for g and k. Naturality of C_h and C_k for d_f and d_g, and naturality of r_X',
reduce the remaining equality to Q applied to
  gamma_T ; h*(d_f) ; d_h = k*(d_g) ; d_k ; T(gamma_P,gamma_Q),
where gamma is the termwise module square. This is exactly the total-complex
identity already established on pure tensors. Functoriality of Q proves the
conjugated equality; cancellation proves the asserted derived equality.
This is only the representative calculation: extension to arbitrary derived objects
and the mate argument are separate steps.
Source: Stacks, Cohomology on Sites, Tags 07A4 (pullback and tensor),
0D6D (composition), and 0E48 (compatibility; verification omitted there)
(blueprint: lem-weil-pbc-ringed-square-tensor-compatibility). -/
theorem ringedSquareTensorCompatibility
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (aY' : RingedTensorModel Y') (aX' : RingedTensorModel X')
    (theta : g.left ⋙ k.left ≅ f.left ⋙ h.left)
    (htheta : ∀ (P : CochainComplex (SheafOfModules.{u}
        ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ),
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
      theta.hom.app (DerivedCategory.Q.obj P) ≫
        h.left.map (derivedPullbackComplexComparison f.pullback f.left f.epsilon P) ≫
        derivedPullbackComplexComparison h.pullback h.left h.epsilon
          ((f.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      k.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
        derivedPullbackComplexComparison k.pullback k.left k.epsilon
          ((g.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P))
    (P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hPf : ∀ n : ℤ, (P.X n).IsFlat)
    (hQ : Q.IsAcyclicTensorKFlat) (hQf : ∀ n : ℤ, (Q.X n).IsFlat) :
    theta.hom.app (Y.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      h.left.map ((f.tensorComparison aY aX).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (h.tensorComparison aX aX').hom.app
        (f.left.obj (DerivedCategory.Q.obj P), f.left.obj (DerivedCategory.Q.obj Q)) =
    k.left.map ((g.tensorComparison aY aY').hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (k.tensorComparison aY' aX').hom.app
        (g.left.obj (DerivedCategory.Q.obj P), g.left.obj (DerivedCategory.Q.obj Q)) ≫
      X'.tensor.map (CategoryTheory.Prod.mkHom
        (theta.hom.app (DerivedCategory.Q.obj P))
        (theta.hom.app (DerivedCategory.Q.obj Q))) := by
  sorry

end SheafOfModules
