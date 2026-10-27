module

public import Sheaf.AlgebraicGeometry.SmoothJacobianDiagonalData
import Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple

/-! # The canonical rigidified ample line on a smooth relative Jacobian

Source: Deligne, Le lemme de Gabber, Section 4.1, pp.141--142
(blueprint: lem-sfb-smooth-jacobian-canonical-line).

The assignment contains all cartesian family arrows, so its explicit identity and
composition equations apply to arbitrary base change, family isomorphisms, and the
three projections from a triple fibre product. The diagonal line is the actual
pullback of the normalized Poincare module along the canonical theta polarization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace
open Poincare JacobianDiagonal

/-- The diagonal Poincare construction for smooth stable unpointed genus-g families,
g at least two, gives a symmetric, identity-rigidified, relatively ample line and
canonical coherent comparisons. The ordinary ampleness assertion includes a scheme
representative and ampleness over every affine open of the actual base. All families
have locally Noetherian actual base; the ambient S has no extra hypothesis.

Source: Deligne, Le lemme de Gabber, Section 4.1, pp.141--142
(blueprint: lem-sfb-smooth-jacobian-canonical-line).

Proof plan:
1. Apply lem-sfb-relative-jacobian-theta-polarization to each represented degree-zero
   Picard space, obtaining theta autoduality. Apply
   lem-sfb-abelian-space-poincare-calculus to obtain the normalized universal module.
   Pull it back along (1,lambda). Rank-one local frames pull back to rank-one frames.
   The graph sends the identity to the intersection of the two identity axes;
   their compatible trivializations give the specified rigidification.
2. Biadditivity of Poincare identifies its pullback under (-1,-1) with itself:
   negating each variable dualizes twice. Theta autoduality respects inversion,
   so restriction to its graph gives symmetry, preserving identity trivializations.
3. On a geometric fibre choose a theta line L. The normalized difference identity,
   restricted to (x,-x), gives B = L tensor [-1]*L tensor the inverse square of
   its identity line. A basis of that field-line removes the final factor.
   lem-sc-ample-tensor gives ampleness. This works also in characteristic two.
4. Apply lem-sfb-space-relative-ample-locus to the proper Jacobian space and B.
   Every geometric fibre lies in the ample locus, so the locus is the whole base.
   This supplies a scheme model and ordinary ampleness over every affine open.
5. Theta and universal Poincare commute with every locally Noetherian base change.
   Pull their comparisons back along the graph. For a curve isomorphism, use its
   induced Picard map a and the identities a-dual lambda_D a = lambda_C and
   (a,1)*P_D = (1,a-dual)*P_C. All comparisons preserve the identity rigidification.
   Their difference is a rigidified line automorphism on a proper abelian space,
   hence the identity by the rigidity clause of the Poincare node. Thus the maps
   and line comparisons obey the displayed identity and composition equations,
   including triple fibre products. No global theta line or theta characteristic
   is chosen, and there is no restriction on the characteristic or base map.
-/
theorem smoothJacobian_canonical_line (S : Scheme.{u}) :
    ∃ A : Assignment S, ∀ I : Input S,
      IsLine I.J (line (A.polarization I)) ∧
      (∃ v : (smallModuleTensorPullback (A.polarization I).group.inv).obj
          (line (A.polarization I)) ≅ line (A.polarization I),
        (smallModuleTensorPullback (A.polarization I).group.e).map v.hom ≫
            (A.rigidification I).hom =
          (rigidificationPullback (A.polarization I).group.e
            (A.polarization I).group.e (𝟙 I.B) (A.polarization I).group.inv
            ((A.polarization I).group.inv_identity.trans (Category.id_comp _).symm)
            (line (A.polarization I)) (A.rigidification I)).hom) ∧
      ∃ M : Model (A.polarization I), RelativelyAmple M := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
