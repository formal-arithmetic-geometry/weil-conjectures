module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.RelativeJacobianThetaData
public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus
import Sheaf.AlgebraicGeometry.ConnectedProperFibresProper
import Sheaf.AlgebraicGeometry.SymmetricAbelImageGeometry
import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceUniversalIsomorphismOpen
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Picard.Degree

/-! # Relative Jacobian theta autoduality

Source: Deligne, Le lemme de Gabber, Section 4.1, pp.141--142;
Milne, Abelian Varieties, III Theorem 6.6, Summary 6.11 and Section 8
(blueprint: lem-sfb-relative-jacobian-theta-polarization).

The base of the family is `X.base.left`. The ambient scheme `R` is arbitrary.
Duals are arbitrary representing normalized Poincare data. The theta line is
asserted only on geometric fibres, with every choice of point and translate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

open Poincare JacobianTheta

/-- The represented degree-zero relative Picard space is an abelian family with its
canonical principal theta polarization. The group law is the Picard tensor law.
Every normalized dual carries the unique compatible polarization, functorial for
arbitrary locally Noetherian base change and curve isomorphisms. No global theta
line on the degree-zero Picard space is asserted.

Source: Deligne, Le lemme de Gabber, Section 4.1, pp.141--142;
Milne, Abelian Varieties, III Theorem 6.6, Summary 6.11 and Section 8
(blueprint: lem-sfb-relative-jacobian-theta-polarization).

Proof plan:
1. Stability gives projectivity, flatness, finite presentation and connected reduced
nodal geometric fibres. Smooth connected geometric curves have one component, so
multidegree zero is degree zero. Apply lem-sfb-nodal-picard-etale-schematic to get
the separated smooth finitely presented Picard group space and its canonical
Picard comparisons. The general-field Jacobian theorem thm-pd-jacobian-general-field
identifies every geometric fibre with an abelian variety. Apply
lem-sfb-connected-proper-fibres-proper to deduce properness. Pullback of line
classes supplies the identity and composition laws for the Picard identifications.
2. Apply lem-sfb-relative-degree-gminusone-theta. Etale locally choose a section p;
pull the canonical determinant theta line from the degree-(g-1) torsor to J using
M ↦ M tensor O((g-1)p). Poincare calculus gives its difference homomorphism.
On an overlap two choices differ by translation by O((g-1)(p_j-p_i)), including
on nonreduced overlaps.
3. In the four-factor normalized difference formula, direct tensor cancellation
gives N_(t_a*L)(x,y) = N_L(x+a,y) tensor N_L(a,y)^(-1). Biadditivity in
lem-sfb-abelian-space-poincare-calculus identifies this with N_L(x,y). Thus the
local homomorphisms agree and glue as maps of fppf sheaves. Refining the cover or
changing sections gives the same glued map by the same identity.
4. On an algebraically closed fibre, lem-sfb-symmetric-abel-image-geometry gives
the pointed Abel map and its normalized universal degree-zero line. Restricting
the Poincare family along the Abel map defines the retraction r from the dual:
lem-pd-degree-locally-constant makes its fibres degree zero, and biadditivity
makes r a homomorphism. The identity in lem-sfb-theta-poincare-pullback gives
r composed with phi_(O(inversion-star Theta)) composed with inversion equal to the identity
as scheme morphisms. The dual has the same dimension by
lem-sfb-abelian-polarization-calculus; apply lem-sfb-equal-dimension-abelian-retract.
5. Biadditivity shows that inversion of both variables preserves the normalized
difference, so phi for the inverse-image theta divisor equals phi for theta.
The effective-divisor ampleness criterion in
lem-sfb-abelian-polarization-calculus makes the theta line ample. The translation
identity of step 3 proves independence of the point and theta translate, in
all characteristics, without dividing by two or choosing a theta characteristic.
6. Apply lem-sfb-space-universal-isomorphism-open. Its source is flat, locally
finitely presented and universally closed, and its target is proper and finitely
presented. Every geometric point belongs to the isomorphism open, so this open is
the entire base, including when the base is empty. The polarization is an isomorphism.
7. The theta torsor and determinant pair commute with arbitrary base change by
lem-sfb-relative-degree-gminusone-theta; normalized differences and duals do so by
lem-sfb-abelian-space-poincare-calculus. Hence the pulled-back local maps glue to
the same map. For u:C ≅ D, inverse pullback transports the torsor and its theta
pair; pullback of the translation formula gives a-dual composed with lambda_D
composed with a equal to lambda_C. The Picard and normalized-dual comparisons
are characterized on all tests and are unique; identity and composition follow.
-/
theorem relativeJacobian_theta_polarization {R : Scheme.{u}} {genus : ℕ}
    (X : StablePointedModuli R genus 0) [IsLocallyNoetherian X.base.left]
    [Smooth X.projection] (J : AlgebraicSpace X.base.left)
    (e : Presentation (B := Over.mk (𝟙 X.base.left)) X.projection J
      (groupSpaceProjection J)) :
    ∃ gJ : CommutativeSpaceGroup J,
      TensorCompatible X.projection J e gJ ∧
      IsAbelianFamily (groupSpaceProjection J) ∧
      ∀ (D : AlgebraicSpace X.base.left) (gD : CommutativeSpaceGroup D)
        (P : (product (groupSpaceProjection J) (groupSpaceProjection D)).SmallModules)
        (r : Axes (pointedGroup J gJ) (pointedGroup D gD) P),
        IsAbelianFamily (groupSpaceProjection D) →
        Represents (pointedGroup J gJ) (pointedGroup D gD) P r →
        ∃! lam : J ⟶ D,
          IsHom gJ gD lam ∧ IsIso lam ∧
          GeometricTheta (B := Over.mk (𝟙 X.base.left)) X.projection genus
            (pointedGroup J gJ) (pointedGroup D gD) e P lam ∧
          UniversalThetaBaseChange X.projection genus
            (pointedGroup J gJ) (pointedGroup D gD) e P r lam ∧
          CurveIsomorphismNaturality X.projection genus J D gJ gD e P lam := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
