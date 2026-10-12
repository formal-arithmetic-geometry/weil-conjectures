module
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue
@[expose] public section
universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry.GrpObj
/-- The Lie algebra identifies linearly with the scheme tangent space at the identity.
Source: `lem-ag-lie-identity-cotangent-dual`, infinitesimal-point identification;
blueprint `sk-i-cartier`, third paragraph, and `sk-d-tangent`.
(blueprint: lem-ag-lie-identity-tangent-equiv)

Proof: Use `lieEquiv.symm` to pass from a Lie vector to an infinitesimal point on
`(Spec k)[epsilon]`. The library isomorphism `dualNumbersToSpecOver` identifies
this with a morphism from `Spec k[epsilon]` reducing to the identity section.
The identity section is rational. Its structural residue-field map is an isomorphism:
compose it with the residue map induced by the section; the section equation makes
this composite the identity, and a field map is injective. Transport both coefficients
of dual numbers by this isomorphism. The reducing-to-the-identity condition becomes
the canonical-residue-point condition in `schemeTangentSpace`; the over-morphism
condition becomes its base condition. Transport back to get the inverse.
The group multiplication of infinitesimal points is tangent-vector addition: the
pushout defining addition maps to the product of the two points, since multiplication
restricts to the identity on each factor by the unit laws. `lieEquiv_mul` therefore
proves additivity. Scaling epsilon is the prescribed tangent scalar action, and
`toLie_infPointsScale` proves compatibility with k-scalars, including the global
sections identification `Scheme.ΓSpecIso`. These identities make the bijection linear.
No smoothness, finite type, or finite-dimensional assumption is used. -/
theorem exists_lie_identity_tangent_linearEquiv
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let r : k →+* G.left.residueField x :=
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
    letI : Module k (schemeTangentSpace k G.left G.hom x) :=
      Module.compHom (schemeTangentSpace k G.left G.hom x) r
    Nonempty (Lie G ≃ₗ[k] schemeTangentSpace k G.left G.hom x) := by sorry
end AlgebraicGeometry.GrpObj
