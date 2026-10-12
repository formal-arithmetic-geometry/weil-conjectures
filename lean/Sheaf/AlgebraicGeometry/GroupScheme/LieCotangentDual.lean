/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
import Sheaf.AlgebraicGeometry.RationalPointTangentDerivationIdentification
import Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue
import Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv

/-!
# The Lie algebra and the cotangent dual at the identity

Source: blueprint `sk-i-cartier`, third paragraph, and the dimension paragraph of
`lem-wf-same-lie-closed-subgroup`.
(blueprint: lem-ag-lie-identity-cotangent-dual)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

private noncomputable def cotangentDualScalarEquiv
    {k K : Type u} [Field k] [Field K] (r : k ≃+* K)
    (M : Type u) [AddCommGroup M] [Module K M] :
    letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv r
    letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
      RingHomInvPair.of_ringEquiv r.symm
    letI : Module k M := Module.compHom M r.toRingHom
    (M →ₗ[k] k) ≃ₛₗ[r.toRingHom] (M →ₗ[K] K) := by
  letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv r
  letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
    RingHomInvPair.of_ringEquiv r.symm
  letI : Module k M := Module.compHom M r.toRingHom
  let f : (M →ₗ[k] k) →ₛₗ[r.toRingHom] (M →ₗ[K] K) :=
    { toFun := fun φ ↦
        { toFun := fun m ↦ r (φ m)
          map_add' := by intros; simp
          map_smul' := by
            intro c m
            have h := φ.map_smul (r.symm c) m
            change φ (r (r.symm c) • m) = r.symm c * φ m at h
            rw [r.apply_symm_apply] at h
            rw [h, map_mul, r.apply_symm_apply]
            rfl }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro φ ψ h
    ext m
    exact r.injective (congrArg (fun L : M →ₗ[K] K ↦ L m) h)
  · intro ψ
    let φ : M →ₗ[k] k :=
      { toFun := fun m ↦ r.symm (ψ m)
        map_add' := by intros; simp
        map_smul' := by
          intro c m
          change r.symm (ψ (r c • m)) = c * r.symm (ψ m)
          rw [ψ.map_smul, smul_eq_mul, map_mul, r.symm_apply_apply] }
    exact ⟨φ, by ext m; exact r.apply_symm_apply (ψ m)⟩

/-- The Lie algebra is the dual of the cotangent space at the rational identity, with
scalars transported by the residue-field identification. No smoothness is required.

Source: blueprint `sk-i-cartier`, third paragraph, and
`lem-wf-same-lie-closed-subgroup`, dimension paragraph; Stacks Project, Tag 0B2C.
(blueprint: lem-ag-lie-identity-cotangent-dual)

Proof: Put `x = e(Spec k)` and `R = O(G,x)`. The section equation `e ≫ p = id`
identifies the residue field at `x` with `k`: the composite from `k` to the residue
field and back along `e` is the identity, and the map back is an injective map of
fields. The structural residue map is therefore bijective; let `r` be this ring
isomorphism. An infinitesimal point of the group is a dual-number morphism whose
restriction is `e`. Transport the dual numbers along `r` to identify these with the
rational tangent vectors at `x`. The library equivalence `lieEquiv` identifies the
infinitesimal points with `Lie G`; its multiplication-to-addition and scaling
identities identify the additive and scalar structures. Rational tangent-cotangent
duality identifies these tangent vectors with the `k`-linear dual of `m/m²`, by
taking the epsilon coefficient of the induced stalk map. Transport the values of
a functional by `r` to obtain the residue-field-linear dual. These identifications
compose to the asserted semilinear equivalence. Each inverse is given by the
inverse construction (a functional defines the local map `a ↦ residue(a) + D(a) ε`),
so the equivalence is bijective. More explicitly, let `i : k → R` be the structural
map and write `a₀ = a - i (r.symm (residue a))`, which lies in the maximal ideal.
For a residue-field-linear functional `φ`, set `D(a) = φ([a₀])`. Modulo the square
of the maximal ideal, `(ab)₀ = residue(a) b₀ + residue(b) a₀`, so this defines a
relative derivation and the stated local dual-number map. Its image lies at `x`,
hence an affine neighbourhood of `x` reconstructs the scheme morphism; this is
independent of the neighbourhood. Differentiating group multiplication at `(e,e)`
sends `(v,w)` to `v+w`: its restrictions to either factor are the identity by the
unit laws, and its differential is linear. Thus the group law on infinitesimal
points agrees with addition of functionals. Scaling epsilon scales the functional,
so the composed bijection is semilinear for the displayed ring isomorphism.
This argument includes cotangent space zero and requires neither finite dimension
nor regularity. -/
theorem exists_lie_identity_cotangent_dual_equiv
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let R := G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))
    ∃ r : k ≃+* IsLocalRing.ResidueField R,
      letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
        RingHomInvPair.of_ringEquiv r
      letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
        RingHomInvPair.of_ringEquiv r.symm
      Nonempty (Lie G ≃ₛₗ[r.toRingHom]
        Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let R := G.left.presheaf.stalk x
  let K := G.left.residueField x
  let ρ : k →+* K :=
    (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
  have hρ : Function.Bijective ρ := (identity_residue_rational G).1
  let r : k ≃+* K := RingEquiv.ofBijective ρ hρ
  let : RingHomInvPair r.toRingHom r.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv r
  let : RingHomInvPair r.symm.toRingHom r.toRingHom :=
    RingHomInvPair.of_ringEquiv r.symm
  let : Module k (schemeTangentSpace k G.left G.hom x) :=
    Module.compHom (schemeTangentSpace k G.left G.hom x) ρ
  let : Module K (IsLocalRing.CotangentSpace R) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
  let : Module k (IsLocalRing.CotangentSpace R) :=
    Module.compHom (IsLocalRing.CotangentSpace R) ρ
  obtain ⟨E⟩ := exists_lie_identity_tangent_linearEquiv G
  obtain ⟨F, _⟩ := exists_rationalPoint_tangent_cotangent_linearEquiv
    k G.left G.hom x hρ
  exact ⟨r, ⟨(E.trans F).trans (cotangentDualScalarEquiv r _)⟩⟩

end AlgebraicGeometry.GrpObj
