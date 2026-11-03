/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedDualTateCompatibility.DualTateCompatibilityData

/-! # Scalar change of native perfect dual and tensor data

Source: latest blueprint, proof Step 5 of
prop-pod-dual-tate-data-compatibility.
(blueprint: lem-pod-scalar-closed-tensor-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.CondensedDualTateCompatibility
variable (P : CondensedPoincareDualityConventions.{u})

set_option maxHeartbeats 1200000 in
-- The statement elaborates the native scalar, closed and derived module instances.
/-- Scalar change of native perfect dual and tensor data.

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md, Step 5
(blueprint: lem-pod-scalar-closed-tensor-compatibility).

Proof in words:
1. The source and target structural coefficient maps commute with Frobenius:
   after restriction to any object, coefficient naturality says that applying
   the ring map before or after the structural identification gives the same
   action. The ordinary scalar/pullback comparison sends a balanced tensor to
   the corresponding balanced tensor. Both orders of its tensor square agree
   on pure tensors, and the unit square sends the coefficient unit to the
   coefficient unit. Check this for the actual normalized comparison, rather
   than choosing some monoidal comparison with the same source and target.
2. Resolve by flat-term K-flat complexes. The preceding ordinary equality
   passes through the canonical derived factor maps. Normalization of the
   inverse-image mate identifies it with scalarPullbackIso; transportation
   through leftDerivedUpperStarIsoMapDerivedCategory identifies its monoidal
   structures with the chosen StrictWeilCondensed.action structures. This
   proves the tensor and unit equations for scalarFrobenius.
3. For site-perfectness keep the original pro-etale cover. Apply ordinary
   extension of scalars termwise to each bounded finite-projective complex.
   It preserves a retraction onto a finite free module, so the new terms are
   finite projective. Such bounded complexes are K-flat, and the normalized
   scalar/pullback comparison identifies their scalar extensions with the
   restrictions of T(K). Bounds and the cover are unchanged.
4. Uncurry the two alleged dual-datum maps. Insert the defining transpose
   identity for ihomUnitComparison, and the source and target equivariant
   evaluation identities. The tensor and unit squares from step 2 identify
   the two evaluations. The closed adjunction is injective on transposes,
   giving the dual equation. This uses ordinary derived extension even for
   nonflat reduction; no coefficient reduction is used to detect equality.
5. For an arbitrary intertwiner m from T(M) to N, expand the two tensor data
   and the scalar datum. The tensor square from step 2 moves the inverse
   scalar/Frobenius comparison past the tensorator. Naturality of T's and
   target Frobenius's tensorators then moves v and m into their separate
   slots. Apply step 4 in the first slot and the hypothesis on m in the
   second slot, then recombine the tensor morphisms.
-/
theorem scalarClosedCompatibility (c c' : Coefficient P.ell)
    (a : c.bundled.{u} P.ell ⟶ c'.bundled P.ell)
    (ha : IsListedScalarCoefficientMap P.ell a)
    (K : c.derived P.ell P.X) (hK : property P.ell c P.X K)
    (hp : IsPerfectOnCoefficientSite (c.obj P.ell) P.X K)
    (phi : (StrictWeilCondensed.action (c.obj P.ell) (geometric P)).obj K ≅ K) :
    let T := scalarSixChange a P.X
    letI : T.Monoidal := scalarSixChangeMonoidal a P.X
    let F' := StrictWeilCondensed.action (c'.obj P.ell) (geometric P)
    let V := StrictWeilCondensed.dual (c.obj P.ell) K
    let b := StrictWeilCondensed.dualDatum (c.obj P.ell) (geometric P) K phi
    let phi' := scalarDatum P c' a K phi
    let b' := StrictWeilCondensed.dualDatum (c'.obj P.ell) (geometric P) (T.obj K) phi'
    let v := ihomUnitComparison T K
    IsPerfectOnCoefficientSite (c'.obj P.ell) P.X (T.obj K) ∧
    (scalarDatum P c' a V b).hom ≫ v = F'.map v ≫ b'.hom ∧
    ∀ (M : c.derived P.ell P.X) (N : c'.derived P.ell P.X)
      (tau : (StrictWeilCondensed.action (c.obj P.ell) (geometric P)).obj M ≅ M)
      (tau' : F'.obj N ≅ N) (m : T.obj M ⟶ N),
      (scalarDatum P c' a M tau).hom ≫ m = F'.map m ≫ tau'.hom →
      let t := (scalarSixTensorIso a P.X V M).hom ≫ (v ⊗ₘ m)
      (scalarDatum P c' a _
        (StrictWeilCondensed.tensorDatum (c.obj P.ell) (geometric P) b tau)).hom ≫ t =
        F'.map t ≫ (StrictWeilCondensed.tensorDatum (c'.obj P.ell) (geometric P)
          b' tau').hom := by
  sorry

end WeilConjectures.CondensedDualTateCompatibility
