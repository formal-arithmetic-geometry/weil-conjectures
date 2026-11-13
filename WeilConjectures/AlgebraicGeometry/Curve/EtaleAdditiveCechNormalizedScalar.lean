/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalData
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechCommonRepresentative
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechScalarTransport
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Scalar action on normalized additive étale Čech edges
Source: Stacks Project, Tags 03P2 and 01EQ. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Augmentation-normalized edges intertwine multiplication with scalar action.
Source: Stacks Project, Tag 03P2, the coefficient edge, and Tag 01EQ,
functoriality of the augmented injective Čech double complex in coefficients. -/
theorem etaleAdditiveCech_normalized_scalar
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (μ : Γ(X, ⊤) → (X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf))
    (hμ : ∀ r (W : X.Etaleᵒᵖ) (x : X.etaleAdditiveSheaf.obj.obj W),
      (μ r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (n : ℕ)
    (a : Sheaf.H X.etaleAdditiveSheaf n ≃+
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n)
    (ha : IsEtaleAdditiveCechNormalized U n a) :
    ∀ r x, a (Sheaf.H.map (μ r) n x) = r • a x := by
  classical
  intro r x
  let I := injectiveResolution X.etaleAdditiveSheaf
  obtain ⟨c⟩ := Etale.exists_resolutionSection_canonical_comparison X.etaleAdditiveSheaf I
  obtain ⟨s, hs⟩ :=
    (AddCommGrpCat.epi_iff_surjective ((additiveCechGlobal I).homologyπ n)).mp
      inferInstance ((c.globalEquiv n).symm x)
  have hx : c.globalEquiv n ((additiveCechGlobal I).homologyπ n s) = x := by
    rw [hs, AddEquiv.apply_symm_apply]
  obtain ⟨z, tα, tβ, hα, hβ, ht⟩ :=
    additiveCech_common_representative X U hU hcover I n s
  have haz := ha I c s z tα tβ hα hβ ht
  rw [hx] at haz
  obtain ⟨s', z', tα', tβ', hα', hβ', ht', hs', hz'⟩ :=
    additiveCech_scalar_transport X U μ hμ I c n r s z tα tβ hα hβ ht
  have haz' := ha I c s' z' tα' tβ' hα' hβ' ht'
  rw [hs', hx, hz', ← haz] at haz'
  exact haz'

end AlgebraicGeometry.Scheme.Modules
