/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization

/-! # Maps from affine limits to affine étale objects

Source: Stacks Project, Tags 01ZC and 099S, finite presentation and affine limits.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Affine étale objects are finitely copresentable for affine inverse systems,
including systems whose index lies in a larger universe (Stacks, Tags 01ZC, 099S). -/
theorem affineEtale_largeLimit_preservesColimit {X : Scheme.{u}}
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ X.ProEt) (haff : ∀ i, IsAffine (D.obj i).left)
    (het : ∀ i, Etale (D.obj i).hom) (c : Cone D)
    (hc : IsLimit ((Scheme.ProEt.forget X).mapCone c))
    (V : X.ProEt) [IsAffine V.left] [Etale V.hom] :
    PreservesColimit D.op (coyoneda.obj (op (op V))) := by
  have hlim : IsLimit c := isLimitOfReflects (Scheme.ProEt.forget X) hc
  apply preservesColimit_of_preserves_colimit_cocone hlim.op
  apply Types.FilteredColimit.isColimitOf'
  · intro a
    obtain ⟨i, b, hb⟩ := affineEtale_largeLimit_factorization D haff het c hc V a.unop
    exact ⟨op i, b.op, congrArg Quiver.Hom.op hb.symm⟩
  · intro i a b hab
    obtain ⟨k, f, hf⟩ := affineEtale_largeLimit_eventualEquality D haff het c hc V
      i.unop a.unop b.unop (congrArg Quiver.Hom.unop hab)
    exact ⟨op k, f.op, congrArg Quiver.Hom.op hf⟩

end AlgebraicGeometry.ProEtale
