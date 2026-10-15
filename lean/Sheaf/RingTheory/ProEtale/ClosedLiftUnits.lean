/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.RingTheory.ProEtale.ClosedLiftMap

/-! # Units of the ind-etale closed lift

Source: blueprint, smooth purity, `sk-prop-sf-open-closed-triangle`,
`lem-exc-closed-lift-units` (blueprint: lem-exc-closed-lift-units).
-/

@[expose] public section

universe u

namespace Algebra.ClosedLift

/-- An element of the closed lift is a unit if its image in the input algebra is a unit.
Source: blueprint `lem-exc-closed-lift-units`, statement and proof
(blueprint: lem-exc-closed-lift-units).

Proof: use the small presentation indexing category of `def-exc-ind-etale-closed-lift`.
It is filtered by `lem-exc-closed-lift-filtered`. The algebra colimit is also a ring colimit:
a compatible family of ring maps has a common restriction to A, by filteredness, so the
algebra-colimit universal property applies. By `lem-pc-filtered-colimit-commrings-elementwise`,
choose a representative b in an etale finitely presented stage B mapping to the element h.
Its image in C is a unit. By `def-weil-ring-localization-away` and
`lem-weil-pbc-ring-localization-universal-property`, the map B to C extends to B[1/b],
and this extension is an A-algebra map. By
`lem-weil-pbc-etale-algebra-finite-presentation-localization`, B[1/b] is again etale and
finitely presented over A, hence another index, with transition B to B[1/b]. Cocone
compatibility identifies the image of b/1 with h. The image of 1/b is an inverse for h,
since applying the cocone ring map to both inverse identities preserves them. -/
theorem isUnit_of_isUnit_toAlgHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] (h : Algebra.ClosedLift A C)
    (hh : IsUnit (toAlgHom A C h)) : IsUnit h := by
  classical
  obtain ⟨X, b, hb⟩ : ∃ (X : Index A C) (b : X.alg),
      (CategoryTheory.Limits.colimit.ι (diagram A C) X).hom b = h :=
    CategoryTheory.Limits.Concrete.colimit_exists_rep (diagram A C) h
  have hbC : IsUnit (X.toC b) := by
    have he : toAlgHom A C ((CategoryTheory.Limits.colimit.ι (diagram A C) X).hom b) = X.toC b :=
      DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom
        (CategoryTheory.Limits.colimit.ι_desc (coconeC A C) X)) b
    exact ((congrArg (toAlgHom A C) hb).symm.trans he) ▸ hh
  let B := Localization.Away b
  let β : B →ₐ[A] C := IsLocalization.Away.liftAlgHom b hbC
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let e : (MvPolynomial (Fin n) A ⧸ RingHom.ker f.toRingHom) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  let Y : Index A C :=
    ⟨n, RingHom.ker f.toRingHom, Algebra.Etale.of_equiv e.symm, β.comp e.toAlgHom⟩
  let loc : X.alg →ₐ[A] B := IsScalarTower.toAlgHom A X.alg B
  let g : Index.Hom X Y := ⟨e.symm.toAlgHom.comp loc, by
    ext x
    change β (e (e.symm (algebraMap X.alg B x))) = X.toC x
    rw [e.apply_symm_apply]
    exact IsLocalization.Away.lift_eq b hbC x⟩
  have hu : IsUnit (g.hom b) :=
    (IsLocalization.Away.algebraMap_isUnit b (S := B)).map e.symm.toAlgHom
  have hw := CategoryTheory.ConcreteCategory.congr_hom
    (CategoryTheory.Limits.colimit.w (diagram A C) g) b
  change (CategoryTheory.Limits.colimit.ι (diagram A C) Y).hom (g.hom b) =
    (CategoryTheory.Limits.colimit.ι (diagram A C) X).hom b at hw
  rw [← hb, ← hw]
  exact hu.map (CategoryTheory.Limits.colimit.ι (diagram A C) Y).hom

end Algebra.ClosedLift
