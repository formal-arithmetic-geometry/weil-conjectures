/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.ForgetCohomologyVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalVanishing

/-!
# Higher cohomology of the affine line over a strictly henselian local ring

Let `R` be a strictly henselian local ring, `Λ` a finite coefficient ring whose exponent is
invertible on `S = Spec R`, `p : 𝔸¹_S ⟶ S` the affine line and `M` a locally constant sheaf of
`Λ`-modules on `S`. This file reduces the vanishing of `Hᵠ(𝔸¹_R, p^* M)` for `q ≥ 2`
(SGA 4 XV 2.1–2.2, Fu, *Étale cohomology theory*, 7.4, Milne, *Étale cohomology*, VI.4) to the
vanishing of the higher direct images `Rᵠp_*(p^* M)`
(`AlgebraicGeometry.Etale.isZero_cohomology_affineLine_of_isZero_higherDirectImage`).

## The argument

The global sections functor of the strictly local scheme `S` is exact and computes the stalk at
the closed geometric point `t` of `S`. Hence the Leray isomorphism `RΓ(𝔸¹_S, -) ≅ RΓ(S, Rp_* -)`
identifies `Hᵠ(𝔸¹_S, F)` with `Γ(S, Rᵠp_* F)`, which vanishes as soon as the stalk of `Rᵠp_* F`
at `t` does (`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_sheafFiber_higherDirectImage`).
This reduces the statement to the vanishing of the higher direct images `Rᵠp_*(p^* M)` for
`q ≥ 2`, the sheaf form of SGA 4 XV 2.2 in degrees `≥ 2`, which is taken as a hypothesis.

Note that the vanishing of `Rᵠp_* G` for `q ≥ 2` fails for general (non locally constant)
torsion sheaves `G` on `𝔸¹_S` over a base of positive dimension: the relative affine vanishing
theorem only bounds `Rᵠp_*` by the dimension of `𝔸¹_S`, not by the relative dimension (compare
`AlgebraicGeometry.Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom`, Stacks 0F0X).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The cohomology `Hᵠ(X, G)` of a sheaf of `Λ`-modules placed in degree `0`, computed in
`D(Λ)`, vanishes if and only if the cohomology of the underlying abelian sheaf does
(Stacks 03FD). -/
theorem isZero_cohomology_singleFunctor_iff_subsingleton_H (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) ↔
      Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj G) q) := by
  obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
  obtain ⟨e'⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  refine ModuleCat.isZero_iff_subsingleton.trans ((AddCommGrpCat.isZero_iff_subsingleton
    (G := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj _)).symm.trans
    (Iff.trans ?_ (AddCommGrpCat.isZero_iff_subsingleton
      (G := (Sheaf.functorH X.smallEtaleTopology q).obj ((sheafForget₂ Λ X).obj G)))))
  exact ⟨fun h ↦ h.of_iso (e'.app _ ≪≫ (e.app G).symm),
    fun h ↦ h.of_iso (e.app G ≪≫ (e'.app _).symm)⟩

end Etale

end AlgebraicGeometry
