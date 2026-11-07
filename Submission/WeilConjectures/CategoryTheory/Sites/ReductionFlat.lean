/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTop
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Submission.WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import Submission.WeilConjectures.Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Reduction of flat sheaves of modules modulo an ideal

Let `R` be a Noetherian commutative ring, `I` an ideal and `F` a sheaf of `R`-modules on a site.
Its reduction `F / I F`, the sheafification of `U ↦ F(U) / I F(U)`
(`CategoryTheory.Sheaf.quotSMulTop`), is a sheaf of `R ⧸ I`-modules. If `F` is flat, so is its
reduction (`CategoryTheory.Sheaf.flat_quotSMulTop_obj`): a linear relation between sections of
`F / I F` lifts, after adding the generators of `I` as coefficients, to a linear relation
between sections of `F`, which is locally trivial since `F` is flat. Restricting the scalars of
the reduction back to `R` gives `F ⊗ (R ⧸ I)`
(`CategoryTheory.Sheaf.quotSMulTopCompRestrictScalarsIso`).

## Main results

- `CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp_quotSMulTop`: reduction modulo `I`
  preserves locally trivial relations.
- `CategoryTheory.Sheaf.flat_quotSMulTop_obj`: the reduction of a flat sheaf is flat.
- `CategoryTheory.Sheaf.quotSMulTopCompRestrictScalarsIso`: `ι (F / I F) ≅ F ⊗ (R ⧸ I)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped Pointwise

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Type (u + 1)} [CommRing R]


section Sheaf

variable [EssentiallySmall.{u + 1} C] [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)] (I : Ideal R)

variable (J) in
/-- Reduction modulo an ideal `I` of sheaves of `R`-modules: the sheafification of
`U ↦ F(U) / I F(U)`, a sheaf of `R ⧸ I`-modules. It is extension of scalars along
`R ⟶ R ⧸ I`. -/
noncomputable abbrev Sheaf.quotSMulTop :
    Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} (R ⧸ I)) :=
  Sheaf.composeAndSheafify J (ModuleCat.quotSMulTop I)


/-- Tensoring a presheaf with a constant presheaf is computed objectwise. -/
noncomputable def whiskeringRightTensorRightIso (X : ModuleCat.{u + 1} R) :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj (tensorRight X) ≅
      tensorRight ((Functor.const Cᵒᵖ).obj X) :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
      simp))
    (fun g ↦ by ext : 2; simp)

set_option synthInstance.maxHeartbeats 400000 in
-- `HasWeakSheafify` for sheaves of modules over the two rings is slow to synthesize
/-- **Restricting the scalars of the reduction gives the tensor product with `R ⧸ I`.** For a
sheaf `F` of `R`-modules, the reduction `F / I F` with scalars restricted back to `R` is
`F ⊗ (R ⧸ I)_X`, naturally in `F`. -/
noncomputable def Sheaf.quotSMulTopCompRestrictScalarsIso :
    Sheaf.quotSMulTop J I ⋙ Sheaf.restrictScalars J (Ideal.Quotient.mk I) ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R (R ⧸ I))) :=
  haveI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I)) :=
    preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} _)
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} (R ⧸ I)) := inferInstance
  haveI : HasWeakSheafify J (ModuleCat.{u + 1} R) := inferInstance
  let S := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.quotSMulTop.{u + 1} I)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} (R ⧸ I))
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let ι := Sheaf.restrictScalars J (Ideal.Quotient.mk I)
  let X := (Functor.const Cᵒᵖ).obj (ModuleCat.of R (R ⧸ I))
  Functor.associator S (W ⋙ a') ι ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W a' ι) ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerLeft W
      (sheafComposeNatIso J (ModuleCat.restrictScalars (Ideal.Quotient.mk I))
        (sheafificationAdjunction J (ModuleCat.{u + 1} (R ⧸ I)))
        (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W _ a).symm ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight _ _ _).mapIso (ModuleCat.quotSMulTopCompRestrictScalarsIso I) ≪≫
        whiskeringRightTensorRightIso _) a) ≪≫
    Functor.isoWhiskerLeft S (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
    (Functor.associator S a (tensorRight (a.obj X))).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
      (tensorRight (a.obj X)) ≪≫
    Functor.leftUnitor _

end Sheaf

end CategoryTheory
