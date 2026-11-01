/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.SetGeneratedDerivedBrown
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
/-- Brown representability on the characteristic-free localizing closure.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-purity-transport/sk-thm-purity-transport.proof.md, General-field localizing tools,
Step 5. The intended proof is: (1) use the structural Brown hypotheses to obtain the
triangulated structure, ambient coproducts, local smallness, and idempotent completeness of
the target closure; (2) use essential smallness of the bounded constructible finite-Tor
subcategory to choose a small skeleton and regard its inclusion as a family of ambient
derived objects; (3) prove that the localizing closure of the range of this family equals
`localizingClosureProEtale` by the two minimality inclusions; (4) transport the given
homological functor across this equality and apply `setGeneratedDerivedBrownRepresentability`,
whose product hypothesis is exactly preservation of the indexed products in the interface;
(5) transport the representing object and reverse the natural isomorphism to obtain
`H ≅ preadditiveYoneda.obj G` in the target closure.
(blueprint: lem-dla1-general-field-brown-representability). -/
theorem localizingBrownRepresentability
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [PerfectField k] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))] :
    ∀ (H : (localizingClosureProEtale Λ S).FullSubcategoryᵒᵖ ⥤
      AddCommGrpCat.{u + 1}), BrownRepresentableOnLocalizingClosure Λ S H := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing
