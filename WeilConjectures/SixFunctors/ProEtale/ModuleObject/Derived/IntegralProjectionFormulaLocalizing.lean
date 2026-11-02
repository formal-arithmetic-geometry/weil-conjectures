/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperProjectionFormula

/-!
# Integral proper projection formula on localizing closures

Source: blueprint latest, `sk-thm-sf-pf-adic`, node `sk-thm-sf-pf-adic`,
unit statement (blueprint: sk-thm-sf-pf-adic).
The schemes and morphisms are in the standing setting of `sk-def-sfb-dc-setting`:
separated schemes of finite type over a field of positive characteristic different from `ell`.

The canonical projection morphism for a proper morphism is an isomorphism when both
arguments belong to the localizing closure of bounded constructible finite-Tor
complexes with coefficients in the valuation ring of a finite extension of
`\mathbb Q_\ell`. The proof extends the bounded constructible projection formula in
both variables by the localizing determination argument.
-/

@[expose] public section

set_option autoImplicit false

attribute [local instance 1]
  AlgebraicGeometry.ProEtale.CondensedRing.ProjectionMorphismData.category

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

/-- For a proper morphism, the canonical integral projection map is invertible on
localizing closures of bounded constructible finite-Tor complexes.

Source: blueprint latest, `sk-thm-sf-pf-adic`, unit statement, order 370
(blueprint: sk-thm-sf-pf-adic). Proof:
1. On bounded constructible finite-Tor inputs, apply the projection clause of
   `sk-thm-sfb-proper-base-change` to the admissible coefficient `O_E` and to the
   specified canonical adjunction mate.
2. Every standing scheme is qcqs. The integral comparison identifies Dctf with Dbc.
   Tensor preserves Dbc by `sk-lem-int-tensor`. For a fixed generator, the objects
   whose tensor lies in Loc form a replete triangulated coproduct-closed subcategory,
   since tensor is exact and preserves coproducts. Minimality of Loc gives tensor
   closure in the first variable; fixing its arbitrary object and repeating gives
   tensor closure in the second variable.
3. Proper direct image maps Loc to Loc and preserves coproducts by
   `sk-prop-proper-image-localizing`. Pullback is exact and preserves coproducts;
   its preservation of the generators extends to Loc by minimality. For a fixed
   second generator, both sides of the projection map are exact coproduct-preserving
   functors of the first localizing variable. The canonical map is natural and shift
   compatible, and step 1 makes it invertible on the generators. Apply
   `sk-lem-sf-determination`, then fix the now arbitrary first input and apply that
   lemma in the second variable. This proves invertibility for both localizing inputs.
-/
theorem isIso_integral_projection_formula_localizing
    (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left]
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.val) X.left)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E.val) Y.left)))
    (hM : localizingClosureProEtale
      (Profinite.padicIntegersRingObj ell E.val) X.left M)
    (hN : localizingClosureProEtale
      (Profinite.padicIntegersRingObj ell E.val) Y.left N) :
    IsIso (moduleObjectProjectionMap
      (Profinite.padicIntegersRingObj ell E.val) p.left M N) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ell E.val
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := inferInstanceAs
    (LocallyOfFiniteType X.hom)
  let : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs
    (QuasiCompact X.hom)
  let : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs
    (IsSeparated X.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := inferInstanceAs
    (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs
    (QuasiCompact Y.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs
    (IsSeparated Y.hom)
  let : p.left.IsOver (Spec (.of k)) := ⟨p.w⟩
  have hctf (T : Over (Spec (.of k))) [QuasiCompact T.hom] [IsSeparated T.hom] :
      (constantModelBoundedConstructible Λ T.left ⊓
        DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T.left := by
    have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
    have : QuasiSeparatedSpace T.left :=
      quasiSeparatedSpace_of_quasiSeparated T.hom
    exact (localizingClosure_ctf_equals_bc ell T.left Λ (by
      exact Or.inr (Or.inr (Or.inl ⟨E, Or.inl (Nonempty.intro (Iso.refl _))⟩)))).1.2.2.1
  have hloc (T : Over (Spec (.of k))) [QuasiCompact T.hom] [IsSeparated T.hom] :
      localizingClosureProEtale Λ T.left =
        CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ T.left) := by
    unfold localizingClosureProEtale
    rw [hctf T]
  rw [hloc X] at hM
  rw [hloc Y] at hN
  exact (integralProperProjectionFormula ell E k p.left).2.2 M N hM hN

end AlgebraicGeometry.ProEtale.CondensedRing
