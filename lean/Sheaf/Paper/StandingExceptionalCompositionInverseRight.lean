/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.Paper.StandingExceptionalCompositionInverse

/-! # Explicit inverse candidate for the standing exceptional compositor

The inverse compact-support compositor is transposed in the reverse direction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- One inverse equation for the explicit counit-transpose candidate.
Source: thm-pur-composition-coherence, exceptional-composition isomorphism, and
pur9-def-upper-shriek-composition, the specified counit formula.
Proof: on bounded-below etale-origin objects, combine the inverse standing Hom
bijection for gf, precomposition by alpha, and the standing Hom bijections for g
and f into E_K : Hom(K,(gf)!L) ≃ Hom(K,f!g!L). The comparison is E_R(id), and the
candidate inverse is E_V.symm(id). Naturality of E in K follows by lifting maps
between etale representatives through fully faithful comparison pullback, then
using naturality of fixedCompactSupportComparisonIso and both adjunction Hom
bijections. Both R=(gf)!L and V=f!g!L lie in this class. The equation E_V(E_V.symm(id))
=id gives b ≫ c=id; applying injectivity of E_R and naturality gives c ≫ b=id.
This theorem records only the displayed one of these two equations. No smoothness,
nonempty-scheme or nonzero-ring hypothesis is used.
(blueprint: lem-pur-standing-composition-hom-inverse). -/
theorem standingExceptionalComposition_hom_inverse (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (L : DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} P.Coefficient) S) :
    standingExceptionalCompositionInverse P f g L ≫
      standingExceptionalComposition P f g L = 𝟙 _ := by sorry

end AlgebraicGeometry.ProEtale
