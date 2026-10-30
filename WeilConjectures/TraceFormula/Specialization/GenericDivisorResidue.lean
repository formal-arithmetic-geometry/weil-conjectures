/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Reduction
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorLisse

/-!

# Generic vanishing along a divisor for finite coefficients

Let `X` be normal, `Z = V(h)` a principal divisor with complement `j : X ∖ Z ⟶ X`, `ζ` a generic
point of `Z`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with residue field `𝔽_E`, and `F` a bounded
constructible complex of `𝔽_E`-module objects on `X ∖ Z`. The restriction `Le^* Ψ_X(j_! F)` of the
nearby cycles of the deformation to the normal cone to the zero section vanishes over a
neighbourhood of `ζ`
(`ProEtale.CondensedRing.exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField`). This is
blueprint `det-sp-generic-divisor` for finite coefficients and complexes `L = j_! F` with
`Li^* L = 0`.

## Unfinished

The statement is `sorry`ed. Its blueprint proof works with finite coefficients throughout: after
shrinking `X` around `ζ`, `F` is lisse up to a finite étale cover of `X ∖ Z` (a finite étale
trivialisation), which extends to a finite cover of `X` by normalisation; the exchange of nearby
cycles with the proper pushforward along this cover reduces to the constant case, which is the
computation of the nearby cycles of the deformation `x = t u` along the divisor, and the general
case follows by induction on the degree of the cover. None of these steps is available for the
pro-étale nearby cycles of this formalism.

-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Generic vanishing along a divisor for finite coefficients** (blueprint
`det-sp-generic-divisor` with coefficients `𝔽_E`, for extensions by zero from the complement of
the divisor): let `X` be normal, `Z = V(h)` for a nonzero global function `h`,
`j : X ∖ Z ⟶ X` the complement, `ζ` a generic point of an irreducible component of `Z`, and `F` a
bounded constructible complex of `𝔽_E`-module objects on `X ∖ Z`. Then `Le^* Ψ_X(j_! F)` vanishes
over a neighbourhood of `ζ`. Unfinished: its proof (finite étale trivialisation of `F` near `ζ`,
normalisation, proper exchange, the constant case and induction on the degree) is not
formalised. -/
theorem exists_isZero_upperStar_nearbyCycles_lowerShriek_residueField
    [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (F : DerivedCategory (Mod (Sheaf (ProEt.topology (overRestrict X I.support.compl).left)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))
        (overRestrict X I.support.compl).left)))
    (hF : boundedConstructible _ F) :
    ∃ U : (centre X I).left.Opens, ζ ∈ U ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj
        (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj
          (((deformationModel X I k').nearbyCycles
            (Profinite.continuousMapRingObj (integersResidueField ℓ E.1))).obj
            (D(((overRestrictι X I.support.compl).left)_!open⟦
              Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧).obj F)))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
