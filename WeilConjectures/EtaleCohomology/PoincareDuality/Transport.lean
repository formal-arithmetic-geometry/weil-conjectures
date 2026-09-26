/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise

/-!

# Transport through the coefficient stages

The blueprint builds the Poincaré pairing at the finite stages `A_{E,n} = 𝒪_E/ϖ^n` and then
carries it to `𝒪_E`, to `E` and to `Q̄_ℓ` by the uniform-tower reconstruction and by descent
along the common-stage construction. In this formalisation the coefficient category `A` is a
parameter of every definition and every statement, so the stages are not separate theorems:
what has to be said is that the constructions are *natural in the coefficient category*, which
is what makes the finite reduction `A_{E,n} → A_{E,m}` and the scalar extensions `𝒪_E → E`,
`E → Q̄_ℓ` carry the pairing along.

This file records that naturality for the degreewise Poincaré pairing, from which — as the
blueprint's own Step 3 observes — the derived isomorphism, the trace map and the Frobenius
statements all transport, being constructed from the pairing and the trace alone.

The comparison between two coefficient stages is taken as data: a functor `Φ : A ⥤ A'`
between the coefficient categories, its realisation `Ψ` on the derived categories of pro-étale
sheaves, and the identifications of the cohomology objects, the twist, the dual and the
monoidal structure that the comparison induces.

## Main results

- `AlgebraicGeometry.ProEtale.degreewisePoincarePairing_transport`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (A' : Type u') [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

The degreewise Poincaré pairing is natural in the coefficient stage: for a comparison
`Φ : A ⥤ A'` of coefficient categories with realisation `Ψ` on pro-étale complexes, the
pairing at the stage `A` maps to the pairing at the stage `A'` under the identifications the
comparison provides. Since the derived isomorphism, the trace map and the Frobenius statements
are all built from the pairing and the trace, they transport with it. -/
theorem degreewisePoincarePairing_transport (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (γ' : ((tateTwist A' X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A' a)
    (Φ : A ⥤ A')
    (Ψ : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A'))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (i : ℤ)
    (eTensor : Φ.obj ((H_c(a)[A](i)).obj K ⊗
        (cohomology A X (2 * d - i)).obj
          ((tateTwist A X (d : ℤ)).obj ((derivedDual A X).obj (op K)))) ≅
      Φ.obj ((H_c(a)[A](i)).obj K) ⊗
        Φ.obj ((cohomology A X (2 * d - i)).obj
          ((tateTwist A X (d : ℤ)).obj ((derivedDual A X).obj (op K)))))
    (eCompact : Φ.obj ((H_c(a)[A](i)).obj K) ≅ (H_c(a)[A'](i)).obj (Ψ.obj K))
    (eDual : Φ.obj ((cohomology A X (2 * d - i)).obj
        ((tateTwist A X (d : ℤ)).obj ((derivedDual A X).obj (op K)))) ≅
      (cohomology A' X (2 * d - i)).obj
        ((tateTwist A' X (d : ℤ)).obj ((derivedDual A' X).obj (op (Ψ.obj K)))))
    (eUnit : Φ.obj (𝟙_ A) ≅ 𝟙_ A') :
    Φ.map (degreewisePoincarePairing A a d γ K i) ≫ eUnit.hom =
      eTensor.hom ≫ tensorHom eCompact.hom eDual.hom ≫
        degreewisePoincarePairing A' a d γ' (Ψ.obj K) i :=
  sorry

end ProEtale

end AlgebraicGeometry
