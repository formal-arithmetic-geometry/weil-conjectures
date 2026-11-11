/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.AffineLineAdjunctionAssembly
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.EllAdicCycleClassDiagonal

/-!
# The projective line with rational coefficients

Let `k` be a field of characteristic `p ≠ ℓ`, let `Y` be a separated `k`-scheme of finite type
and `q : ℙ¹_Y ⟶ Y` the projection. For `Λ = E` a finite extension of `ℚ_ℓ` or `Λ = ℚ̄_ℓ`
(`c = some E` or `c = none`), blueprint `proposition-projective-line-rational-coefficients`
asserts that `q^*(1)[2]` is right adjoint to `Rq_*` on the localizing categories of bounded
constructible complexes, and hence agrees with the exceptional inverse image `q^!`.

The functors are `AlgebraicGeometry.ProEtale.RationalP1.push` (`Rq_*`) and
`AlgebraicGeometry.ProEtale.RationalP1.exceptional` (`q^*(1)[2]`), on
`Loc(D^b_c(-, Λ))`; with rational coefficients this is `Loc(D^b_ctf(-, Λ))`.

## Main statements

- `AlgebraicGeometry.ProEtale.RationalP1.nonempty_push_adjunction_exceptional`:
  `Rq_* ⊣ q^*(1)[2]` (`proposition-projective-line-rational-coefficients--1`).
- `AlgebraicGeometry.ProEtale.RationalP1.exists_rightAdjoint_iso_exceptional`:
  `q^! ≅ q^*(1)[2]` (`proposition-projective-line-rational-coefficients--2`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]

/-- Blueprint `proposition-projective-line-rational-coefficients--1`: for `Λ = E` or `ℚ̄_ℓ`,
the functor `q^*(1)[2] : Loc(D^b_ctf(Y, Λ)) ⥤ Loc(D^b_ctf(ℙ¹_Y, Λ))` is right adjoint to
`Rq_*`. -/
theorem nonempty_push_adjunction_exceptional :
    Nonempty (push l c k (ringChar k) (Fact.out : ringChar k ≠ l) Y ⊣
      exceptional l c k (ringChar k) (Fact.out : ringChar k ≠ l) Y) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsNoetherian (ProjectiveLine Y) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y ↘ Y)
  have : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  exact rationalP1_adjunction_assembly l c k Y

/-- Blueprint `proposition-projective-line-rational-coefficients--2`: for `Λ = E` or `ℚ̄_ℓ`,
`q^! ≅ q^*(1)[2]`. Precisely: for every compactification of `q` and every right adjoint `G` of
the corresponding `Rq_! : Loc(D^b_ctf(ℙ¹_Y, Λ)) ⥤ Loc(D^b_ctf(Y, Λ))` (such as the one of
`theorem-existence-exceptional-inverse-image`), `G` is isomorphic to `q^*(1)[2]` under the
identifications `Loc(D^b_ctf(-, Λ)) = Loc(D^b_c(-, Λ))`. -/
theorem exists_rightAdjoint_iso_exceptional
    (compactification : Compactification.BoundaryCompactification (ProjectiveLine Y ↘ Y))
    (h : ∀ A, localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y) A →
      localizingClosureProEtale (coefficient l c).X Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient l c).X
          compactification.obj.obj).obj A))
    (G : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ⥤
      (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory)
    (adjG : localizingLowerShriek (coefficient l c).X compactification.obj.obj h ⊣ G) :
    ∃ (eP : (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).FullSubcategory ≌
        rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y))
      (eY : (localizingClosureProEtale (coefficient l c).X Y).FullSubcategory ≌
        rationalLocalizingCategory (coefficient l c).X Y),
      Nonempty (eP.functor ⋙ rationalLocalizingInclusion (coefficient l c).X (ProjectiveLine Y) ≅
        (localizingClosureProEtale (coefficient l c).X (ProjectiveLine Y)).ι) ∧
      Nonempty (eY.functor ⋙ rationalLocalizingInclusion (coefficient l c).X Y ≅
        (localizingClosureProEtale (coefficient l c).X Y).ι) ∧
      Nonempty (G ⋙ eP.functor ≅
        eY.functor ⋙ exceptional l c k (ringChar k) (Fact.out : ringChar k ≠ l) Y) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  have : IsNoetherian (ProjectiveLine Y) :=
    isNoetherian_of_locallyOfFiniteType (ProjectiveLine Y ↘ Y)
  have : IsNoetherian (diagonalSurface Y) :=
    isNoetherian_of_locallyOfFiniteType
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  obtain ⟨family, hY, aY, aP, aW, hfamily⟩ := exists_family_isCanonical l k Y
  let := aY
  let := aP
  let := aW
  obtain ⟨D, hcompletion, hsystem, δ, hδ, ⟨reference⟩, -⟩ := hfamily
  exact (rationalP1_triangle l c k (ringChar k) (Fact.out : ringChar k ≠ l) Y hY D
    hcompletion hsystem δ hδ family reference).2.2.2.2.2 compactification h G adjG

end AlgebraicGeometry.ProEtale.RationalP1
