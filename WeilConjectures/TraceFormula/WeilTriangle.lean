/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Additivity
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar

/-!

# Distinguished triangles of Weil objects

A triangle of Weil objects is distinguished
(`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang`) if it extends to a distinguished
triangle of the ambient derived category whose connecting morphism commutes with the Frobenius
structures. The local trace is additive along such triangles
(`ProEtale.CondensedRing.weilStalkSupertrace_eq_add_of_isDistTriang`), the lower shriek of Weil
objects preserves them
(`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map`), and the
localization triangle `j_! j^* K ⟶ K ⟶ i_* i^* K ⟶` is one
(`ProEtale.CondensedRing.exists_isDistTriang_openClosed`).

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y W : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) (eW : W ≅ W)


/-- A triangle `A ⟶ B ⟶ C` of Weil objects for `Φ` is *distinguished* if it extends to a
distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of the ambient derived category `D(Mod_{ℚ̲̄_ℓ,X})`
whose connecting morphism `δ` commutes with the Frobenius structures: `δ ∘ φ_C = φ_A[1] ∘ LΦ^* δ`,
where `LΦ^* δ` is formed through the ambient derived pullback, which commutes with the
shifts. -/
def WeilBoundedConstructible.IsDistTriang {V : Over (Spec (.of k))} [LocallyOfFiniteType V.hom]
    [QuasiCompact V.hom] [IsSeparated V.hom] {Φ : V ⟶ V} {A B C : WeilBoundedConstructible ℓ Φ}
    (a : A ⟶ B) (b : B ⟶ C) : Prop :=
  ∃ δ : (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
      C.carrier ⟶ (shiftFunctor _ (1 : ℤ)).obj
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.obj
          A.carrier),
    Pretriangulated.Triangle.mk
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
          a.hom.f)
        ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
          b.hom.f) δ ∈ Pretriangulated.distinguishedTriangles ∧
      (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
          C.str.hom ≫ δ =
        connectingOfIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι
            (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι
            L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
            (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ) δ ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V.left)).ι.map
              A.str.hom)

/-- **Additivity of the local trace along distinguished triangles of Weil objects** (standard
input, still `sorry`): for a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` of Weil objects for `e`,
`t_{n+1}(B; x̄) = t_{n+1}(A; x̄) + t_{n+1}(C; x̄)`. The long exact sequence of homology sheaves
`Hʲ(A) ⟶ Hʲ(B) ⟶ Hʲ(C) ⟶ Hʲ⁺¹(A)` is one of Weil sheaves, the connecting morphisms commuting with
the Frobenius structures; the stalk functor at `x̄` is exact, the stalks of the homology sheaves of
constructible complexes are finite-dimensional `ℚ̄_ℓ`-vector spaces, and the alternating sum of
the traces of an endomorphism of a bounded exact sequence of finite-dimensional vector spaces
vanishes. -/
theorem weilStalkSupertrace_eq_add_of_isDistTriang {e : Y ≅ Y} (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ Y.left)
    (hx : x ≫ (e.powSucc n).hom.left = ((geometricFrobeniusField k).powSucc n).hom ≫ x)
    {A B C : WeilBoundedConstructible ℓ e.hom} {a : A ⟶ B} {b : B ⟶ C}
    (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    weilStalkSupertrace ℓ n x hx B =
      weilStalkSupertrace ℓ n x hx A + weilStalkSupertrace ℓ n x hx C :=
  sorry

/-- **The lower shriek of Weil objects preserves distinguished triangles** (standard input, still
`sorry`): `Rf_!` is a triangulated functor (`R(f)_!` on the ambient derived categories commutes
with the shifts and is triangulated), and the compact-support base change isomorphism giving the
Frobenius structure of `Rf_!^Weil` commutes with the shifts, so the image of the connecting
morphism commutes with the Frobenius structures. -/
theorem WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map {f : X ⟶ Y}
    (hf : eX.hom ≫ f = f ≫ eY.hom) {A B C : WeilBoundedConstructible ℓ eX.hom} {a : A ⟶ B}
    {b : B ⟶ C} (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    WeilBoundedConstructible.IsDistTriang ℓ ((weilLowerShriek ℓ eX eY hf).map a)
      ((weilLowerShriek ℓ eX eY hf).map b) :=
  sorry


variable {U Z : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (eU : U ≅ U) (eZ : Z ≅ Z) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
  {j : U ⟶ X} {i : Z ⟶ X} [IsOpenImmersion j.left] [IsClosedImmersion i.left]
  (hj : eU.hom ≫ j = j ≫ eX.hom) (hi : eZ.hom ≫ i = i ≫ eX.hom)

/-- **The localization triangle of Weil objects** (standard input, still `sorry`, blueprint
`prop-sf-open-closed-triangle-all-stages` and `prop-trf-trace-additivity-open-closed`, Step 2):
for an open immersion `j` with closed complement `i`, both stable under `e_X`, the counit
`Rj_! Lj^* K ⟶ K` and the unit `K ⟶ Ri_* Li^* K = Ri_! Li^* K` are morphisms of Weil objects and
extend to a distinguished triangle of Weil objects. The triangle is
`ProEtale.CondensedRing.exists_distTriang_openClosed`; the Frobenius compatibility of the
connecting morphism is `ProEtale.CondensedRing.map_comp_connecting_eq_of_isCompl`. -/
theorem exists_isDistTriang_openClosed
    (hcompl : IsCompl (Set.range j.left.base) (Set.range i.left.base))
    (K : WeilBoundedConstructible ℓ eX.hom) :
    ∃ (α : (weilLowerShriek ℓ eU eX hj).obj ((weilUpperStar ℓ eU.hom eX.hom j hj).obj K) ⟶ K)
      (β : K ⟶ (weilLowerShriek ℓ eZ eX hi).obj ((weilUpperStar ℓ eZ.hom eX.hom i hi).obj K)),
      WeilBoundedConstructible.IsDistTriang ℓ α β :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
