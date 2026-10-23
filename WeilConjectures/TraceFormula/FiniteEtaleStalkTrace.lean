/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.TraceFormula.WeilSheafLowerStar
public import WeilConjectures.TraceFormula.WeilTrace

/-!

# The Frobenius trace on a stalk of the pushforward along a finite étale morphism

Let `f : X ⟶ Y` be a finite étale morphism and `ȳ : Spec Ω ⟶ Y` a geometric point, `Ω`
separably closed. For a module object `F` on `X`, the stalk of `f_* F` at `ȳ` is the product of
the stalks of `F` at the geometric points `x̄` of `X` over `ȳ`
(`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`): the projection to the factor of `x̄` is
`ȳ^* f_* F ≅ x̄^* f^* f_* F ⟶ x̄^* F`, through the counit of `f^* ⊣ f_*`
(`ProEtale.CondensedRing.stalkLowerStarProj`).

For automorphisms `e_X`, `e_Y` with `e_X ≫ f = f ≫ e_Y` and a Weil sheaf `F` for `e_X`, the
Frobenius of the stalk of the Weil sheaf `f_* F` at a point `ȳ` with `ȳ ≫ e_Y = σ ≫ ȳ` permutes
the factors: it sends the factor of `x̄⁺` to the factor of `x̄`, where `σ ≫ x̄⁺ = x̄ ≫ e_X`
(`ProEtale.CondensedRing.stalkFrobenius_lowerStar_comp_stalkLowerStarProj`). The factors fixed by
this permutation are those of the points with `x̄ ≫ e_X = σ ≫ x̄`, on which the Frobenius is the
Frobenius of the stalk of `F`. Hence the trace of the Frobenius of the stalk of `f_* F` at `ȳ` is
the sum of the traces of the Frobenius of the stalks of `F` at these points
(`ProEtale.CondensedRing.categoricalTrace_stalkFrobenius_lowerStar`), provided the stalks
are dualizable.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme


variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (σ : Spec (.of Ω) ⟶ Spec (.of Ω))

/-- The Frobenius of the stalk at a geometric point `x̄` with `x̄ ≫ e = σ ≫ x̄` of a module object
`M` with a morphism `φ : e^* M ⟶ M`: the composite
```
x̄^* M ≅ σ^* x̄^* M ≅ (σ ≫ x̄)^* M = (x̄ ≫ e)^* M ≅ x̄^* e^* M ⟶ x̄^* M
```
of `weilStalkComparison` and `x̄^* φ`. For a Weil sheaf `(M, φ)` it is the structure morphism of
its stalk (`WeilSheaf.stalkFunctor`). -/
noncomputable def stalkFrobenius {Z : Over (Spec (.of k))} (e : Z ≅ Z) {x : Spec (.of Ω) ⟶ Z.left}
    (hx : x ≫ e.hom.left = σ ≫ x)
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)}
    (φ : (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ M) :
    (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M :=
  (weilStalkComparison ℓ e σ x hx).hom.app M ≫ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map φ

/-- The Frobenius transport `x̄'^* F ⟶ x̄^* F` of a Weil sheaf `F` for `e_X` between geometric
points with `x̄ ≫ e_X = σ ≫ x̄'`: the composite
```
x̄'^* F ≅ σ^* x̄'^* F ≅ (σ ≫ x̄')^* F = (x̄ ≫ e_X)^* F ≅ x̄^* e_X^* F ⟶ x̄^* F
```
of `upperStarIsoIdOfIsSepClosed σ`, the composition isomorphisms and `x̄^* φ_F`. For `x̄' = x̄` it
is the Frobenius of the stalk of `F` at `x̄` (`stalkFrobenius`). -/
noncomputable def weilStalkTransport {x x' : Spec (.of Ω) ⟶ X.left}
    (h : x ≫ eX.hom.left = σ ≫ x') (F : WeilSheaf ℓ eX) :
    (x')^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier ⟶
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier :=
  (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ).inv.app _ ≫
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x').inv.app _ ≫
    eqToHom (by rw [h]) ≫
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x eX.hom.left).hom.app _ ≫
    (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom

/-- The Frobenius transport at a point fixed by the twisted Frobenius is the Frobenius of the
stalk. -/
lemma weilStalkTransport_self {x : Spec (.of Ω) ⟶ X.left} (h : x ≫ eX.hom.left = σ ≫ x)
    (F : WeilSheaf ℓ eX) :
    weilStalkTransport ℓ eX σ h F = stalkFrobenius ℓ σ eX h F.str.hom :=
  sorry

/-- **The Frobenius of the stalk of a pushforward permutes the factors**: for a point `ȳ` with
`ȳ ≫ e_Y = σ ≫ ȳ` and points `x̄`, `x̄'` over `ȳ` with `x̄ ≫ e_X = σ ≫ x̄'`, the Frobenius of the
stalk of `f_* F` at `ȳ`, followed by the projection to the factor of `x̄`, is the projection to
the factor of `x̄'` followed by the Frobenius transport. -/
theorem stalkFrobenius_lowerStar_comp_stalkLowerStarProj {y : Spec (.of Ω) ⟶ Y.left}
    (hy : y ≫ eY.hom.left = σ ≫ y) {x x' : Spec (.of Ω) ⟶ X.left} (hx : x ≫ f.left = y)
    (hx' : x' ≫ f.left = y) (h : x ≫ eX.hom.left = σ ≫ x') (F : WeilSheaf ℓ eX) :
    stalkFrobenius ℓ σ eY hy ((weilSheafLowerStarComparison ℓ eX eY hf).hom.app F.carrier ≫
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom) ≫
        stalkLowerStarProj _ hx F.carrier =
      stalkLowerStarProj _ hx' F.carrier ≫ weilStalkTransport ℓ eX σ h F :=
  sorry

/-- **The Frobenius trace on a stalk of a finite étale pushforward of Weil sheaves**: for a point
`ȳ` with `ȳ ≫ e_Y = σ ≫ ȳ`, `σ` an automorphism of `Spec Ω`, the trace of the Frobenius of the
stalk of `f_* F` at `ȳ` is the sum of the traces of the Frobenius of the stalks of `F` at the
points `x̄` over `ȳ` with `x̄ ≫ e_X = σ ≫ x̄`, provided the stalks of `F` over `ȳ` are dualizable. -/
theorem categoricalTrace_stalkFrobenius_lowerStar [IsFinite f.left] [Etale f.left]
    [IsIso σ] {y : Spec (.of Ω) ⟶ Y.left} (hy : y ≫ eY.hom.left = σ ≫ y) (F : WeilSheaf ℓ eX)
    (hF : ∀ x : GeometricFibre f.left y,
      Nonempty (HasRightDual ((x.1)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier))) :
    categoricalTrace (stalkFrobenius ℓ σ eY hy
        ((weilSheafLowerStarComparison ℓ eX eY hf).hom.app F.carrier ≫
          (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom)) =
      ∑ᶠ x : {x : GeometricFibre f.left y // x.1 ≫ eX.hom.left = σ ≫ x.1},
        categoricalTrace (stalkFrobenius ℓ σ eX x.2 F.str.hom) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
