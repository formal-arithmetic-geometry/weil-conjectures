/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence

/-!
# The Lefschetz-Verdier pairing, trace classes and local terms

For an opposite pair of correspondences `(C, c, u)` from `(X, K)` to `(Y, L)` and
`(D, d, v)` back, the Kuenneth-Verdier comparison turns the two coefficient maps into
sections over the intersection `E(C, D) = C ×_{Y × X} D`, and their contraction is the
Lefschetz-Verdier pairing `⟨u, v⟩_LV : A_E ⟶ ω_E`, a Borel-Moore section. Pairing against
the diagonal identity gives the *trace class* of an endocorrespondence, a Borel-Moore
section on the fixed scheme, and integrating over a clopen piece gives a *local term*.

## Main definitions

- `AlgebraicGeometry.ProEtale.Correspondence.supportedClass`: the class `ũ` on `Y × X` of a
  correspondence.
- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedPairing`: the Lefschetz-Verdier
  pairing `⟨u, v⟩_LV`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass`: the trace class `Tr_c(u)`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm`: the local term `LT_B(α)`.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.integral_traceClass_eq_trace`: the point
  normalisation of the pairing.
- `AlgebraicGeometry.ProEtale.GeometricOperations.integral_eq_sum_localTerm`: the
  decomposition of an integral into local terms.

## Implementation notes

`supportedPairing`, `traceClass` and `localTerm` are composites of the adjunctions of the
pro-étale functors and the comparison data of the package
`AlgebraicGeometry.ProEtale.GeometricOperations`:

* `GeometricOperations.kunnethClass` turns a coefficient map into a class on `Y × X`
  through the projection formula, the composition of exceptional inverse images, tensor-hom
  and the inverse of the field `kunnethVerdier`;
* `GeometricOperations.pairingOfSquare` contracts two such classes using the projection
  formula, `!`-base change, the monoidal structure `upperStarTensor` of the pullback, the
  Verdier evaluations and `GeometricOperations.dualizingProd : ω_Y ⊠ ω_X ⟶ ω_{Y × X}`, which is
  built from the trace `Ra_{X!} a_X^! A ⟶ A` rather than from `kunnethVerdier`, whose
  hypotheses `ω_Y` and `A_X` need not satisfy;
* `traceClass` is the pairing against the diagonal identity, restricted along the
  identification `Fix(c) ≃ E(C, X)` of `Correspondence.isPullback_fixι_toProd`;
* `localTerm` is the integral of the restriction `GeometricOperations.borelMooreRestrict`.

The Künneth-Verdier field needs a field as base, `X` and `Y` separated of finite type and
the coefficients in `Dᵇctf`, so `supportedPairing` and `traceClass` carry those hypotheses.
The helpers are stated for an arbitrary Cartesian square rather than for `pullback aY aX`:
the kernel check of monoidal composites in the derived category of the literal fibre
product is very slow, and instantiating the general statement avoids it.

Perfectness is rendered as dualizability, `HasRightDual`, and `tr_A` is
`CategoryTheory.MonoidalCategory.trace`, taken in `D(s, A)`, whose unit endomorphism ring
is the coefficient ring. Its braiding is an instance hypothesis: this project installs a
monoidal structure on a derived category but not yet a braiding.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X Y : Scheme.{u}} {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

namespace Correspondence

/-- The support map of `ofEnd G aX K v` is the diagonal of `aX`, a closed immersion when
`aX` is separated, so it admits a compactification. -/
instance hasCompactification_toProd_ofEnd (G : GeometricOperations A s) [IsSeparated aX]
    (v : K ⟶ K) : HasCompactification (ofEnd G aX K v).toProd :=
  inferInstanceAs (HasCompactification (pullback.diagonal aX))

/-- The swapped support map of `ofEnd G aX K v` is the diagonal of `aX`, a closed immersion
when `aX` is separated, so it admits a compactification. -/
instance hasCompactification_toProdSwap_ofEnd (G : GeometricOperations A s) [IsSeparated aX]
    (v : K ⟶ K) : HasCompactification (ofEnd G aX K v).toProdSwap :=
  inferInstanceAs (HasCompactification (pullback.diagonal aX))

end Correspondence

namespace GeometricOperations

variable (G : GeometricOperations A s)

section KunnethClass

variable {Z T X' Y' : Scheme.{u}} {aX' : X' ⟶ s} {aY' : Y' ⟶ s} {pX : Z ⟶ X'} {pY : Z ⟶ Y'}
  [HasCompactification pX] (i : T ⟶ Z) [HasCompactification i] {cX : T ⟶ X'} {cY : T ⟶ Y'}
  [HasCompactification cX] (hX : i ≫ pX = cX) (hY : i ≫ pY = cY)
  (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A))
  (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A))
  (u : ((upperStar A cY).leftDerivedFunctor).obj N ⟶ (rightDerivedUpperShriek A cX).obj M)

/-- The tensor-hom mate `pY^* N ⊗ᴸ Ri_! A_T ⟶ pX^! M` of a coefficient map
`u : cY^* N ⟶ cX^! M` along a morphism `i : T ⟶ Z` with `i ≫ pX = cX` and `i ≫ pY = cY`:
the composite

```
  pY^* N ⊗ᴸ Ri_! A_T ≃ Ri_! (A_T ⊗ᴸ i^* pY^* N) ≃ Ri_! cY^* N ──u──▶ Ri_! cX^! M
                     ≃ Ri_! i^! pX^! M ──ε──▶ pX^! M
```

of the braiding, the projection formula, the unitor, the composition of pullbacks, `u`, the
composition of exceptional inverse images and the counit of `Ri_! ⊣ i^!`
(part of blueprint `sk-d-corr`). -/
noncomputable def exceptionalMate
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))] :
    ((upperStar A pY).leftDerivedFunctor).obj N ⊗ (rightDerivedLowerShriek A i).obj (𝟙_ _) ⟶
      (rightDerivedUpperShriek A pX).obj M :=
  have : HasCompactification (i ≫ pX) := hX ▸ inferInstance
  (β_ _ _).hom ≫ (G.projectionFormula i).hom.app (𝟙_ _, _) ≫
    (rightDerivedLowerShriek A i).map ((λ_ _).hom ≫
      ((leftDerivedUpperStarComp A i pY).symm ≪≫ leftDerivedUpperStarCongr A hY).hom.app N ≫
      u ≫
      (conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A cX)
        (rightDerivedUpperShriekAdjunction A (i ≫ pX)) (lowerShriekCongr (A := A) hX)).hom.app M ≫
      (G.upperShriekComp i pX).hom.app M) ≫
    (rightDerivedUpperShriekAdjunction A i).counit.app _

/-- The Künneth-Verdier class `Ri_! A_T ⟶ pX^* M ⊗ᴸ pY^* D N` of a coefficient map
`u : cY^* N ⟶ cX^! M` supported on `i : T ⟶ Z`, for a Cartesian square
`Z = X' ×_s Y'`: the curried `GeometricOperations.exceptionalMate` of `u`, read through
the inverse of the Künneth-Verdier isomorphism
`pX^* M ⊗ᴸ pY^* D N ≃ RHom(pY^* N, pX^! M)` (part of blueprint `sk-d-pairing`). -/
noncomputable def kunnethClass (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k)))
    [IsSeparated aX'] [LocallyOfFiniteType aX'] [QuasiCompact aX']
    [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (sq : IsPullback pX pY aX' aY') (hM : G.ctf X' M) (hN : G.ctf Y' N)
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))] :
    (rightDerivedLowerShriek A i).obj (𝟙_ _) ⟶
      ((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj (G.verdierDual aY' N) :=
  MonoidalClosed.curry (G.exceptionalMate i hX hY M N u) ≫
    (G.kunnethVerdier hs sq M hM N hN).inv

end KunnethClass

section Square

variable [HasCompactification aX] {Z : Scheme.{u}} {p₁ : Z ⟶ Y} {p₂ : Z ⟶ X}
  (sq : IsPullback p₁ p₂ aY aX) [HasCompactification p₁] [HasCompactification p₂]
  [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))]

/-- The exterior product of the dualizing complexes, `ω_Y ⊠ ω_X ⟶ ω_Z` for a Cartesian square
`Z = Y ×_s X`: the exceptional adjoint under `Rp₁_! ⊣ p₁^!` of

```
  Rp₁_! (p₁^* ω_Y ⊗ᴸ p₂^* ω_X) ≃ Rp₁_! p₂^* ω_X ⊗ᴸ ω_Y ≃ a_Y^* Ra_{X!} ω_X ⊗ᴸ ω_Y
      ──tr──▶ a_Y^* A_s ⊗ᴸ ω_Y ≃ ω_Y,
```

built from the projection formula, `!`-base change and the trace `Ra_{X!} a_X^! A ⟶ A`,
followed by `p₁^! ω_Y ≃ ω_Z` (part of blueprint `sk-d-pairing`). -/
noncomputable def dualizingProd :
    ((upperStar A p₁).leftDerivedFunctor).obj (G.dualizing aY) ⊗
        ((upperStar A p₂).leftDerivedFunctor).obj (G.dualizing aX) ⟶
      G.dualizing (p₁ ≫ aY) :=
  (rightDerivedUpperShriekAdjunction A p₁).homEquiv _ _
      ((rightDerivedLowerShriek A p₁).map (β_ _ _).hom ≫
        (G.projectionFormula p₁).inv.app (_, G.dualizing aY) ≫
        ((G.baseChange sq.flip).inv.app (G.dualizing aX) ▷ _) ≫
        (((upperStar A aY).leftDerivedFunctor).map
          ((rightDerivedLowerShriek A aX).map (G.dualizingIso aX).hom ≫
            (rightDerivedUpperShriekAdjunction A aX).counit.app (𝟙_ _)) ▷ _) ≫
        ((G.upperStarUnit aY).hom ▷ _) ≫ (λ_ _).hom) ≫
    (G.dualizingComp p₁ aY).hom

variable {C D E : Scheme.{u}} (i : C ⟶ Z) (j : D ⟶ Z) [HasCompactification i]
  [HasCompactification j] {q₁ : E ⟶ C} {q₂ : E ⟶ D} (sqE : IsPullback q₁ q₂ i j)
  [HasCompactification q₁]
  (uc : (rightDerivedLowerShriek A i).obj (𝟙_ _) ⟶
    ((upperStar A p₁).leftDerivedFunctor).obj L ⊗
      ((upperStar A p₂).leftDerivedFunctor).obj (G.verdierDual aX K))
  (vd : (rightDerivedLowerShriek A j).obj (𝟙_ _) ⟶
    ((upperStar A p₂).leftDerivedFunctor).obj K ⊗
      ((upperStar A p₁).leftDerivedFunctor).obj (G.verdierDual aY L))

/-- The contraction `Ri_! (A_C ⊗ᴸ i^* Rj_! A_D) ⟶ ω_Z` of two classes
`ũ : Ri_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rj_! A_D ⟶ K ⊠ D_Y L` on `Z = Y ×_s X`: the projection
formula `Ri_! (A_C ⊗ᴸ i^* Rj_! A_D) ≃ Ri_! A_C ⊗ᴸ Rj_! A_D`, then `ũ ⊗ ṽ`, the exchange of the
middle factors, the monoidality of `p₁^*` and `p₂^*`, the two Verdier evaluations
`L ⊗ᴸ D_Y L ⟶ ω_Y` and `K ⊗ᴸ D_X K ⟶ ω_X`, and `ω_Y ⊠ ω_X ⟶ ω_Z`
(part of blueprint `sk-d-pairing`). -/
noncomputable def pairingContraction :
    (rightDerivedLowerShriek A i).obj (((upperStar A i).leftDerivedFunctor).obj
        ((rightDerivedLowerShriek A j).obj (𝟙_ _))) ⟶
      G.dualizing (p₁ ≫ aY) :=
  (rightDerivedLowerShriek A i).map (λ_ _).inv ≫
    (G.projectionFormula i).inv.app (𝟙_ _, _) ≫ (uc ⊗ₘ vd) ≫
    (_ ◁ (β_ _ _).hom) ≫ tensorμ _ _ _ _ ≫ (_ ◁ (β_ _ _).hom) ≫
    ((G.upperStarTensor p₁ L (G.verdierDual aY L)).inv ⊗ₘ
      (G.upperStarTensor p₂ K (G.verdierDual aX K)).inv) ≫
    (((upperStar A p₁).leftDerivedFunctor).map ((ihom.ev L).app (G.dualizing aY)) ⊗ₘ
      ((upperStar A p₂).leftDerivedFunctor).map ((ihom.ev K).app (G.dualizing aX))) ≫
    G.dualizingProd sq

/-- The pairing of two classes `ũ : Ri_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rj_! A_D ⟶ K ⊠ D_Y L`
on `Z = Y ×_s X`, a Borel-Moore section on `E = C ×_Z D`: the composite

`Rq₁_! A_E ≃ Rq₁_! q₂^* A_D ≃ i^* Rj_! A_D ⟶ i^! ω_Z ≃ ω_C`

of `upperStarUnit`, `!`-base change and the exceptional adjoint of
`GeometricOperations.pairingContraction`, followed by the exceptional adjoint along `q₁` and
`q₁^! ω_C ≃ ω_E` (part of blueprint `sk-d-pairing`). -/
noncomputable def pairingOfSquare : G.borelMooreSections (q₁ ≫ i ≫ p₁ ≫ aY) :=
  (rightDerivedUpperShriekAdjunction A q₁).homEquiv _ _
      ((rightDerivedLowerShriek A q₁).map (G.upperStarUnit q₂).inv ≫
        (G.baseChange sqE.flip).inv.app (𝟙_ _) ≫
        (rightDerivedUpperShriekAdjunction A i).homEquiv _ _
          (G.pairingContraction sq i j uc vd) ≫
        (G.dualizingComp i _).hom) ≫
    (G.dualizingComp q₁ _).hom

end Square

variable [HasCompactification aX] [HasCompactification aY]

instance hasCompactification_pullback_fst : HasCompactification (pullback.fst aY aX) :=
  .of_isPullback (IsPullback.of_hasPullback aY aX).flip

instance hasCompactification_pullback_snd : HasCompactification (pullback.snd aY aX) :=
  .of_isPullback (IsPullback.of_hasPullback aY aX)

end GeometricOperations

namespace Correspondence

variable (G : GeometricOperations A s) [HasCompactification aX] [HasCompactification aY]
  (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k)))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aY aX)) A))]

/-- The supported class `ũ : Rc_! A_C ⟶ L ⊠ D_X K` on `Y × X` of a correspondence
`(C, c, u)` from `(X, K)` to `(Y, L)`: the `GeometricOperations.kunnethClass` of `u` along
the support map `c : C ⟶ Y × X` (blueprint: `sk-d-corr`, `sk-d-pairing`). -/
noncomputable def supportedClass (c : Correspondence aX aY K L)
    (hK : G.ctf X K) (hL : G.ctf Y L) [HasCompactification c.toProd] :
    (rightDerivedLowerShriek A c.toProd).obj (𝟙_ _) ⟶
      ((upperStar A (pullback.fst aY aX)).leftDerivedFunctor).obj L ⊗
        ((upperStar A (pullback.snd aY aX)).leftDerivedFunctor).obj (G.verdierDual aX K) :=
  G.kunnethClass c.toProd (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) L K c.coeff hs
    (IsPullback.of_hasPullback aY aX) hL hK

/-- The supported class `ṽ : Rd̄_! A_D ⟶ K ⊠ D_Y L` on `Y × X` of an opposite correspondence
`(D, d, v)` from `(Y, L)` to `(X, K)`: the `GeometricOperations.kunnethClass` of `v` along
the swapped support map `d̄ : D ⟶ Y × X` (blueprint: `sk-d-pairing`). -/
noncomputable def supportedClassSwap (d : Correspondence aY aX L K) (hK : G.ctf X K)
    (hL : G.ctf Y L)
    [HasCompactification d.toProdSwap] :
    (rightDerivedLowerShriek A d.toProdSwap).obj (𝟙_ _) ⟶
      ((upperStar A (pullback.snd aY aX)).leftDerivedFunctor).obj K ⊗
        ((upperStar A (pullback.fst aY aX)).leftDerivedFunctor).obj (G.verdierDual aY L) :=
  G.kunnethClass d.toProdSwap (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) K L d.coeff
    hs (IsPullback.of_hasPullback aY aX).flip hK hL

end Correspondence

namespace GeometricOperations

variable (G : GeometricOperations A s) [HasCompactification aX] [HasCompactification aY]

/-- The *Lefschetz-Verdier pairing* of an opposite pair of correspondences: the inverse
Kuenneth-Verdier maps turn the supported classes of `u` and `v` into

`ũ : Rc_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rd̄_! A_D ⟶ K ⊠ D_Y L`

on `Z = Y × X` (`Correspondence.supportedClass`), and
`GeometricOperations.pairingOfSquare` contracts them, through the projection formula,
`!`-base change, the two Verdier evaluations and `ω_Y ⊠ ω_X ⟶ ω_Z`, to a Borel-Moore
section `⟨u, v⟩_LV : A_E ⟶ ω_E` on the intersection `E = E(C, D)`
(blueprint: `sk-d-pairing`).

The Künneth-Verdier isomorphism is only available for `X`, `Y` separated of finite type
over a field and `K`, `L` in `Dᵇctf`, hence the hypotheses `hs`, `hK` and `hL`. -/
noncomputable def supportedPairing (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K)
    (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k)))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hK : G.ctf X K) (hL : G.ctf Y L)
    [HasCompactification c.toProd] [HasCompactification d.toProdSwap]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aY aX)) A))] :
    G.borelMooreSections (c.intersectionStr d) :=
  have : HasCompactification (pullback.fst c.toProd d.toProdSwap) :=
    .of_isPullback (IsPullback.of_hasPullback c.toProd d.toProdSwap).flip
  G.pairingOfSquare (IsPullback.of_hasPullback aY aX) c.toProd d.toProdSwap
      (IsPullback.of_hasPullback c.toProd d.toProdSwap)
      (c.supportedClass G hs hK hL) (d.supportedClassSwap G hs hK hL) ≫
    eqToHom (congrArg G.dualizing (by
      simp [Correspondence.intersectionStr, Correspondence.toProd, c.fst_comp]))

/-- The *trace class* `Tr_c(u) : A_F ⟶ ω_F` of an endocorrespondence `(C, c, u)` on
`(X, K)`, a Borel-Moore section on the fixed scheme `F = Fix(c)`: the supported pairing
`⟨u, 𝟙 K⟩_LV` against the diagonal identity, transported to `F` along the identification
`F ≃ E(C, X)` of the fixed scheme with the intersection of `c` and the diagonal
(`Correspondence.isPullback_fixι_toProd`), as blueprint `sk-d-trace-class` computes it. -/
noncomputable def traceClass (c : Correspondence aX aX K K)
    (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k)))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] (hK : G.ctf X K)
    [HasCompactification c.toProd]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aX aX)) A))] :
    G.borelMooreSections c.fixStr :=
  let e : c.fix ≅ c.intersection (Correspondence.ofEnd G aX K (𝟙 K)) :=
    c.isPullback_fixι_toProd.isoPullback
  G.borelMooreRestrict e.hom (G.supportedPairing c (Correspondence.ofEnd G aX K (𝟙 K)) hs hK hK) ≫
    eqToHom (congrArg G.dualizing (by
      rw [Correspondence.intersectionStr, ← Category.assoc]
      exact congrArg (· ≫ c.str) c.isPullback_fixι_toProd.isoPullback_hom_fst))

/-- The *local term* `LT_B(α) ∈ A` of a Borel-Moore section `α : A_E ⟶ ω_E` along a clopen
immersion `j_B : B ⟶ E` with `B` proper over `s`: restrict `α` along `j_B`, identify
`j_B^* A_E ≃ A_B` and `j_B^* ω_E ≃ ω_B` by open purity and dualizing composition, and
integrate over `B`. The ambient support `E` need not be proper; at a Frobenius fixed point
`LT_x̄` means the local term on its reduced clopen point component
(blueprint: `sk-d-local-term`). -/
noncomputable def localTerm {E B : Scheme.{u}} (aE : E ⟶ s) (jB : B ⟶ E)
    [IsOpenImmersion jB] [HasCompactification jB] (hB : IsClosed (Set.range jB.base))
    [HasCompactification (jB ≫ aE)] [IsProper (jB ≫ aE)] (α : G.borelMooreSections aE) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  G.integral (jB ≫ aE) (G.borelMooreRestrict jB α)

/-- Point normalization of the pairing: for a perfect `A`-complex `P` on the base point `s`
and an endomorphism `v : P ⟶ P`, regarded as an endocorrespondence with support `s` and
identity legs, the supported pairing against the diagonal identity is the ordinary
categorical trace, `⟨v, 𝟙 P⟩_LV = tr_A(v ∣ P)`.

The same adjunction calculation identifies the trace class of an endocorrespondence on an
arbitrary `X`, which is what the proper compatibility theorem uses
(blueprint: `sk-p-pairing`). -/
theorem integral_traceClass_eq_trace
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback (𝟙 s) (𝟙 s))) A))]
    (hs : ∃ (k : Type u) (_ : Field k), Nonempty (s ≅ Spec (.of k)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology s) A)) (hP : G.ctf s P) [HasRightDual P]
    (v : P ⟶ P) :
    G.integral (Correspondence.ofEnd G (𝟙 s) P v).fixStr
        (G.traceClass (Correspondence.ofEnd G (𝟙 s) P v) hs hP) =
      MonoidalCategory.trace v :=
  sorry

/-- Decomposition into local terms: if the support of a Borel-Moore section is a finite
disjoint union `E = ∐_{β ∈ B} β` of clopen subschemes, each proper over `s`, then the
integral of the section is the sum of its local terms, `∫_E α = ∑_β LT_β(α)`. In particular
this applies to the Lefschetz-Verdier pairing `α = ⟨u, v⟩_LV`; the empty support gives the
empty sum `0` (blueprint: `sk-p-local`). -/
theorem integral_eq_sum_localTerm {E : Scheme.{u}} (aE : E ⟶ s) [HasCompactification aE]
    [IsProper aE] {ι : Type u} [Fintype ι] {B : ι → Scheme.{u}} (j : ∀ i, B i ⟶ E)
    [∀ i, IsOpenImmersion (j i)] [∀ i, HasCompactification (j i)]
    [∀ i, HasCompactification (j i ≫ aE)]
    [∀ i, IsProper (j i ≫ aE)] (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (α : G.borelMooreSections aE) :
    G.integral aE α = ∑ i, G.localTerm aE (j i) (hclosed i) α :=
  sorry

end GeometricOperations

end AlgebraicGeometry.ProEtale
