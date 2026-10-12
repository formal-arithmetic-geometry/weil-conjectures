/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.Derived.ClopenIdempotent
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence

/-!
# The Lefschetz-Verdier pairing, trace classes and local terms

For an opposite pair of correspondences `(C, c, u)` from `(X, K)` to `(Y, L)` and
`(D, d, v)` back, the Künneth-Verdier comparison turns the two coefficient maps into
sections over the intersection `E(C, D) = C ×_{Y × X} D`, and their contraction is the
Lefschetz-Verdier pairing `⟨u, v⟩_LV : A_E ⟶ ω_E`, a Borel-Moore section. Pairing against
the diagonal identity gives the *trace class* of an endocorrespondence, a Borel-Moore
section on the fixed scheme, and integrating over a clopen piece gives a *local term*.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedClass`: the class `ũ` on `Y × X`
  of a correspondence.
- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedClassSwap`: the class `ṽ` on
  `Y × X` of an opposite correspondence.
- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedPairing`: the Lefschetz-Verdier
  pairing `⟨u, v⟩_LV`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.traceClass`: the trace class `Tr_c(u)`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.localTerm`: the local term `LT_B(α)`.

## Main results

- `AlgebraicGeometry.ProEtale.GeometricOperations.supportedClass_eq_rhomClass_comp`: the
  supported class is the class `[u]` read through the Künneth-Verdier isomorphism.
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
  and the inverse of the Künneth-Verdier isomorphism `GeometricOperations.kunnethVerdier`;
* `GeometricOperations.pairingOfSquare` contracts two such classes using the projection
  formula, `!`-base change, the monoidal structure `upperStarTensor` of the pullback, the
  Verdier evaluations and
  `GeometricOperations.dualizingExteriorProd : ω_Y ⊠ ω_X ⟶ ω_{Y × X}`, which is built from
  the trace `Ra_{X!} a_X^! A ⟶ A` rather than from `kunnethVerdier`, whose hypotheses `ω_Y`
  and `A_X` need not satisfy;
* `traceClass` is `pairingOfSquare` applied to the Cartesian square
  `Fix(c) = C ×_{X × X} X` of `Correspondence.isPullback_fixι_toProd`, with the class of the
  diagonal identity, so it lives on `Fix(c)` with no transport step. Its comparison with
  `supportedPairing c (Correspondence.ofEnd G aX K (𝟙 K))` along `Fix(c) ≅ E(C, X)` is not
  formalised;
* `localTerm` along a clopen `j_B : B ⟶ E` is the integral over `E` of `e_B · α`, where
  `e_B = AlgebraicGeometry.ProEtale.clopenIdempotent j_B` is the idempotent of `A_E` cut out
  by `B`. It is built from the adjunctions `Lj^* ⊣ Rj_*` and `j_! ⊣ j^*` alone, so the local
  terms use no package data beyond that of `GeometricOperations.integral`. This is
  `∫_B α|_B` in the blueprint's formulation; restricting `α` to `B` itself would need
  open purity `j^! ≃ Lj^*` and the monoidal unit `Lj^* A_E ≃ A_B`, which are not pinned to
  canonical maps here.

The Künneth-Verdier isomorphism needs a field as base (the class `Scheme.IsSpecOfField`),
`X` and `Y` separated of finite type and the coefficients in `Dᵇctf`, so `supportedPairing`
and `traceClass` carry those hypotheses. Separatedness and local finite type of `a_X` are
instances derived from `HasCompactification a_X`, so only `QuasiCompact a_X` is added.
The helpers are stated for an arbitrary Cartesian square rather than for `pullback aY aX`:
the kernel check of monoidal composites in the derived category of the literal fibre
product is very slow, and instantiating the general statement avoids it.

`dualizingExteriorProd` and the exceptional trace of `GeometricOperations.kunnethVerdierMap`
are built from the same package data: `!`-base change, `dualizingIso` and the counit of
`Ra_! ⊣ a^!`.

Perfectness is rendered as dualizability, `HasRightDual`, and `tr_A` is
`CategoryTheory.MonoidalCategory.trace`, taken in `D(s, A)`, whose unit endomorphism ring
is the coefficient ring. The braidings used by `exceptionalMate`, `pairingContraction` and
`trace` all come from the one instance `DerivedBraiding A`, for which the pullbacks are
braided monoidal (`GeometricOperations.upperStarMonoidal_braiding`).
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [DerivedBraiding A] {s X Y : Scheme.{u}}
  {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

namespace GeometricOperations

variable (G : GeometricOperations A s)

section KunnethClass

variable {Z T X' Y' : Scheme.{u}} {aX' : X' ⟶ s} {aY' : Y' ⟶ s} {pX : Z ⟶ X'} {pY : Z ⟶ Y'}
  [HasCompactification pX] (i : T ⟶ Z) [HasCompactification i] {cX : T ⟶ X'} {cY : T ⟶ Y'}
  [HasCompactification cX] (hX : i ≫ pX = cX) (hY : i ≫ pY = cY)
  (hi : IsGeometricHom s i) (hpX : IsGeometricHom s pX) (hpY : IsGeometricHom s pY)
  (hT : IsGeometricHom s (𝟙 T))
  {M : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A)} (hM : G.ctf X' M)
  {N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A)} (hN : G.ctf Y' N)
  (u : ((upperStar A cY).leftDerivedFunctor).obj N ⟶ (rightDerivedUpperShriek A cX).obj M)

/-- The tensor-hom mate `pY^* N ⊗ᴸ Ri_! A_T ⟶ pX^! M` of a coefficient map
`u : cY^* N ⟶ cX^! M` along a morphism `i : T ⟶ Z` of geometric schemes with `i ≫ pX = cX` and
`i ≫ pY = cY`, for `M` and `N` in `Dᵇctf`: the composite

```
  pY^* N ⊗ᴸ Ri_! A_T ≃ Ri_! (A_T ⊗ᴸ i^* pY^* N) ≃ Ri_! cY^* N ──u──▶ Ri_! cX^! M
                     ≃ Ri_! i^! pX^! M ──ε──▶ pX^! M
```

of the braiding, the projection formula, the unitor, the composition of pullbacks, `u`, the
composition of exceptional inverse images and the counit of `Ri_! ⊣ i^!`
(part of blueprint `sk-d-corr`). -/
noncomputable def exceptionalMate :
    ((upperStar A pY).leftDerivedFunctor).obj N ⊗ (rightDerivedLowerShriek A i).obj (𝟙_ _) ⟶
      (rightDerivedUpperShriek A pX).obj M :=
  have : HasCompactification (i ≫ pX) := .of_eq hX.symm
  (β_ _ _).hom ≫ (G.projectionFormula i hi).hom.app
      (⟨𝟙_ _, G.ctf_unit hT⟩, ⟨_, G.ctf_upperStar pY hpY hN⟩) ≫
    (rightDerivedLowerShriek A i).map ((λ_ _).hom ≫
      ((leftDerivedUpperStarComp A i pY).symm ≪≫ leftDerivedUpperStarCongr A hY).hom.app N ≫
      u ≫ (rightDerivedUpperShriekCongr A hX.symm).hom.app M ≫
      ((G.upperShriekComp i pX hi hpX (hi.comp hpX)).hom.app ⟨M, hM⟩).hom) ≫
    G.exceptionalCounit i hi _ (G.ctf_upperShriek pX hpX hM)

/-- The tensor-hom mate of `GeometricOperations.exceptionalMate` is the class `[u]` of `u`:
the class bijection `GeometricOperations.correspondenceClassEquiv` sends it to `u`
(part of blueprint `lem-trf-correspondence-class`). -/
lemma correspondenceClassEquiv_curry_exceptionalMate :
    haveI : HasCompactification (i ≫ pX) := .of_eq hX.symm
    G.correspondenceClassEquiv hpX hpY hi hX hY hN hM
      (curry (G.exceptionalMate i hX hY hi hpX hpY hT hM hN u)) = u := by
  subst hX hY
  rw [correspondenceClassEquiv_apply, supportedClassHomEquiv_apply, uncurry_curry]
  have hE : (G.upperShriekCompIso i pX hi hpX (hi.comp hpX) M hM).inv =
      ((G.upperShriekComp i pX hi hpX (hi.comp hpX)).hom.app ⟨M, hM⟩).hom := rfl
  have hS : (leftDerivedUpperStarCompIso i (rfl : i ≫ pY = _) N).hom =
      ((leftDerivedUpperStarComp A i pY).symm ≪≫ leftDerivedUpperStarCongr A rfl).hom.app N := by
    simp [leftDerivedUpperStarCompIso]
  simp only [exceptionalMate, Iso.app_inv, rightDerivedUpperShriekCongr_rfl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id, ← hE, ← hS]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id_assoc]
  rw [GeometricCoefficients.exceptionalHomEquiv_naturality_left _ i hi _
      (G.ctf_upperShriek i hi (G.ctf_upperShriek pX hpX hM))]
  erw [GeometricCoefficients.exceptionalHomEquiv_exceptionalCounit]
  simp

/-- The class `[u]` of `u` is the tensor-hom mate of `GeometricOperations.exceptionalMate`
(part of blueprint `lem-trf-correspondence-class`). -/
lemma correspondenceClass_eq_curry_exceptionalMate :
    haveI : HasCompactification (i ≫ pX) := .of_eq hX.symm
    G.correspondenceClass hpX hpY hi hX hY hN hM u =
      curry (G.exceptionalMate i hX hY hi hpX hpY hT hM hN u) := by
  rw [correspondenceClass, Equiv.symm_apply_eq,
    correspondenceClassEquiv_curry_exceptionalMate]

/-- The Künneth-Verdier class `Ri_! A_T ⟶ pX^* M ⊗ᴸ pY^* D N` of a coefficient map
`u : cY^* N ⟶ cX^! M` supported on `i : T ⟶ Z`, for a Cartesian square
`Z = X' ×_s Y'` of geometric schemes: the curried `GeometricOperations.exceptionalMate` of `u`,
read through the inverse of the Künneth-Verdier isomorphism
`pX^* M ⊗ᴸ pY^* D N ≃ RHom(pY^* N, pX^! M)` (part of blueprint `sk-d-pairing`). -/
noncomputable def kunnethClass [s.IsSpecOfField] [IsGeometric aX'] [IsGeometric aY']
    [IsGeometric (pX ≫ aX')] [HasCompactification aX'] [HasCompactification aY']
    (sq : IsPullback pX pY aX' aY') :
    (rightDerivedLowerShriek A i).obj (𝟙_ _) ⟶
      ((upperStar A pX).leftDerivedFunctor).obj M ⊗
        ((upperStar A pY).leftDerivedFunctor).obj (G.verdierDual aY' N) :=
  MonoidalClosed.curry (G.exceptionalMate i hX hY hi hpX hpY hT hM hN u) ≫
    (G.kunnethVerdier sq M hM N hN).inv

end KunnethClass

section Square

variable [IsGeometric aX] [IsGeometric aY] [HasCompactification aX] {Z : Scheme.{u}}
  {p₁ : Z ⟶ Y} {p₂ : Z ⟶ X} (sq : IsPullback p₁ p₂ aY aX) [IsGeometric (p₁ ≫ aY)]
  [HasCompactification p₁] [HasCompactification p₂]

/-- The exterior product of the dualizing complexes, `ω_Y ⊠ ω_X ⟶ ω_Z` for a Cartesian square
`Z = Y ×_s X` of geometric schemes: the exceptional adjoint under `Rp₁_! ⊣ p₁^!` of

```
  Rp₁_! (p₁^* ω_Y ⊗ᴸ p₂^* ω_X) ≃ Rp₁_! p₂^* ω_X ⊗ᴸ ω_Y ≃ a_Y^* Ra_{X!} ω_X ⊗ᴸ ω_Y
      ──tr──▶ a_Y^* A_s ⊗ᴸ ω_Y ≃ ω_Y,
```

built from the projection formula, `!`-base change and the trace `Ra_{X!} a_X^! A ⟶ A`,
followed by `p₁^! ω_Y ≃ ω_Z` (part of blueprint `sk-d-pairing`). -/
noncomputable def dualizingExteriorProd :
    ((upperStar A p₁).leftDerivedFunctor).obj (G.dualizing aY) ⊗
        ((upperStar A p₂).leftDerivedFunctor).obj (G.dualizing aX) ⟶
      G.dualizing (p₁ ≫ aY) :=
  haveI : IsGeometric (p₂ ≫ aX) := IsGeometric.of_eq sq.w
  G.exceptionalHomEquiv p₁ (.mk (aY := aY) rfl)
      (G.ctf_tensor (.id (p₁ ≫ aY)) (G.ctf_upperStar p₁ (.mk (aY := aY) rfl) (G.ctf_dualizing aY))
        (G.ctf_upperStar p₂ (.mk (aY := aX) rfl) (G.ctf_dualizing aX)))
      (G.ctf_dualizing aY)
      ((rightDerivedLowerShriek A p₁).map (β_ _ _).hom ≫
        (G.projectionFormula p₁ (.mk (aY := aY) rfl)).inv.app
          (⟨_, G.ctf_upperStar p₂ (.mk (aY := aX) rfl) (G.ctf_dualizing aX)⟩,
            ⟨G.dualizing aY, G.ctf_dualizing aY⟩) ≫
        (((G.baseChange sq.flip (.of_isGeometric aX) (.of_isGeometric aY) (.mk (aY := aY) rfl)
          (.mk (aY := aX) rfl)).inv.app ⟨G.dualizing aX, G.ctf_dualizing aX⟩).hom ▷ _) ≫
        (((upperStar A aY).leftDerivedFunctor).map
          ((rightDerivedLowerShriek A aX).map (G.dualizingIso aX).hom ≫
            G.exceptionalCounit aX (.of_isGeometric aX) (𝟙_ _) (G.ctf_unit (.id (𝟙 s)))) ▷ _) ≫
        ((G.upperStarUnit aY).hom ▷ _) ≫ (λ_ _).hom) ≫
    (G.dualizingComp p₁ aY).hom

variable {C D E : Scheme.{u}} (i : C ⟶ Z) (j : D ⟶ Z) [HasCompactification i]
  [HasCompactification j] {q₁ : E ⟶ C} {q₂ : E ⟶ D} (sqE : IsPullback q₁ q₂ i j)
  [HasCompactification q₁] [IsGeometric (i ≫ p₁ ≫ aY)] [IsGeometric (j ≫ p₁ ≫ aY)]
  [IsGeometric (q₁ ≫ i ≫ p₁ ≫ aY)]
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
    (G.projectionFormula i (.mk (aY := p₁ ≫ aY) rfl)).inv.app
      (⟨𝟙_ _, G.ctf_unit (.id (i ≫ p₁ ≫ aY))⟩,
        ⟨_, G.ctf_lowerShriek j (.mk (aY := p₁ ≫ aY) rfl) (G.ctf_unit (.id (j ≫ p₁ ≫ aY)))⟩) ≫
    (uc ⊗ₘ vd) ≫
    (_ ◁ (β_ _ _).hom) ≫ tensorμ _ _ _ _ ≫ (_ ◁ (β_ _ _).hom) ≫
    ((G.upperStarTensor p₁ L (G.verdierDual aY L)).inv ⊗ₘ
      (G.upperStarTensor p₂ K (G.verdierDual aX K)).inv) ≫
    (((upperStar A p₁).leftDerivedFunctor).map ((ihom.ev L).app (G.dualizing aY)) ⊗ₘ
      ((upperStar A p₂).leftDerivedFunctor).map ((ihom.ev K).app (G.dualizing aX))) ≫
    G.dualizingExteriorProd sq

/-- The pairing of two classes `ũ : Ri_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rj_! A_D ⟶ K ⊠ D_Y L`
on `Z = Y ×_s X`, a Borel-Moore section on `E = C ×_Z D`: the composite

`Rq₁_! A_E ≃ Rq₁_! q₂^* A_D ≃ i^* Rj_! A_D ⟶ i^! ω_Z ≃ ω_C`

of `upperStarUnit`, `!`-base change and the exceptional adjoint of
`GeometricOperations.pairingContraction`, followed by the exceptional adjoint along `q₁` and
`q₁^! ω_C ≃ ω_E` (part of blueprint `sk-d-pairing`). -/
noncomputable def pairingOfSquare : G.borelMooreSections (q₁ ≫ i ≫ p₁ ≫ aY) :=
  haveI : IsGeometric (q₂ ≫ j ≫ p₁ ≫ aY) :=
    IsGeometric.of_eq (a := q₁ ≫ i ≫ p₁ ≫ aY) (by rw [← Category.assoc, sqE.w, Category.assoc])
  G.exceptionalHomEquiv q₁ (.mk (aY := i ≫ p₁ ≫ aY) rfl)
      (G.ctf_unit (.id (q₁ ≫ i ≫ p₁ ≫ aY))) (G.ctf_dualizing (i ≫ p₁ ≫ aY))
      ((rightDerivedLowerShriek A q₁).map (G.upperStarUnit q₂).inv ≫
        ((G.baseChange sqE.flip (.mk (aY := p₁ ≫ aY) rfl) (.mk (aY := p₁ ≫ aY) rfl)
          (.mk (aY := i ≫ p₁ ≫ aY) rfl) (.mk (aY := j ≫ p₁ ≫ aY) rfl)).inv.app
            ⟨𝟙_ _, G.ctf_unit (.id (j ≫ p₁ ≫ aY))⟩).hom ≫
        G.exceptionalHomEquiv i (.mk (aY := p₁ ≫ aY) rfl)
          (G.ctf_upperStar i (.mk (aY := p₁ ≫ aY) rfl)
            (G.ctf_lowerShriek j (.mk (aY := p₁ ≫ aY) rfl) (G.ctf_unit (.id (j ≫ p₁ ≫ aY)))))
          (G.ctf_dualizing (p₁ ≫ aY))
          (G.pairingContraction sq i j uc vd) ≫
        (G.dualizingComp i (p₁ ≫ aY)).hom) ≫
    (G.dualizingComp q₁ (i ≫ p₁ ≫ aY)).hom

end Square

section Pairing

variable [HasCompactification aX] [HasCompactification aY] [s.IsSpecOfField]
  [QuasiCompact aX] [QuasiCompact aY]

/-- The supported class `ũ : Rc_! A_C ⟶ L ⊠ D_X K` on `Y × X` of a correspondence
`(C, c, u)` from `(X, K)` to `(Y, L)` on geometric schemes, with `K` and `L` in `Dᵇctf`: the
`GeometricOperations.kunnethClass` of `u` along the support map `c : C ⟶ Y × X`
(blueprint: `sk-d-corr`, `sk-d-pairing`). -/
noncomputable def supportedClass (c : Correspondence aX aY K L) [IsGeometric c.str]
    (hK : G.ctf X K) (hL : G.ctf Y L) [HasCompactification c.toProd] :
    (rightDerivedLowerShriek A c.toProd).obj (𝟙_ _) ⟶
      ((upperStar A (pullback.fst aY aX)).leftDerivedFunctor).obj L ⊗
        ((upperStar A (pullback.snd aY aX)).leftDerivedFunctor).obj (G.verdierDual aX K) :=
  G.kunnethClass c.toProd (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (.mk (aX := c.str) (aY := pullback.fst aY aX ≫ aY)
      (by simp [Correspondence.toProd, c.fst_comp]))
    (.mk (aY := aY) rfl) (.mk (aX := pullback.fst aY aX ≫ aY) (aY := aX) pullback.condition.symm)
    (.id c.str) hL hK c.coeff (IsPullback.of_hasPullback aY aX)

/-- The supported class `ũ` of a correspondence is its class
`[u] ∈ H_C^0(Y × X, RHom(Lp₂^* K, Rp₁^! L))` (`Correspondence.rhomClass`) read through the
inverse of the Künneth-Verdier isomorphism `L ⊠ D_X K ≃ RHom(Lp₂^* K, Rp₁^! L)`
(blueprint: `lem-trf-correspondence-class`). -/
lemma supportedClass_eq_rhomClass_comp (c : Correspondence aX aY K L) [IsGeometric c.str]
    (hK : G.ctf X K) (hL : G.ctf Y L) [HasCompactification c.toProd] :
    G.supportedClass c hK hL = c.rhomClass G hK hL ≫
      (G.kunnethVerdier (IsPullback.of_hasPullback aY aX) L hL K hK).inv := by
  rw [supportedClass, kunnethClass, Correspondence.rhomClass,
    correspondenceClass_eq_curry_exceptionalMate]

/-- The supported class `ṽ : Rd̄_! A_D ⟶ K ⊠ D_Y L` on `Y × X` of an opposite correspondence
`(D, d, v)` from `(Y, L)` to `(X, K)` on geometric schemes: the
`GeometricOperations.kunnethClass` of `v` along the swapped support map `d̄ : D ⟶ Y × X`
(blueprint: `sk-d-pairing`). -/
noncomputable def supportedClassSwap (d : Correspondence aY aX L K) [IsGeometric d.str]
    (hK : G.ctf X K) (hL : G.ctf Y L) [HasCompactification d.toProdSwap] :
    (rightDerivedLowerShriek A d.toProdSwap).obj (𝟙_ _) ⟶
      ((upperStar A (pullback.snd aY aX)).leftDerivedFunctor).obj K ⊗
        ((upperStar A (pullback.fst aY aX)).leftDerivedFunctor).obj (G.verdierDual aY L) :=
  haveI : IsGeometric (pullback.snd aY aX ≫ aX) := IsGeometric.of_eq pullback.condition
  G.kunnethClass d.toProdSwap (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
    (.mk (aX := d.str) (aY := pullback.snd aY aX ≫ aX)
      (by simp [Correspondence.toProdSwap, d.fst_comp]))
    (.mk (aY := aX) rfl) (.mk (aX := pullback.snd aY aX ≫ aX) (aY := aY) pullback.condition)
    (.id d.str) hK hL d.coeff (IsPullback.of_hasPullback aY aX).flip

/-- The *Lefschetz-Verdier pairing* of an opposite pair of correspondences on geometric
schemes, with coefficients in `Dᵇctf`: the inverse Künneth-Verdier maps turn the supported
classes of `u` and `v` into

`ũ : Rc_! A_C ⟶ L ⊠ D_X K` and `ṽ : Rd̄_! A_D ⟶ K ⊠ D_Y L`

on `Z = Y × X` (`GeometricOperations.supportedClass`), and
`GeometricOperations.pairingOfSquare` contracts them, through the projection formula,
`!`-base change, the two Verdier evaluations and `ω_Y ⊠ ω_X ⟶ ω_Z`, to a Borel-Moore
section `⟨u, v⟩_LV : A_E ⟶ ω_E` on the intersection `E = E(C, D)`
(blueprint: `def-trf-supported-pairing`, subsection `sk-d-pairing`). -/
noncomputable def supportedPairing (c : Correspondence aX aY K L)
    (d : Correspondence aY aX L K) [IsGeometric c.str] [IsGeometric d.str] (hK : G.ctf X K)
    (hL : G.ctf Y L) [HasCompactification c.toProd] [HasCompactification d.toProdSwap]
    [HasCompactification (pullback.fst c.toProd d.toProdSwap)] :
    G.borelMooreSections (c.intersectionStr d) :=
  haveI : IsGeometric (c.toProd ≫ pullback.fst aY aX ≫ aY) :=
    IsGeometric.of_eq (a := c.str) (by simp [Correspondence.toProd, c.fst_comp])
  haveI : IsGeometric (d.toProdSwap ≫ pullback.fst aY aX ≫ aY) :=
    IsGeometric.of_eq (a := d.str) (by simp [Correspondence.toProdSwap, d.snd_comp])
  have hd : IsGeometricHom s d.toProdSwap := .mk (aX := d.str)
    (aY := pullback.fst aY aX ≫ aY) (by simp [Correspondence.toProdSwap, d.snd_comp])
  have := hd.isSeparated
  have := hd.locallyOfFiniteType
  have := hd.quasiCompact
  haveI : IsGeometric (c.intersectionStr d) :=
    inferInstanceAs (IsGeometric (pullback.fst c.toProd d.toProdSwap ≫ c.str))
  haveI : IsGeometric (pullback.fst c.toProd d.toProdSwap ≫ c.toProd ≫ pullback.fst aY aX ≫
      aY) := IsGeometric.of_eq (c.pullback_fst_toProd_fst_comp_eq_intersectionStr d).symm
  G.pairingOfSquare (IsPullback.of_hasPullback aY aX) c.toProd d.toProdSwap
      (IsPullback.of_hasPullback c.toProd d.toProdSwap)
      (G.supportedClass c hK hL) (G.supportedClassSwap d hK hL) ≫
    eqToHom (congrArg G.dualizing (c.pullback_fst_toProd_fst_comp_eq_intersectionStr d))

end Pairing

/-- The *trace class* `Tr_c(u) : A_F ⟶ ω_F` of an endocorrespondence `(C, c, u)` on
`(X, K)` with `K ∈ Dᵇctf(X)` on a geometric scheme, a Borel-Moore section on the fixed scheme
`F = Fix(c)`: the contraction `GeometricOperations.pairingOfSquare` of the supported class of
`u` against the supported class of the diagonal identity `1_K`, over the Cartesian square
`F = C ×_{X × X} X` of `Correspondence.isPullback_fixι_toProd` (blueprint:
`sk-d-trace-class`). It is the construction of the Lefschetz-Verdier pairing `⟨u, 1_K⟩_LV`
with the fixed scheme `F` in place of the intersection `E(C, X)`; the comparison with
`supportedPairing` along `F ≅ E(C, X)` is not formalised. -/
noncomputable def traceClass [HasCompactification aX] [s.IsSpecOfField] [QuasiCompact aX]
    (c : Correspondence aX aX K K) [IsGeometric c.str] (hK : G.ctf X K)
    [HasCompactification c.toProd] :
    G.borelMooreSections c.fixStr :=
  haveI : IsGeometric (c.toProd ≫ pullback.fst aX aX ≫ aX) :=
    IsGeometric.of_eq (a := c.str) (by simp [Correspondence.toProd, c.fst_comp])
  haveI : IsGeometric ((Correspondence.ofEnd G aX K hK (𝟙 K)).toProdSwap ≫
      pullback.fst aX aX ≫ aX) := IsGeometric.of_eq (a := aX) (by simp)
  haveI : IsGeometric (c.fixι ≫ c.toProd ≫ pullback.fst aX aX ≫ aX) :=
    IsGeometric.of_eq c.fixι_toProd_fst_comp_eq_fixStr.symm
  G.pairingOfSquare (IsPullback.of_hasPullback aX aX) c.toProd
      (Correspondence.ofEnd G aX K hK (𝟙 K)).toProdSwap c.isPullback_fixι_toProd
      (G.supportedClass c hK hK)
      (G.supportedClassSwap (Correspondence.ofEnd G aX K hK (𝟙 K)) hK hK) ≫
    eqToHom (congrArg G.dualizing c.fixι_toProd_fst_comp_eq_fixStr)

/-- The *local term* `LT_B(α) ∈ A` of a Borel-Moore section `α : A_E ⟶ ω_E` along a clopen
immersion `j_B : B ⟶ E`, for `E` geometric and proper over `s`: the integral `∫_E e_B · α` of
`α` cut down by the idempotent `e_B : A_E ⟶ A_E` of the clopen piece `B`
(`AlgebraicGeometry.ProEtale.clopenIdempotent`), which is `∫_B α|_B`. At a Frobenius fixed
point `LT_x̄` means the local term on its reduced clopen point component
(blueprint: `sk-d-local-term`). -/
noncomputable def localTerm {E B : Scheme.{u}} (aE : E ⟶ s) [IsGeometric aE]
    [HasCompactification aE] [IsProper aE] (jB : B ⟶ E) [IsOpenImmersion jB]
    (hB : IsClosed (Set.range jB.base))
    (α : G.borelMooreSections aE) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  G.integral aE ((clopenIdempotent A jB hB).app (𝟙_ _) ≫ α)

/-- Point normalization of the pairing: for a perfect `A`-complex `P` on the base point `s`
and an endomorphism `v : P ⟶ P`, regarded as an endocorrespondence with support `s` and
identity legs, the supported pairing against the diagonal identity is the ordinary
categorical trace, `⟨v, 𝟙 P⟩_LV = tr_A(v ∣ P)`.

The same adjunction calculation identifies the trace class of an endocorrespondence on an
arbitrary `X`, which is what the proper compatibility theorem uses
(blueprint: `sk-p-pairing`). -/
theorem integral_traceClass_eq_trace [s.IsSpecOfField]
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology s) A)) (hP : G.ctf s P) [HasRightDual P]
    (v : P ⟶ P) :
    G.integral (Correspondence.ofEnd G (𝟙 s) P hP v).fixStr
        (G.traceClass (Correspondence.ofEnd G (𝟙 s) P hP v) hP) =
      MonoidalCategory.trace v :=
  sorry

/-- Decomposition into local terms: if the support of a Borel-Moore section is a finite
disjoint union `E = ∐_{β ∈ B} β` of clopen subschemes and `E` is geometric and proper over
`s`, then the integral of the section is the sum of its local terms, `∫_E α = ∑_β LT_β(α)`.
In particular this applies to the Lefschetz-Verdier pairing `α = ⟨u, v⟩_LV`; the empty support
gives the empty sum `0` (blueprint: `lem-trf-integration-component-sum`, with the local terms
in the idempotent form `∫_E e_β · α` of `localTerm`; subsection `sk-p-local`). -/
theorem integral_eq_sum_localTerm {E : Scheme.{u}} (aE : E ⟶ s) [IsGeometric aE]
    [HasCompactification aE] [IsProper aE] {ι : Type u} [Fintype ι] {B : ι → Scheme.{u}}
    (j : ∀ i, B i ⟶ E)
    [∀ i, IsOpenImmersion (j i)] (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (α : G.borelMooreSections aE) :
    G.integral aE α = ∑ i, G.localTerm aE (j i) (hclosed i) α := by
  have h := NatTrans.congr_app (sum_clopenIdempotent A j hclosed hdisj hcover) (𝟙_ _)
  rw [NatTrans.app_sum, NatTrans.id_app] at h
  have h' : (∑ i, (clopenIdempotent A (j i) (hclosed i)).app (𝟙_ _)) ≫ α = α := by
    rw [h]
    exact Category.id_comp α
  conv_lhs => rw [← h']
  simp only [localTerm, integral, borelMoorePushforward, Preadditive.sum_comp,
    Preadditive.comp_sum, Functor.map_sum, Category.assoc]


section LocalTermPair

variable [IsGeometric aX] [IsGeometric aY] [HasCompactification aX] [HasCompactification aY]
  [s.IsSpecOfField] [QuasiCompact aX] [QuasiCompact aY]
  (c : Correspondence aX aY K L) (d : Correspondence aY aX L K) [IsGeometric c.str]
  [IsGeometric d.str] (hK : G.ctf X K) (hL : G.ctf Y L) [HasCompactification c.toProd]
  [HasCompactification d.toProdSwap] [HasCompactification (pullback.fst c.toProd d.toProdSwap)]
  [IsGeometric (c.intersectionStr d)] [HasCompactification (c.intersectionStr d)]
  [IsProper (c.intersectionStr d)]

/-- Blueprint `def-trf-local-term-pair`: the local term `LT_B(u, v) = LT_B(⟨u, v⟩_LV)` of an
opposite pair `(C, c, u)`, `(D, d, v)` along a clopen piece `j_B : B ⟶ E(C, D)` of the
intersection support, when `E(C, D)` is proper over `s`: the local term
`GeometricOperations.localTerm` of the Lefschetz-Verdier pairing. -/
noncomputable def localTermPair {B : Scheme.{u}} (jB : B ⟶ c.intersection d)
    [IsOpenImmersion jB] (hB : IsClosed (Set.range jB.base)) :
    End (𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))) :=
  G.localTerm (c.intersectionStr d) jB hB (G.supportedPairing c d hK hL)

omit [IsGeometric aX] [IsGeometric aY] in
/-- Blueprint `prop-trf-pairing-local-decomposition`: if the intersection support `E(C, D)` of
an opposite pair is proper over `s` and a finite disjoint union of clopen pieces `β`, the
integral of the Lefschetz-Verdier pairing is the sum of the local terms of the pair,
`∫_E ⟨u, v⟩_LV = ∑_β LT_β(u, v)` (the empty union gives `0`). -/
theorem integral_supportedPairing_eq_sum_localTermPair {ι : Type u} [Fintype ι]
    {B : ι → Scheme.{u}} (j : ∀ i, B i ⟶ c.intersection d) [∀ i, IsOpenImmersion (j i)]
    (hclosed : ∀ i, IsClosed (Set.range (j i).base))
    (hdisj : Pairwise fun i i' ↦ Disjoint (Set.range (j i).base) (Set.range (j i').base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ) :
    G.integral (c.intersectionStr d) (G.supportedPairing c d hK hL) =
      ∑ i, G.localTermPair c d hK hL (j i) (hclosed i) :=
  G.integral_eq_sum_localTerm _ j hclosed hdisj hcover _

end LocalTermPair

end GeometricOperations

end AlgebraicGeometry.ProEtale
