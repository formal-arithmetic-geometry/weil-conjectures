/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

import Sheaf.Paper.ContinuousConstructibleIntegralModel
import Sheaf.Paper.ContinuousIntegralExchangeSquare
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Integral realization of a continuous E exchange arrow

Source: Bhatt--Scholze, Sections 6.7--6.8
(blueprint: lem-weil-pbc-continuous-exchange-integral-model).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]


set_option maxHeartbeats 400000 in
-- Elaborating both bundled coefficient exchange arrows needs the extra budget.
/-- A continuous E exchange arrow is realized by scalar extension of an integral one.
Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2), with the exchange
compatibility of `lem-weil-pbc-condensed-e-realization`
(blueprint: lem-weil-pbc-continuous-exchange-integral-model).

Proof in words. Lemma 6.8.13 gives a constructible O_E lattice for each lisse
 E-cohomology sheaf; it need not be a global lisse integral lattice. Refine the finite
 stratification until the integral lattices have the required finite presentations.
 Extend them across the open and closed pieces, and lift the
 finitely many extension classes after multiplying by powers of ℓ. Bounded truncation
 triangles yield a bounded constructible integral complex M whose derived E scalar
 extension is K. The completed integral realization identifies M with its ordinary
 continuous-coefficient complex. The proved `continuousIntegralFunctions_isLocalization`
 identifies coefficient localization on compact profinite tests. Exact inverse image
 from the point preserves it. Exact scalar localization commutes with inverse image.
 For proper direct image, bounded-below coproduct continuity makes the scalar-localization
 comparison invertible. These comparisons preserve units and counits, and the coherent
 pullback composition comparison. Substitute them into the specified three-factor
 exchange formula. Its image under scalar extension is conjugate to the continuous E
 exchange at the realized object. Naturality transports across its isomorphism to K.
 The two conjugating object comparisons define the asserted isomorphism of arrows.
 No invertibility of either exchange arrow is asserted or used. -/
theorem continuousExchange_integral_model [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    ∃ M : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X),
      Nonempty (Arrow.mk ((integralScalarExtension ℓ E Y').map
          ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app M).hom) ≅
        Arrow.mk ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app K).hom) := by
  let : IsNoetherian (Spec (.of k)) := {}
  let : IsNoetherian X := AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  let : TopologicalSpace.NoetherianSpace X := by infer_instance
  obtain ⟨M, ⟨e⟩⟩ := continuousConstructible_integral_model ℓ E X K
  have hM : ProEtale.boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X)
      ((integralScalarExtension ℓ E X).obj M.obj) :=
    ((integralScalarConstructible ℓ E X).obj M).property
  let N : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X) :=
    ⟨(integralScalarExtension ℓ E X).obj M.obj, hM⟩
  let eN : N ≅ K := ObjectProperty.isoMk _ e
  obtain ⟨s, t, h⟩ := continuousIntegral_exchange_square ℓ E k sq M hM
  let S := boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f.asOver (Spec (.of k))) ⋙
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k)))
  let T := boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k))) ⋙
    boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of k)))
  let ι := (ProEtale.boundedConstructible
    (condensedRingObj (Profinite.continuousMapRingObj E) Y')).ι
  refine ⟨M, ⟨Arrow.isoMk (s ≪≫ ι.mapIso (S.mapIso eN))
    (t ≪≫ ι.mapIso (T.mapIso eN)) ?_⟩⟩
  change (s.hom ≫ (S.map eN.hom).hom) ≫
      ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app K).hom =
    (integralScalarExtension ℓ E Y').map
      ((boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app M).hom ≫
        (t.hom ≫ (T.map eN.hom).hom)
  have hn := (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).naturality eN.hom
  have hn' := congrArg (fun a ↦ a.hom) hn
  change (S.map eN.hom).hom ≫ _ = _ ≫ (T.map eN.hom).hom at hn'
  rw [Category.assoc, hn', ← Category.assoc, h, Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
