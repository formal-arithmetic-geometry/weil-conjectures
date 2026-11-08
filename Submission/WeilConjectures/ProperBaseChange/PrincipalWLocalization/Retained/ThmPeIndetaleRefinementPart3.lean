/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart2Supplement3
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2
import Submission.WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Properties of the retained localization

Source: blueprint, proper base change, order 1225, Properties of the retained localization
(blueprint: lem-weil-pbc-retained-localization).
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.Retained

variable {R : Type u} [CommRing R]

private noncomputable def partAt (i : Index R) (x : PrimeSpectrum R) : i.parts :=
  (i.partition x).choose

private theorem partAt_mem (i : Index R) (x : PrimeSpectrum R) : x ∈ (partAt i x).val :=
  (i.partition x).choose_spec.1

private theorem parent_partAt {i j : Index R} (h : i ≤ j) (x : PrimeSpectrum R) :
    parent h (partAt j x) = partAt i x := by
  apply (i.partition x).choose_spec.2
  exact ((h (partAt j x)).choose_spec.1) (partAt_mem j x)

private noncomputable def evalFactorAt (i : Index R) (E : i.parts) (x : PrimeSpectrum R)
    (hx : x ∈ E.val) : Localization.Away (i.denominator E) →ₐ[R]
      Localization.AtPrime x.asIdeal :=
  IsLocalization.Away.liftAlgHom (i.denominator E)
    (f := Algebra.ofId R (Localization.AtPrime x.asIdeal))
    (IsLocalization.map_units (Localization.AtPrime x.asIdeal)
      (M := x.asIdeal.primeCompl) ⟨i.denominator E, i.nonvanishing E hx⟩)

private noncomputable def evalFactor (i : Index R) (x : PrimeSpectrum R) :
    Localization.Away (i.denominator (partAt i x)) →ₐ[R]
      Localization.AtPrime x.asIdeal :=
  evalFactorAt i (partAt i x) x (partAt_mem i x)

private noncomputable def evalStage (i : Index R) (x : PrimeSpectrum R) :
    Stage i →ₐ[R] Localization.AtPrime x.asIdeal :=
  (evalFactor i x).comp (Pi.evalAlgHom R _ (partAt i x))

private theorem evalFactorAt_compatible {i j : Index R} (h : i ≤ j)
    (E : i.parts) (F : j.parts) (x : PrimeSpectrum R) (hxE : x ∈ E.val) (hxF : x ∈ F.val)
    (hpar : parent h F = E) (b : Stage i) :
    evalFactorAt j F x hxF ((PrincipalWLocalization.transition h b) F) =
      evalFactorAt i E x hxE (b E) := by
  subst E
  let φ : Localization.Away (i.denominator (parent h F)) →ₐ[R]
      Localization.Away (j.denominator F) :=
    IsLocalization.Away.liftAlgHom (i.denominator (parent h F))
      (f := Algebra.ofId R (Localization.Away (j.denominator F)))
      (IsLocalization.Away.isUnit_of_dvd _ (parent_dvd h F))
  have heq : (evalFactorAt j F x hxF).comp φ = evalFactorAt i (parent h F) x hxE :=
    (IsLocalization.algHom_subsingleton
      (Submonoid.powers (i.denominator (parent h F)))).elim _ _
  exact DFunLike.congr_fun heq (b (parent h F))

private theorem evalStage_compatible {i j : Index R} (h : i ≤ j) (x : PrimeSpectrum R) :
    (evalStage j x).comp (PrincipalWLocalization.transition h) = evalStage i x := by
  ext b
  exact evalFactorAt_compatible h (partAt i x) (partAt j x) x
    (partAt_mem i x) (partAt_mem j x) (parent_partAt h x) b

private noncomputable def evaluation (x : PrimeSpectrum R) :
    PrincipalWLocalization.algebra R →ₐ[R] Localization.AtPrime x.asIdeal :=
  (CategoryTheory.Limits.colimit.desc (diagram (A := R))
    { pt := CommAlgCat.of R (Localization.AtPrime x.asIdeal)
      ι :=
        { app := fun i ↦ CommAlgCat.ofHom (evalStage i x)
          naturality := by
            intro i j h
            apply CommAlgCat.hom_ext
            exact evalStage_compatible h.le x } }).hom

end PrincipalWLocalization.Retained
