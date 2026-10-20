/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.MultipointedCurve
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.TraceFormula.PureRelativeDimensionFiniteStage

/-! # Finite-type integral models of multipointed curves

Source: Temkin, *Stable modification of relative curves*, §3.1 and the first
sentence of the proof of Theorem 1.5, pp. 14--15 and 35--36
(blueprint: lem-trf-marked-curve-finite-type-model).

## Main statement

* `exists_finite_type_model_of_multipointed_curve` descends an integral
  quasi-compact quasi-separated base and its generically smooth marked curve
  to an integral finite-type model over `ℤ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Finite-type integral models of a multipointed curve.
Source: Temkin, *Stable modification of relative curves*, §3.1 and the first
sentence of the proof of Theorem 1.5, pp. 14--15 and 35--36
(blueprint: lem-trf-marked-curve-finite-type-model).

Proof plan, following the node's ten steps:
1. Apply `prop-nagata-noetherian-inverse-system`, reindex by a directed set using
   `lem-weil-pbc-filtered-category-directed-cofinal`, and obtain Noetherian qcqs
   stages with `lem-weil-pbc-finite-type-over-noetherian`.
2. Apply `thm-pd-spreading-out` to both schemes and then their marking arrow.
   Finite presentation and qcqs permanence use `lem-weil-pbc-qcqs-morphism-permanence`.
3. Descend the closed marking with `lem-weil-pbc-descend-closed-immersion`, using
   `lem-weil-pbc-proper-fp-permanence` to establish local finite type.
4. Descend flatness of both structural maps by
   `lem-weil-pbc-descend-flat-finite-presentation`; preserve it by
   `lem-weil-pbc-flat-morphism-base-change`.
5. Apply `lem-trf-pure-relative-dimension-finite-stage` with dimensions one and zero,
   and take a common later stage.
6. Use `lem-weil-pbc-reduced-induced-closed-subscheme` to take the reduced closed
   closure T of the image of the generic point. It is integral.
7. Every function in this radical ideal pulls back to zero on the reduced S, so
   S factors through T. The map is dominant, and quotient affine charts show that
   T is of finite type over the integers.
8. Pull the stage pair back to T using the non-semistable first clause of
   `lem-trf-semistable-marked-base-change`.
9. The generic field extension is faithfully flat by
   `lem-weil-pbc-field-extension-base-change-faithfully-flat`. Descend smoothness
   and etaleness by `lem-trf-smooth-fpqc-base-descent` and
   `lem-galois-fpqc-descend-etale` along its singleton fpqc covering.
10. Fibre-product associativity gives the two isomorphisms; the descended arrow
    makes them commute with the markings.
-/
theorem exists_finite_type_model_of_multipointed_curve
    {S : Scheme.{u}} [IsIntegral S] [CompactSpace S] [QuasiSeparatedSpace S]
    (P : MultipointedCurve S)
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (hXη : Smooth (P.x.fiberToSpecResidueField η))
    (hDη : Etale (P.d.fiberToSpecResidueField η)) :
    ∃ (T : Scheme.{u}) (hT : IsIntegral T) (ηT : T),
      IsGenericPoint ηT (Set.univ : Set T) ∧
      ∃ (s : S ⟶ T),
        IsDominant s ∧ s η = ηT ∧
        ∃ (tZ : T ⟶ Spec (.of (ULift.{u} ℤ))),
          LocallyOfFiniteType tZ ∧ QuasiCompact tZ ∧
          ∃ (P₀ : MultipointedCurve T),
            Smooth (P₀.x.fiberToSpecResidueField ηT) ∧
            Etale (P₀.d.fiberToSpecResidueField ηT) ∧
            ∃ (eX : P.X ≅ pullback P₀.x s)
              (eD : P.D ≅ pullback P₀.d s),
              eX.hom ≫ pullback.snd P₀.x s = P.x ∧
              eD.hom ≫ pullback.snd P₀.d s = P.d ∧
              eD.hom ≫ pullback.fst P₀.d s ≫ P₀.i =
                P.i ≫ eX.hom ≫ pullback.fst P₀.x s := by
  sorry

end AlgebraicGeometry
