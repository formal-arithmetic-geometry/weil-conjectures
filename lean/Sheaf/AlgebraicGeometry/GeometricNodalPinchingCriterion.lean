/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.PowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedCurveNormalization
import Sheaf.TraceFormula.MultipointedCurve
import Sheaf.AlgebraicGeometry.MultipointedCurveModification
import Sheaf.Paper.OrgogozoInductionData
import Sheaf.AlgebraicGeometry.RelativeNodalPointPinching
import Sheaf.AlgebraicGeometry.FerrandSchemePushout

/-! # Geometric nodal fibres of smooth double-branch pinching

Source: Stacks Project, curves.tex, Tags 0E36 and 0C1J, and more-morphisms.tex, Tag 0E25,
via the field pinching theorem `exists_relative_nodal_point_pinching`.
(blueprint: lem-sfb-geometric-nodal-pinching-criterion).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fibrewise scheme pushout identifying finite étale double branches in the smooth locus
of a proper flat curve preserves reduced pure one-dimensional nodal geometric fibres.
The maps in every clause are the images of the specified maps under `Over.pullback g`.
Finite coproduct cofans express the split finite étale schemes, including the empty case.
The complement isomorphism commutes with the given map and with the projections to `Spec Ω`;
it therefore preserves the old singularities and their local rings. The last two ring
isomorphisms use the constant-coefficient maps to form `Ω[[u]] ×_Ω Ω[[v]]`.
No connectedness, flatness of the output, trait, or projectivity hypothesis is imposed.

Source: Stacks Project, curves.tex, Tags 0E36 (lemma-complete-local-ring-pushout),
0C1J (example-glue-points); more-morphisms.tex, Tag 0E25.
(blueprint: lem-sfb-geometric-nodal-pinching-criterion).

Proof plan:
1. Fix a geometric point. Properness and finite presentation of X and P, finiteness and
   étaleness of Z, T and j, and the smooth closed branch locus survive base change, by
   lem-pc-proper-base-change, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-etale-scheme-base-change and
   lem-weil-pbc-closed-immersion-base-change. No flatness of P or of the point is used.
2. By lem-weil-pbc-etale-algebra-over-field-product and
   lem-weil-pbc-spec-finite-product-fields the branch schemes are finite coproducts of
   Spec Ω: every finite extension of an algebraically closed field is trivial.
   lem-weil-pbc-fibre-degree-base-change makes every fibre of j have degree two, hence
   exactly two distinct points. Their images under the closed immersion remain distinct
   and smooth. This uses def-pc-finite-locally-free and def-weil-algebraic-closure.
3. The curve is Noetherian with finitely many components, by
   lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-noetherian-finitely-many-components. Pure dimension one makes a nonclosed
   point generic in a component: otherwise a strict specialization gives a chain of
   length two in that component. The dense smooth open supplied by
   lem-weil-pbc-reduced-curve-normalization contains every component generic point, so
   all nonclosed points are smooth.
4. With empty marking the geometric curve is semistable. Flatness over Ω is
   lem-pc-flat-field; finite presentation and pure dimension one were checked above.
   The marking conditions are vacuous. Step 3 and the closed-point hypothesis give
   smoothness or a node at every point. An algebraic closure of Ω is Ω up to Ω-isomorphism.
   These are precisely def-trf-multipointed-curve, def-trf-multipointed-curve-modification
   and def-trf-orgogozo-induction-data.
5. Apply lem-trf-relative-nodal-point-pinching over Ω with reference Spec Ω. It gives a
   pushout, the complement isomorphism, pure dimension one and the displayed completed
   local rings at each identified pair. Both it and the given fibre of P are pushouts
   in all schemes (def-weil-pbc-category-colimit), so uniqueness gives an isomorphism
   commuting with the specified maps and transfers these conclusions to P.
6. Apply lem-sfb-ferrand-scheme-pushout to this diagram. Its affine-neighbourhood
   condition holds because the finite map from X has affine inverse images of affine
   neighbourhoods in P. The finite map j is integral (def-weil-finite-integral-morphism).
   On the simultaneous affine charts the section ring is a subring of A × B, with A
   reduced and B a product of fields. A nilpotent pair is zero in both coordinates;
   thus the subring is reduced. The charts cover P (def-pc-reduced-scheme).
7. Surjectivity of X to the pushout gives nonemptiness. Apply step 3 to the now reduced
   pure one-dimensional proper output to make its nonclosed points smooth. Every new
   point has the completed local ring of step 5. Elsewhere the complement isomorphism
   preserves smoothness, local rings and completions, giving the old nodal condition.
   No connectedness or separation of branches into different components was used.
   If T is empty, Z is empty and the pushout is X; all branch clauses are vacuous.
-/
theorem geometric_nodal_pinching_criterion
    (S : Scheme.{u}) (X Z T P : Over S)
    [IsProper X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [IsFinite Z.hom] [Etale Z.hom] [IsFinite T.hom] [Etale T.hom]
    [IsProper P.hom] [LocallyOfFinitePresentation P.hom]
    (i : Z ⟶ X) (j : Z ⟶ T) [IsClosedImmersion i.left] [Etale j.left]
    [j.left.IsFiniteLocallyFreeOfDegree 2]
    (hi : ∀ z : Z.left, i.left z ∈ X.hom.smoothLocus)
    (a : X ⟶ P) (b : T ⟶ P) (hab : i ≫ a = j ≫ b)
    (hpushout : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S),
      IsPushout ((Over.pullback g).map i).left ((Over.pullback g).map j).left
        ((Over.pullback g).map a).left ((Over.pullback g).map b).left)
    (hX : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S),
      Nonempty ↥(pullback (C := Scheme.{u}) X.hom g) ∧
      IsReduced (pullback (C := Scheme.{u}) X.hom g) ∧
      (pullback (C := Scheme.{u}) X.hom g).IsPureDimension 1 ∧
      ∀ x : pullback (C := Scheme.{u}) X.hom g,
        x ∈ closedPoints (pullback (C := Scheme.{u}) X.hom g) →
        x ∉ (pullback.snd X.hom g).smoothLocus →
        Nonempty (NodalFiber.completedLocalRing x ≃+* NodalFiber.powerSeriesQuotient Ω)) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S),
      Nonempty ↥(pullback (C := Scheme.{u}) P.hom g) ∧
      IsReduced (pullback (C := Scheme.{u}) P.hom g) ∧
      (pullback (C := Scheme.{u}) P.hom g).IsPureDimension 1 ∧
      (∀ x : pullback (C := Scheme.{u}) P.hom g,
        x ∈ closedPoints (pullback (C := Scheme.{u}) P.hom g) →
        x ∉ (pullback.snd P.hom g).smoothLocus →
        Nonempty (NodalFiber.completedLocalRing x ≃+* NodalFiber.powerSeriesQuotient Ω)) ∧
      (∀ x : pullback (C := Scheme.{u}) X.hom g,
        x ∉ closedPoints (pullback (C := Scheme.{u}) X.hom g) →
        x ∈ (pullback.snd X.hom g).smoothLocus) ∧
      (∀ x : pullback (C := Scheme.{u}) P.hom g,
        x ∉ closedPoints (pullback (C := Scheme.{u}) P.hom g) →
        x ∈ (pullback.snd P.hom g).smoothLocus) ∧
      (∃ (m : ℕ)
          (ε : Fin m → (Over.mk (𝟙 (Spec (.of Ω))) ⟶ (Over.pullback g).obj Z)),
        Nonempty (IsColimit (Cofan.mk (pullback (C := Scheme.{u}) Z.hom g) (fun l ↦ (ε l).left)))) ∧
      (∃ (n : ℕ)
          (φ : Fin n → (Over.mk (𝟙 (Spec (.of Ω))) ⟶ (Over.pullback g).obj T)),
        Nonempty (IsColimit (Cofan.mk (pullback (C := Scheme.{u}) T.hom g) (fun l ↦ (φ l).left)))) ∧
      (∀ t : pullback (C := Scheme.{u}) T.hom g,
        ∃ z : Fin 2 → ↥(pullback (C := Scheme.{u}) Z.hom g),
        Function.Injective (fun l ↦ ((Over.pullback g).map i).left (z l)) ∧
        (∀ z' : pullback (C := Scheme.{u}) Z.hom g,
          ((Over.pullback g).map j).left z' = t ↔ z' ∈ Set.range z) ∧
        ∀ l : Fin 2,
          ((Over.pullback g).map i).left (z l) ∈ (pullback.snd X.hom g).smoothLocus) ∧
      (∃ (U : (pullback (C := Scheme.{u}) X.hom g).Opens)
          (V : (pullback (C := Scheme.{u}) P.hom g).Opens)
          (e : U.toScheme ≅ V.toScheme),
        (U : Set (pullback (C := Scheme.{u}) X.hom g)) =
          (Set.range ((Over.pullback g).map i).left)ᶜ ∧
        (V : Set (pullback (C := Scheme.{u}) P.hom g)) =
          (Set.range ((Over.pullback g).map b).left)ᶜ ∧
        e.hom ≫ V.ι = U.ι ≫ ((Over.pullback g).map a).left ∧
        e.hom ≫ V.ι ≫ pullback.snd P.hom g = U.ι ≫ pullback.snd X.hom g) ∧
      (∀ t : pullback (C := Scheme.{u}) T.hom g,
        Nonempty (NodalFiber.completedLocalRing (((Over.pullback g).map b).left t) ≃+*
          ↥(pullback (CommRingCat.ofHom (PowerSeries.constantCoeff (R := Ω)))
            (CommRingCat.ofHom (PowerSeries.constantCoeff (R := Ω))))) ∧
        Nonempty (↥(pullback (CommRingCat.ofHom (PowerSeries.constantCoeff (R := Ω)))
          (CommRingCat.ofHom (PowerSeries.constantCoeff (R := Ω)))) ≃+*
            NodalFiber.powerSeriesQuotient Ω)) := by
  sorry

end AlgebraicGeometry
