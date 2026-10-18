module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Nodes persist under extension of algebraically closed fields

Source: Stacks Project, `literature/stacks-project/curves.tex`, Tag 0C56
(lemma-node-field-extension), direction (1) ⇒ (2); completed-local-ring comparison
from Varieties Tag 0C54 (blueprint: lem-trf-node-algebraically-closed-extension).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Source: Stacks Project, `literature/stacks-project/curves.tex`, Tag 0C56,
lemma-node-field-extension, direction (1) ⇒ (2), with Varieties Tag 0C54
(blueprint: lem-trf-node-algebraically-closed-extension).

Proof plan.  For a nonsmooth point of the base change, its image is nonsmooth:
a smooth neighbourhood would remain smooth after base change.  The assumed ring
isomorphism of the completed local ring identifies the residue field with an
algebraically closed field; finite type and Zariski's lemma then identify that
residue field with `k`, so the point is closed.  On an affine neighbourhood,
the fibre product is the affine scalar extension and has a unique point above
this closed point.  A presentation of the completed local ring over `k`,
together with the nondegenerate quadratic criterion and a linear change of
variables, gives the presentation `k[[u,v]]/(uv)`.  The completed-local-ring
base-change comparison then gives `Ω[[u,v]]/(uv)` at the point after extension.
The argument is pointwise and therefore also covers an empty scheme.
-/
theorem node_algebraically_closed_extension
    (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hC : ∀ x : C,
      (¬ ∃ U : C.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) →
        Nonempty
          (AdicCompletion
            (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
            (C.presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) k ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
                MvPowerSeries.X 1})))
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] :
    ∀ x : Limits.pullback (C := Scheme.{u}) f
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
      (¬ ∃ U : (Limits.pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).Opens,
        x ∈ U ∧
          Smooth (U.ι ≫ Limits.pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) →
      Nonempty
        (AdicCompletion
          (IsLocalRing.maximalIdeal
            ((Limits.pullback (C := Scheme.{u}) f
              (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).presheaf.stalk x))
          ((Limits.pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              MvPowerSeries.X 1})) := by
  sorry

end AlgebraicGeometry
