/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import Sheaf.Algebra.FinitePresentationColimit

/-! # Finite-stage local module models

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-local-object-models). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Local finitely presented modules lift on a finite affine cover, without any overlap maps.
Source: Stacks Project, Limits, Tag 01ZR, first proof; Algebra, Tag 05N7, object clause.
(blueprint: lem-pc-fp-local-object-models).

Proof: Quasi-compactness of f over the affine base makes Xi quasi-compact. Take a finite
subcover of its affine cover. On each chart the stage coordinate rings are base changes
of the chart ring, and the limit chart ring is their directed colimit: first identify
c.pt with Spec(colim R) by uniqueness of limits, then use the spectrum/tensor-product
pullback comparison. The restriction of M is quasi-coherent and finitely presented,
so its module of sections on this affine chart is finitely presented. Apply the object
clause of 05N7 to obtain a finitely presented stage module, realized geometrically by
its associated quasi-coherent sheaf. Lift its finite relation matrix, rather than
choosing arbitrary sheaf data. Finitely many charts give finitely many stages; choose
a common upper bound also above i, and extend scalars on all charts to that stage.
Finite presentation survives extension of scalars; the affine module equivalence and
pullback comparisons supply the displayed component isomorphisms. The pulled-back
charts form a finite affine cover of Xj. For a preorder take the partial-order quotient
of the upper tail; equivalent indices give canonically isomorphic rings. The fixed i
makes this tail nonempty. Empty Xi uses the empty family; zero modules and zero rings
use their zero presentations. No overlap identifications are claimed. -/
theorem exists_finitePresentation_local_object_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u}),
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
      ∃ N : (a : U.I₀) → (U.X a).Modules,
        (∀ a, (N a).IsFinitePresentation) ∧ (∀ a, (N a).IsQuasicoherent) ∧
        (∀ a, Nonempty ((Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅
          (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M)) := by
  sorry

end AlgebraicGeometry
