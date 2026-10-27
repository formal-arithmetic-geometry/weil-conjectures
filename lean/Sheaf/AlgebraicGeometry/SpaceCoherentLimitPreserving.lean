/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.SpaceFinitePresentationModuleLimit

/-! # Continuity of coherent families with proper support

Source: Stacks Project, quot.tex, Situation 08KB and Lemma 08KD
(blueprint: lem-sfb-space-coherent-limit-preserving).

We use the existing coherent-family category, including its actual tensor comparisons.
The three clauses state essential surjectivity, fullness, and faithfulness of the
comparison from the groupoid of eventual arrows. Specified lifts retain the limit
identifications, so arrow descent is descent of the given arrow, not just some arrow.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.CoherentModuli

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The fibre over an S-scheme, retaining actual modules and their automorphisms.
This is Mathlib's fibre, with no new objects or arrows.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-limit-preserving). -/
abbrev Fiber (f : X ⟶ B) (T : Over S) := Functor.Fiber (category f).p T

/-- An actual tensor-pullback isomorphism over the specified scheme map.
Source: Stacks, Situation 08KB (blueprint: lem-sfb-space-coherent-limit-preserving). -/
abbrev Lift {f : X ⟶ B} {T U : Over S} (a : T ⟶ U)
    (x : Fiber f T) (y : Fiber f U) :=
  {b : x.val ⟶ y.val // (category f).p.IsHomLift a b}

/-- The coherent-family groupoids preserve directed affine limits when B is locally
of finite presentation over S. That hypothesis is tested on every etale scheme chart
of B, using its actual structure map to S. No separatedness of f or B is assumed.

Source: Stacks Project, quot.tex, Lemma 08KD in Situation 08KB
(blueprint: lem-sfb-space-coherent-limit-preserving).

Proof:
1. Apply lem-sfb-space-module-base-change-flat-proper-support to X_T -> T.
   Its local finite type follows from finite presentation and
   lem-sfb-space-flat-proper-fp-locality. Thus restriction preserves all object
   conditions. Pull back an isomorphism and its inverse. The comparisons of
   def-sfb-space-module-tensor-composition satisfy the unit and associativity laws
   on pure tensors, giving the canonical comparison on eventual arrows.
2. Affine stages are qcqs by lem-weil-pbc-affine-scheme-qcqs. Apply
   lem-sfb-lfp-space-scheme-limit-test to B: base maps descend, and equality of
   their restrictions is eventual equality. Pass to a tail to fix a stage base map.
3. The X_i = X times_B T_i are finitely presented over the affines, hence qcqs by
   lem-sfb-space-flat-proper-fp-locality and lem-sfb-space-qcqs-source-products.
   Transitions are affine by lem-sfb-space-affine-locality. The limit is X_T by
   lem-sfb-space-affine-limits-schematic-stages. Use lem-sfb-space-change-base-to-integers
   where a continuity input is stated over the integers; the ringed sites agree.
4. Apply the object clause of lem-sfb-space-fp-module-limit-category. Finite local
   presentation gives quasi-coherence by def-trf-space-quasi-coherent-module and
   remains finitely presented after tensor pullback.
5. Use lem-sfb-space-module-flat-chart-test in both directions to apply
   lem-sfb-space-module-eventually-flat. Use lem-sfb-space-module-proper-carrier-support
   to convert the proper carrier to scheme-theoretic support; finite presentation
   implies finite type and X_T -> T is locally of finite type. Apply
   lem-sfb-space-module-eventually-proper-support and convert back to a proper
   carrier. This gives the first clause, including flatness and proper support.
6. For an arrow, make the two base maps equal eventually by
   lem-sfb-lfp-space-scheme-limit-test. Descend its module isomorphism and inverse
   using the map clause of lem-sfb-space-fp-module-limit-category. Its equality
   clause makes their composites identities at a common later stage. Canonical
   tensor comparisons give the three displayed factorization equations.
7. For two stage arrows equal after restriction, the equality clause of
   lem-sfb-space-fp-module-limit-category makes their maps equal eventually, after
   aligning the base maps by lem-sfb-lfp-space-scheme-limit-test. Conversely a stage
   equality stays equality under pullback. These are exactly the eventual-arrow
   equivalence relation, fullness and faithfulness; step 5 gives essential surjectivity.
-/
theorem limit_preserving (f : X ⟶ B) (_hf : ProperQuotFinitePresentation f)
    (_hB : ∀ U : B.EtaleSite, LocallyOfFinitePresentation U.obj.left.hom)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over S) (_haff : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left)
    (_htrans : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a).left)
    (c : Cone D) (_hc : IsLimit c) :
    (∀ x : Fiber f c.pt, ∃ (i : I) (xi : Fiber f (D.obj (op i))),
      Nonempty (Lift (c.π.app (op i)) x xi)) ∧
    (∀ (i : I) (xi yi : Fiber f (D.obj (op i)))
      (x y : Fiber f c.pt) (px : Lift (c.π.app (op i)) x xi)
      (py : Lift (c.π.app (op i)) y yi) (a : x ⟶ y),
      ∃ (j : I) (hij : i ≤ j) (xj yj : Fiber f (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi)
        (qy : Lift (D.map (homOfLE hij).op) yj yi)
        (rx : Lift (c.π.app (op j)) x xj) (ry : Lift (c.π.app (op j)) y yj)
        (b : xj ⟶ yj),
        rx.val ≫ qx.val = px.val ∧ ry.val ≫ qy.val = py.val ∧
          a.val ≫ ry.val = rx.val ≫ b.val) ∧
    (∀ (i : I) (xi yi : Fiber f (D.obj (op i))) (a b : xi ⟶ yi)
      (x : Fiber f c.pt) (px : Lift (c.π.app (op i)) x xi),
      px.val ≫ a.val = px.val ≫ b.val →
      ∃ (j : I) (hij : i ≤ j) (xj : Fiber f (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi),
        qx.val ≫ a.val = qx.val ≫ b.val) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentModuli
