/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Left-acyclic objects in short exact sequences

Source: Stacks Project, Derived Categories, dual of Tag 015D(1)--(2), with
Tags 015C, 05S8 and 05S9 (blueprint: lem-trf-left-acyclic-short-exact).

Left acyclicity means invertibility of the universal total-derived counit on the
complex concentrated in degree zero. The pointwise definedness assumption expands
`Functor.IsTriangulatedLeftDerivedDefinedAt` at the fixed quasi-isomorphism system,
as in `boundedAbove_acyclic_leftDerived_computation`: it retains essential constancy
of the denominator pro-diagrams at every unbounded homotopy-category object.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Left-acyclic objects are closed under extensions and kernels of epimorphisms
between left-acyclic objects. In both cases the specified image sequence is short exact.
Source: Stacks Project, Derived Categories, dual of Tag 015D(1)--(2), with
Tags 015C, 05S8 and 05S9 (blueprint: lem-trf-left-acyclic-short-exact).

Here `S.X₁`, `S.X₂`, `S.X₃` are respectively the subobject, middle object and quotient.
`IsLeftDerivedFunctor` makes `ε` the universal counit, not an arbitrary comparison.
`hdefined` is the essential-constancy condition of the recorded pointwise derived-value
definition, expanded so that saturation and exactness of the fixed homotopy functor
are consequences of additivity rather than extra hypotheses. Passing from `Qh` to
the cochain localization `Q` uses its canonical factorization through the homotopy category.

Proof (the six steps of the node):
1. Put `T^q(M) = H^q(LV(Q(M[0])))`. The duals of Tags 05TC, 05TD and 015C,
   `lem-trf-left-derived-object-cohomology`, give zero for `q > 0`, the natural
   isomorphism `T^0(M) ≅ V(M)` induced by the actual counit, and acyclicity exactly
   when `T^q(M)` vanishes for every `q < 0`.
2. Applying additive `V` preserves the homotopy equation, signed shifts and cone
   differential matrices, hence the homotopy functor is exact. The input
   `lem-trf-additive-homotopy-category-triangulated` and
   `lem-pur-quasi-isos-saturated-triangulated` give Situation 05S8 and exactness of `Qh`.
3. Apply `lem-sf-derived-ses-triangle` to `S`. By everywhere-definedness and
   `lem-pur-left-derived-exact-when-defined`, its image under `LV` is distinguished.
4. The long exact sequence `lem-sf-derived-homology-long-exact` contains
   `T^(q-1)(S.X₃) → T^q(S.X₁) → T^q(S.X₂) → T^q(S.X₃) → T^(q+1)(S.X₁)`.
   Its degree-zero tail is `T^(-1)(S.X₃) → V(S.X₁) → V(S.X₂) → V(S.X₃) → 0`.
   Naturality of the counit-induced degree-zero isomorphisms identifies the arrows
   with exactly `V.map S.f` and `V.map S.g`.
5. If `S.X₁` and `S.X₃` are acyclic, the outer zero terms force `T^q(S.X₂) = 0`
   for `q < 0`. Thus `S.X₂` is acyclic. Also `T^(-1)(S.X₃) = 0`, so the image
   sequence is short exact.
6. If `S.X₂` and `S.X₃` are acyclic, for `q < 0` use the exact segment
   `T^(q-1)(S.X₃) → T^q(S.X₁) → T^q(S.X₂)`. Both outer terms vanish, including
   when `q = -1`, so `S.X₁` is acyclic. The same degree-zero tail is short exact. -/
theorem leftAcyclic_shortExact
    (A : Type uA) (B : Type uB) [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [EnoughProjectives A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteColimits V]
    (LV : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ LV ⟶
      V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hLV : LV.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (hdefined : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ Y : DerivedCategory B, IsEssentiallyConstantProDiagram
        (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙ Over.forget X ⋙
            V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) Y)
    (S : ShortComplex A) (hS : S.ShortExact) :
    (IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.X₁)) →
      IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.X₃)) →
        IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.X₂)) ∧
          (S.map V).ShortExact) ∧
    (IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.X₂)) →
      IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.X₃)) →
        IsIso (ε.app ((CochainComplex.singleFunctor A 0).obj S.X₁)) ∧
          (S.map V).ShortExact) := by
  sorry

end CategoryTheory
