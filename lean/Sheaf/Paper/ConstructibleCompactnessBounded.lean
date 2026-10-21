/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.Paper.DetIndHeartIISums
import Sheaf.Paper.AmbientIndDerivedSums

/-!
# Constructible compactness for uniformly bounded ind-constructible families

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness/sk-thm-constructible-compactness-bounded.md
(blueprint: det-constructible-compactness-bounded).

IndCons is `ObjectProperty.ind` of finite constant-model constructibility; membership in
Dic is imposed on every cohomology sheaf. All complexes, morphisms and coproducts are in
the ordinary unbounded derived category. A sum is specified by a colimit cofan, whose
injections define the comparison. Existence of this cofan is included in the conclusion;
any other coproduct gives the same assertion by the unique compatible isomorphism.

The signatures use only the coefficient objects and ordinary derived module categories
reexported by CondensedConstantConstructibility. They do not require the six-functor
restriction framework; omitting that unrelated import keeps this interface within the
60-second single-file compilation budget. The chosen localization is bound explicitly
at the fixed coefficient universe, avoiding repeated normalization of its construction.
This is only a choice of derived-category presentation, supplied by the existing
Grothendieck abelian instance, not an additional mathematical hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe t w v u

open CategoryTheory CategoryTheory.Limits DirectSum

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Classical in
/-- The additive comparison induced by the shifted coprojections of a cofan in an
ordinary derived category, with the source sheaf in degree zero. On a finitely supported
tuple it is the sum of composites with these shifted coprojections. The convention is
`(K[s])^n = K^(n+s)`. Source: blueprint main-20261015,
sk-thm-constructible-compactness-bounded, displayed alpha_s
(blueprint: det-constructible-compactness-bounded). -/
noncomputable def constructibleBoundedComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type t} (C : A) (K : I → DerivedCategory A) (c : Cofan K) (s : ℤ) :
    (⨁ i : I, ((DerivedCategory.singleFunctor A 0).obj C ⟶ (K i)⟦s⟧)) →+
      ((DerivedCategory.singleFunctor A 0).obj C ⟶ c.pt⟦s⟧) :=
  DirectSum.toAddMonoid fun i ↦
    Preadditive.rightComp _ ((shiftFunctor (DerivedCategory A) s).map (c.inj i))

open Classical in
/-- A constructible sheaf over a finite coefficient subextension commutes with coproducts
of ind-constructible complexes in a common cohomological interval, in every shift.
Source: blueprint main-20261015, sk-thm-constructible-compactness-bounded, statement
(blueprint: det-constructible-compactness-bounded).

Proof: Induct on the nonnegative width b-a, simultaneously for every integer shift.
For width zero, the truncation inclusion and the projection to H^a(K)[-a] are
quasi-isomorphisms by lem-weil-pbc-truncation-cohomology and
lem-weil-pbc-truncation-triangle, so they identify K with its one-term cohomology
complex. By det-def-localizing-closure-existence, sums are termwise and commute with
shifts. The comparison is the Ext^(s-a) sum comparison of det-ind-heart-ii-sums.
For positive width, the truncation triangle has terms tau_le_(b-1) K, K, H^b(K)[-b].
The outer terms have the smaller respective bounds [a,b-1] and [b,b], and remain
in Dic by det-ambient-ind-derived-sums. The sum of these triangles is distinguished
by det-def-localizing-closure-existence. Apply lem-weil-pbc-hom-into-triangle-exact
and rotate to obtain the five-term Hom sequences with terms B[s-1], A[s], K[s],
B[s], A[s+1]. Their direct sum is exact, by choosing preimages on the finite support.
Coprojection equations, including the shifted boundary equation, give a commutative
ladder to the sequence for the sum triangle. Induction makes its four outer vertical
maps bijective. For injectivity of the middle map, lift a kernel element to the
second term, lift its image from the first term, and subtract; outer injectivity
makes the lift a boundary. For surjectivity, lift the image in the fourth term,
use injectivity at the fifth term to lift it from the middle term, and correct
the resulting difference using surjectivity at the second term. This proves the
middle comparison bijective. Empty families are included, giving zero groups. -/
theorem constructible_compactness_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1}
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))]
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (a b : ℤ) (hab : a ≤ b) (I : Type (u + 1))
    (K : I → DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hK : ∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i)))
    (hbound : ∀ (i : I) (n : ℤ), n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ s : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c s) := by
  sorry

open Classical in
/-- The same bounded-family comparison for the condensed algebraic closure, whose sections
have values in a finite subextension. Source: blueprint main-20261015,
sk-thm-constructible-compactness-bounded, statement, Lambda = Qlb
(blueprint: det-constructible-compactness-bounded).

Proof: Induct on b-a, with all shifts in the induction assertion. Width zero identifies
each K with H^a(K)[-a] using the quasi-isomorphisms supplied by
lem-weil-pbc-truncation-cohomology and lem-weil-pbc-truncation-triangle. Termwise sums
and shifts from det-def-localizing-closure-existence identify the comparison with
Ext^(s-a), and det-ind-heart-ii-sums applies also to this coefficient ring.
For positive width use the triangle tau_le_(b-1) K -> K -> H^b(K)[-b]. Its outer terms
lie in Dic with bounds [a,b-1] and [b,b] by det-ambient-ind-derived-sums. Sum the
triangles using det-def-localizing-closure-existence. The Hom exactness of
lem-weil-pbc-hom-into-triangle-exact and rotations give the five terms B[s-1], A[s],
K[s], B[s], A[s+1]. Taking their sums remains exact since all tuples have finite
support. The coprojection identities, including the boundary identity, make the
comparison ladder commute. Induction identifies the four outer vertical maps.
For a kernel element at the middle, lift from the second term; its image is a
boundary from the first term, which lifts, and outer injectivity kills the original
element. For a target middle element, lift its fourth-term image; injectivity on
the fifth term permits a middle lift; the remaining difference lifts from the second
term, giving the desired preimage. This proves bijectivity in every shift and includes
the empty family. -/
theorem constructible_compactness_bounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1}
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))]
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (a b : ℤ) (hab : a ≤ b) (I : Type (u + 1))
    (K : I → DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : ∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i)))
    (hbound : ∀ (i : I) (n : ℤ), n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ s : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c s) := by
  sorry

end AlgebraicGeometry.ProEtale
