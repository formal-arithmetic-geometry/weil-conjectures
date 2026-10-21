/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.UniformConstructibleExt
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.Paper.IndHeartIIVanishing

/-!
# Lower-tail vanishing for bounded ind-constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-finite-window,
sk-lem-finite-window-bounded.md and its proof (blueprint: det-finite-window-bounded).

The two statements cover finite subextensions E and the condensed algebraic closure.
IndCons is the replete filtered-colimit closure `ObjectProperty.ind` of finite constant-model
constructibility. Dic membership is imposed on every cohomology sheaf in the ordinary
ambient derived category. Boundedness means finite support of the cohomology sheaves.
Ext uses its standard size convention and `Abelian.Ext.homAddEquiv` identifies it with
shifted ambient derived morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Lower-tail vanishing for bounded complexes with finite-subextension coefficients.
The bound d_C is a chosen nonnegative integer satisfying the uniform constructible Ext
property, rather than a choice of witness from the existence theorem.
Source: blueprint main-20261015, sk-lem-finite-window-bounded, statement and proof
(blueprint: det-finite-window-bounded).

Proof (the four steps of the DAG node):
1. Induct strongly on the finite number of nonzero cohomology sheaves. If it is zero,
a representative is acyclic, and its map from zero is a quasi-isomorphism; localization
(def-weil-abstract-derived-category) therefore makes L isomorphic to zero.
2. If only H^q(L) is nonzero, lem-sf-derived-concentrated-single identifies L with
H^q(L)[-q]. The upper bound forces q <= -d_C-1, hence -q > d_C. Dic membership puts
H^q(L) in IndCons, so det-ind-heart-ii-vanishing and the Ext convention def-pc-ext give
Hom(C,L) = Ext^(-q)(C,H^q(L)) = 0.
3. Otherwise choose the smallest nonzero cohomology degree q_0. By
lem-pc-derived-lower-truncation-step-triangle and def-kun-truncations there is a triangle
A -> L -> B -> A[1], with A = H^(q_0)(L)[-q_0] and B = tau_ge_(q_0+1) L. More precisely,
the canonical triangle has middle term tau_ge_(q_0) L; its map from L is invertible
since it is an isomorphism on all cohomology. Transport along this isomorphism by TR1
(def-weil-triangulated-category). The zero sheaf has a constant filtered presentation,
so A lies in Dic; B lies in Dic by det-ambient-ind-derived-sums(2). Both have the same
upper bound and fewer nonzero cohomology sheaves, so induction kills Hom(C,A), Hom(C,B).
4. For f : C -> L its composite with L -> B is zero. By
lem-weil-pbc-hom-into-triangle-exact(ii), f factors through A. Every map C -> A is zero,
so f is zero. This proves the conclusion. -/
theorem finiteWindow_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u})
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (d_C : ℕ)
    (hExt : ∀ N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X),
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hbounded : {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj L)}.Finite)
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  sorry

/-- Lower-tail vanishing for bounded complexes with condensed algebraic-closure coefficients.
The bound d_C is a chosen nonnegative integer satisfying the uniform constructible Ext
property, rather than a choice of witness from the existence theorem.
Source: blueprint main-20261015, sk-lem-finite-window-bounded, statement and proof
(blueprint: det-finite-window-bounded).

Proof (the four steps of the DAG node):
1. Induct strongly on the finite number of nonzero cohomology sheaves. If it is zero,
a representative is acyclic, and its map from zero is a quasi-isomorphism; localization
(def-weil-abstract-derived-category) therefore makes L isomorphic to zero.
2. If only H^q(L) is nonzero, lem-sf-derived-concentrated-single identifies L with
H^q(L)[-q]. The upper bound forces q <= -d_C-1, hence -q > d_C. Dic membership puts
H^q(L) in IndCons, so det-ind-heart-ii-vanishing and the Ext convention def-pc-ext give
Hom(C,L) = Ext^(-q)(C,H^q(L)) = 0.
3. Otherwise choose the smallest nonzero cohomology degree q_0. By
lem-pc-derived-lower-truncation-step-triangle and def-kun-truncations there is a triangle
A -> L -> B -> A[1], with A = H^(q_0)(L)[-q_0] and B = tau_ge_(q_0+1) L. More precisely,
the canonical triangle has middle term tau_ge_(q_0) L; its map from L is invertible
since it is an isomorphism on all cohomology. Transport along this isomorphism by TR1
(def-weil-triangulated-category). The zero sheaf has a constant filtered presentation,
so A lies in Dic; B lies in Dic by det-ambient-ind-derived-sums(2). Both have the same
upper bound and fewer nonzero cohomology sheaves, so induction kills Hom(C,A), Hom(C,B).
4. For f : C -> L its composite with L -> B is zero. By
lem-weil-pbc-hom-into-triangle-exact(ii), f factors through A. Every map C -> A is zero,
so f is zero. This proves the conclusion. -/
theorem finiteWindow_bounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u})
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (d_C : ℕ)
    (hExt : ∀ N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hbounded : {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj L)}.Finite)
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  sorry

end AlgebraicGeometry.ProEtale
