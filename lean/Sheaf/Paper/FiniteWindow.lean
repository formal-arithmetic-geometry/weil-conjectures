/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.UniformConstructibleExt
import Sheaf.Paper.FiniteWindowUnbounded
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The finite cohomological window for constructible sources

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-finite-window,
statement and sk-lem-finite-window.proof.md (blueprint: sk-lem-finite-window).

The two coefficient cases use the ordinary unbounded derived category of module sheaves.
The predicate indexing the equivalences is precisely Dic: every cohomology sheaf is an
ambient small filtered colimit of finite constant-model constructible sheaves.
`FiniteWindowAssertions` specifies the truncation zigzag and naturality in K.
No lower or upper cohomological bound on K is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The finite-window conclusion, including its canonical-map characterization and
naturality on a full class P of derived objects. This only packages the two equations
in the statement; it chooses no map or inverse.
Source: blueprint main-20261015, sk-lem-finite-window, displayed natural isomorphism
(blueprint: sk-lem-finite-window). -/
def FiniteWindowAssertions
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{t} A]
    (C : A) (P : ObjectProperty (DerivedCategory A)) (d_C : ℕ) (m : ℤ) : Prop :=
    ∃ e : ∀ K : {K : DerivedCategory A // P K},
      ((DerivedCategory.singleFunctor _ 0).obj C ⟶ K.val⟦m⟧) ≃+
        ((DerivedCategory.singleFunctor _ 0).obj C ⟶
          ((DerivedCategory.TStructure.t.truncGE (m - (d_C : ℤ))).obj
            ((DerivedCategory.TStructure.t.truncLE m).obj K.val))⟦m⟧),
      (∀ K, ∀ f : (DerivedCategory.singleFunctor _ 0).obj C ⟶
          ((DerivedCategory.TStructure.t.truncLE m).obj K.val)⟦m⟧,
        e K (f ≫ ((DerivedCategory.TStructure.t.truncLEι m).app K.val)⟦m⟧') =
          f ≫ ((DerivedCategory.TStructure.t.truncGEπ (m - (d_C : ℤ))).app
            ((DerivedCategory.TStructure.t.truncLE m).obj K.val))⟦m⟧') ∧
      (∀ K L, ∀ (f : K.val ⟶ L.val)
          (g : (DerivedCategory.singleFunctor _ 0).obj C ⟶ K.val⟦m⟧),
        e L (g ≫ f⟦m⟧') = e K g ≫
          ((DerivedCategory.TStructure.t.truncLE m ⋙
            DerivedCategory.TStructure.t.truncGE (m - (d_C : ℤ))).map f)⟦m⟧')

/-- The truncation zigzag induces a natural additive equivalence on Hom from C,
for a finite subextension of the fixed algebraic closure. The indexing subtype is
the full object class Dic;
its morphisms below are all ambient derived morphisms.
Source: blueprint main-20261015, sk-lem-finite-window, statement and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the four DAG steps:
1. Put A = tau_le(m) K, U = tau_ge(m+1) K, V = tau_le(m-d_C-1) A,
   B = tau_ge(m-d_C) A. The canonical triangles A --> K --> U and V --> A --> B
   are distinguished (lem-sf-derived-truncation-triangle). Good truncation cohomology
   formulas (def-kun-truncations) keep A,V and their shifts in Dic: each cohomology
   sheaf is a cohomology sheaf of K or zero, and zero is constructible.
2. The standard t-structure (def-sbc-standard-tstructure-derived-category) and its
   orthogonality (def-weil-t-structure) kill Hom(C,U[m]) and Hom(C,U[m-1]). Applying
   representable Hom exactness (lem-weil-pbc-hom-into-triangle-exact) to the first
   triangle and its rotations makes a: Hom(C,A[m]) --> Hom(C,K[m]) bijective.
3. V[m] and V[m+1] have cohomology zero above -d_C-1 and -d_C-2 respectively.
   det-finite-window-unbounded kills Hom from C to both, without any lower bound.
   Representable Hom exactness for the second triangle and its rotations makes
   b: Hom(C,A[m]) --> Hom(C,B[m]) bijective.
4. The additive equivalence is b composed with the inverse of a; the first equation
   in FiniteWindowAssertions says e(a(f))=b(f). For K --> L, functoriality
   of the canonical truncations
   gives F a_K = a_L F_A and F_B b_K = b_L F_A. Consequently
   F_B b_K a_K^(-1) = b_L a_L^(-1) F. This is the naturality equation
   in FiniteWindowAssertions. -/
theorem finiteWindow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u})
    (C : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X)
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X,
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (m : ℤ) :
    FiniteWindowAssertions C (fun K ↦ ∀ q : ℤ,
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by
  sorry

/-- The truncation zigzag induces a natural additive equivalence on Hom from C,
for the condensed algebraic closure with finite-subextension-valued sections.
The indexing subtype is the full object class Dic;
its morphisms below are all ambient derived morphisms.
Source: blueprint main-20261015, sk-lem-finite-window, statement and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the four DAG steps:
1. Put A = tau_le(m) K, U = tau_ge(m+1) K, V = tau_le(m-d_C-1) A,
   B = tau_ge(m-d_C) A. The canonical triangles A --> K --> U and V --> A --> B
   are distinguished (lem-sf-derived-truncation-triangle). Good truncation cohomology
   formulas (def-kun-truncations) keep A,V and their shifts in Dic: each cohomology
   sheaf is a cohomology sheaf of K or zero, and zero is constructible.
2. The standard t-structure (def-sbc-standard-tstructure-derived-category) and its
   orthogonality (def-weil-t-structure) kill Hom(C,U[m]) and Hom(C,U[m-1]). Applying
   representable Hom exactness (lem-weil-pbc-hom-into-triangle-exact) to the first
   triangle and its rotations makes a: Hom(C,A[m]) --> Hom(C,K[m]) bijective.
3. V[m] and V[m+1] have cohomology zero above -d_C-1 and -d_C-2 respectively.
   det-finite-window-unbounded kills Hom from C to both, without any lower bound.
   Representable Hom exactness for the second triangle and its rotations makes
   b: Hom(C,A[m]) --> Hom(C,B[m]) bijective.
4. The additive equivalence is b composed with the inverse of a; the first equation
   in FiniteWindowAssertions says e(a(f))=b(f). For K --> L, functoriality
   of the canonical truncations
   gives F a_K = a_L F_A and F_B b_K = b_L F_A. Consequently
   F_B b_K a_K^(-1) = b_L a_L^(-1) F. This is the naturality equation
   in FiniteWindowAssertions. -/
theorem finiteWindow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u})
    (C : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X)
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (m : ℤ) :
    FiniteWindowAssertions C (fun K ↦ ∀ q : ℤ,
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by
  sorry

end AlgebraicGeometry.ProEtale
