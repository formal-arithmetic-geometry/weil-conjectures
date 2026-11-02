/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The finite cohomological window for constructible sources

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-lem-finite-window/_section.md and its proof
(blueprint: sk-lem-finite-window).

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

open CategoryTheory.Triangulated CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

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
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-lem-finite-window/_section.md, equation (6.3)
and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the six DAG steps of the node:
1. (sk-cor-ambient-ind-derived, def-kun-truncations, lem-sf-derived-truncation-triangle,
   def-sbc-standard-tstructure-derived-category, def-weil-t-structure,
   lem-weil-pbc-hom-into-triangle-exact) Dic is stable under truncations and shifts;
   replace K by K[m] to work at m = 0. Put A = tau_le(0) K and U = tau_ge(1) K. In the
   triangle A --> K --> U, Hom(C,U) = Hom(C,U[-1]) = 0 since C is <= 0 and U, U[-1]
   are >= 1, so a_K: Hom(C,A) --> Hom(C,K) is bijective.
2. (sk-cor-ind-heart-ii, def-pc-ext, lem-sfb-degreewise-bounded-devissage,
   lem-weil-pbc-hom-into-triangle-exact) Claim (6.4) for bounded L in Dic with
   H^q(L) = 0 for q > -d_C-1: each layer H^q(L)[-q] has Hom(C,H^q(L)[-q]) =
   Ext^(-q)(C,H^q L) = 0 since -q > d_C; devissage over a finite interval
   gives Hom(C,L) = 0.
3. (sk-thm-pe-weakly-contractible-basis, sk-prop-pe-products, sk-prop-pe-left-complete,
   sk-prop-pe-milnor, lem-weil-pbc-hom-into-triangle-exact) For arbitrary such L,
   L = R lim L_n with L_n = tau_ge(-n) L; the Milnor triangle and the product universal
   property give the exact segment
   prod Hom(C,L_n[-1]) --(1-T)--> prod Hom(C,L_n[-1]) --> Hom(C,L)
   --> prod Hom(C,L_n) --(1-T)--> prod Hom(C,L_n).
4. (lem-pc-derived-lower-truncation-step-triangle, lem-weil-pbc-hom-into-triangle-exact,
   def-pc-ext, sk-cor-ind-heart-ii) Step 2 kills every Hom(C,L_n). The triangle
   H^(-n-1)(L)[n+1] --> L_(n+1) --> L_n, shifted by [-1], has outer terms
   Ext^n(C,H^(-n-1) L) and Ext^(n+1)(C,H^(-n-1) L), zero for n > d_C; so the
   transitions G_(n+1) --> G_n of G_n = Hom(C,L_n[-1]) are bijective for n > d_C.
5. (elementary) For N > d_C and any (y_n), put x_N = 0, x_(n+1) = t_n^(-1)(x_n - y_n)
   for n >= N and x_n = y_n + t_n(x_(n+1)) for n < N; so 1-T is surjective on
   prod G_n, and exactness gives Hom(C,L) = 0, proving (6.4) with no lower bound.
6. (lem-sf-derived-truncation-triangle, sk-cor-ambient-ind-derived,
   lem-weil-pbc-hom-into-triangle-exact, def-kun-truncations) Put V = tau_le(-d_C-1) A,
   B = tau_ge(-d_C) A. In V --> A --> B, (6.4) kills Hom(C,V) and Hom(C,V[1]), so
   b_K: Hom(C,A) --> Hom(C,B) is bijective. The equivalence is b_K a_K^(-1); the first
   equation in FiniteWindowAssertions says e(a(f)) = b(f). Functorial truncation gives
   F a_K = a_L F_A and F_B b_K = b_L F_A, hence F_B b_K a_K^(-1) = b_L a_L^(-1) F: the
   naturality equation in FiniteWindowAssertions. Undoing the shift yields (6.3). -/
theorem finiteWindow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
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
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by sorry

/-- The truncation zigzag induces a natural additive equivalence on Hom from C,
for the condensed algebraic closure with finite-subextension-valued sections.
The indexing subtype is the full object class Dic;
its morphisms below are all ambient derived morphisms.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-lem-finite-window/_section.md, equation (6.3)
and proof paragraph 1
(blueprint: sk-lem-finite-window).

Proof, following the six DAG steps of the node:
1. (sk-cor-ambient-ind-derived, def-kun-truncations, lem-sf-derived-truncation-triangle,
   def-sbc-standard-tstructure-derived-category, def-weil-t-structure,
   lem-weil-pbc-hom-into-triangle-exact) Dic is stable under truncations and shifts;
   replace K by K[m] to work at m = 0. Put A = tau_le(0) K and U = tau_ge(1) K. In the
   triangle A --> K --> U, Hom(C,U) = Hom(C,U[-1]) = 0 since C is <= 0 and U, U[-1]
   are >= 1, so a_K: Hom(C,A) --> Hom(C,K) is bijective.
2. (sk-cor-ind-heart-ii, def-pc-ext, lem-sfb-degreewise-bounded-devissage,
   lem-weil-pbc-hom-into-triangle-exact) Claim (6.4) for bounded L in Dic with
   H^q(L) = 0 for q > -d_C-1: each layer H^q(L)[-q] has Hom(C,H^q(L)[-q]) =
   Ext^(-q)(C,H^q L) = 0 since -q > d_C; devissage over a finite interval
   gives Hom(C,L) = 0.
3. (sk-thm-pe-weakly-contractible-basis, sk-prop-pe-products, sk-prop-pe-left-complete,
   sk-prop-pe-milnor, lem-weil-pbc-hom-into-triangle-exact) For arbitrary such L,
   L = R lim L_n with L_n = tau_ge(-n) L; the Milnor triangle and the product universal
   property give the exact segment
   prod Hom(C,L_n[-1]) --(1-T)--> prod Hom(C,L_n[-1]) --> Hom(C,L)
   --> prod Hom(C,L_n) --(1-T)--> prod Hom(C,L_n).
4. (lem-pc-derived-lower-truncation-step-triangle, lem-weil-pbc-hom-into-triangle-exact,
   def-pc-ext, sk-cor-ind-heart-ii) Step 2 kills every Hom(C,L_n). The triangle
   H^(-n-1)(L)[n+1] --> L_(n+1) --> L_n, shifted by [-1], has outer terms
   Ext^n(C,H^(-n-1) L) and Ext^(n+1)(C,H^(-n-1) L), zero for n > d_C; so the
   transitions G_(n+1) --> G_n of G_n = Hom(C,L_n[-1]) are bijective for n > d_C.
5. (elementary) For N > d_C and any (y_n), put x_N = 0, x_(n+1) = t_n^(-1)(x_n - y_n)
   for n >= N and x_n = y_n + t_n(x_(n+1)) for n < N; so 1-T is surjective on
   prod G_n, and exactness gives Hom(C,L) = 0, proving (6.4) with no lower bound.
6. (lem-sf-derived-truncation-triangle, sk-cor-ambient-ind-derived,
   lem-weil-pbc-hom-into-triangle-exact, def-kun-truncations) Put V = tau_le(-d_C-1) A,
   B = tau_ge(-d_C) A. In V --> A --> B, (6.4) kills Hom(C,V) and Hom(C,V[1]), so
   b_K: Hom(C,A) --> Hom(C,B) is bijective. The equivalence is b_K a_K^(-1); the first
   equation in FiniteWindowAssertions says e(a(f)) = b(f). Functorial truncation gives
   F a_K = a_L F_A and F_B b_K = b_L F_A, hence F_B b_K a_K^(-1) = b_L a_L^(-1) F: the
   naturality equation in FiniteWindowAssertions. Undoing the shift yields (6.3). -/
theorem finiteWindow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
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
        ((DerivedCategory.homologyFunctor _ q).obj K)) d_C m := by sorry
end AlgebraicGeometry.ProEtale
