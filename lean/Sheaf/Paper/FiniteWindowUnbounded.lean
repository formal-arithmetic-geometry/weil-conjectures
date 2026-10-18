/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.Paper.FiniteWindowBounded

/-!
# Lower-tail vanishing without a lower cohomology bound

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-finite-window,
sk-lem-finite-window-unbounded.md and its proof (blueprint: det-finite-window-unbounded).

The two statements give the finite-extension and algebraic-closure coefficient cases.
IndCons is Mathlib's filtered-colimit closure of finite constant-model constructibility.
Dic membership is imposed on every cohomology sheaf in the ordinary derived category.
The Ext hypothesis uses Mathlib's Ext with its standard size convention, canonically
identified with ambient derived morphisms by `CategoryTheory.Abelian.Ext.homAddEquiv`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Lower-tail vanishing for a finite coefficient subextension, with no lower bound on L.
Source: blueprint main-20261015, sk-lem-finite-window-unbounded, statement and proof
(blueprint: det-finite-window-unbounded).

Proof:
1. Set L_n = tau_ge_(-n) L. By det-pe-left-complete-iso and det-pe-products-derived,
L is the fibre of 1-T on the derived product of the L_n.
2. Representable Hom exactness (lem-weil-pbc-hom-into-triangle-exact), its rotations,
and the product universal property give the exact segment
prod Hom(C,L_n[-1]) --(1-t)--> prod Hom(C,L_n[-1]) --> Hom(C,L) --> prod Hom(C,L_n).
Shifts preserve products since they are equivalences.
3. The truncation formulas of def-kun-truncations put every L_n in Dic, supported in
[-n,-d_C-1]. The bounded theorem det-finite-window-bounded gives Hom(C,L_n)=0,
including when that interval is empty.
4. By lem-sf-derived-truncation-triangle the fibre of L_(n+1) --> L_n is
B_n[n+1], where B_n = H^(-n-1)(L) is ind-constructible. Shift by [-1] and apply
representable Hom exactness. Its outer terms are Hom(C,B_n[n]) and Hom(C,B_n[n+1]).
For n>d_C both vanish by det-finite-window-bounded applied to the single-cohomology
objects. Thus the transition G_(n+1) --> G_n, with G_n = Hom(C,L_n[-1]), is bijective.
5. For arbitrary y in prod G_n, set N=d_C+1 and x_N=0. For n>=N recursively set
x_(n+1)=u_n^(-1)(x_n-y_n). For n<N, recursively downwards set
x_n=y_n+u_n(x_(n+1)). Then x_n-u_n(x_(n+1))=y_n for every n, so 1-t is surjective.
6. Exactness of the segment in step 2, surjectivity in step 5 and the vanishing
in step 3 force every morphism C --> L to vanish. -/
theorem finiteWindow_unbounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u})
    (C : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X)
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.continuousMapRingObj E) X,
      IsConstantModelConstructible (Profinite.continuousMapRingObj E) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  sorry

/-- Lower-tail vanishing for the condensed algebraic closure, with no lower bound on L.
Source: blueprint main-20261015, sk-lem-finite-window-unbounded, statement and proof
(blueprint: det-finite-window-unbounded).

Proof:
1. Set L_n = tau_ge_(-n) L. By det-pe-left-complete-iso and det-pe-products-derived,
L is the fibre of 1-T on the derived product of the L_n.
2. Representable Hom exactness (lem-weil-pbc-hom-into-triangle-exact), its rotations,
and the product universal property give the exact segment
prod Hom(C,L_n[-1]) --(1-t)--> prod Hom(C,L_n[-1]) --> Hom(C,L) --> prod Hom(C,L_n).
Shifts preserve products since they are equivalences.
3. The truncation formulas of def-kun-truncations put every L_n in Dic, supported in
[-n,-d_C-1]. The bounded theorem det-finite-window-bounded gives Hom(C,L_n)=0,
including when that interval is empty.
4. By lem-sf-derived-truncation-triangle the fibre of L_(n+1) --> L_n is
B_n[n+1], where B_n = H^(-n-1)(L) is ind-constructible. Shift by [-1] and apply
representable Hom exactness. Its outer terms are Hom(C,B_n[n]) and Hom(C,B_n[n+1]).
For n>d_C both vanish by det-finite-window-bounded applied to the single-cohomology
objects. Thus the transition G_(n+1) --> G_n, with G_n = Hom(C,L_n[-1]), is bijective.
5. For arbitrary y in prod G_n, set N=d_C+1 and x_N=0. For n>=N recursively set
x_(n+1)=u_n^(-1)(x_n-y_n). For n<N, recursively downwards set
x_n=y_n+u_n(x_(n+1)). Then x_n-u_n(x_(n+1))=y_n for every n, so 1-t is surjective.
6. Exactness of the segment in step 2, surjectivity in step 5 and the vanishing
in step 3 force every morphism C --> L to vanish. -/
theorem finiteWindow_unbounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u})
    (C : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X)
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (d_C : ℕ)
    (hExt : ∀ N : pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N →
      ∀ r : ℕ, d_C < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (L : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hL : ∀ q : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (hvanish : ∀ q : ℤ, -(d_C : ℤ) - 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L) := by
  sorry

end AlgebraicGeometry.ProEtale
