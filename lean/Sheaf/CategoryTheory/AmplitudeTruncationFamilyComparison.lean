/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.CategoryTheory.ArrowExactColimits
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # Uniform finite cohomological windows for families

Source: blueprint sec-six-functors-basics, sk-prop-ctf-finite-proper-localizing.proof.md,
Étale statements and Transfer; Stacks Tags 07D9 and 08J5.
(blueprint: lem-sfb-amplitude-truncation-family-comparison)

Families are diagrams on `Discrete I`. Each of the four arrows below is explicitly
an evaluation of a natural transformation on this diagram category. Thus its naturality
in all morphisms of families is part of its type. `colim` is the ambient derived
coproduct functor, and its action on a transformation is the map induced by coprojections.
The first two transformations take the coproduct before `G`, the last two after `G`.
-/

@[expose] public section

universe uA uB vA vB w dA dB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

open ZeroObject

namespace DerivedCategory

/-- Good truncations give a uniform window `[m-c,m]` and four natural cohomological
comparison isomorphisms, without any boundedness assumption on the input family.

Source: blueprint sec-six-functors-basics, sk-prop-ctf-finite-proper-localizing.proof.md,
Étale statements and Transfer; Stacks Tags 07D9 and 08J5.
(blueprint: lem-sfb-amplitude-truncation-family-comparison)

Proof plan, following the nine steps of the node:
1. In either Grothendieck category, express a coproduct as the filtered colimit of
finite subsums. Finite sums are finite products, and filtered colimits preserve finite
limits by lem-sfb-grothendieck-filtered-finite-limits. Thus coproducts are exact,
including for the empty family.
2. Use lem-kun-grothendieck-derived-coproducts and
src-weil-homology-preserves-exact-colimits to identify the cohomology of an ambient
coproduct with the coproduct of cohomologies, naturally on the specified coprojections.
Hence common cohomological bounds and P-cohomology are preserved by coproducts.
3. Put a = m-c, U = truncLE m K, V = truncGE a U, and T = truncLE (a-1) U.
Good truncation preserves P-cohomology since P is invariant under isomorphisms and
contains zero. It gives U ≤ m, a ≤ V ≤ m, and T ≤ a-1, also after coproducts.
4. Apply lem-sfb-arrow-exact-colimits to the kernels and cokernels defining good
truncation. Their canonical comparisons identify the sums of the truncations with
the corresponding truncations of the sum, compatibly with the actual arrows u and v.
5. Apply G to the distinguished triangle truncLE m L → L → truncGE (m+1) L.
The last term after G is ≥ m+1. The long exact cohomology sequence identifies
H^m(G(u)) as an isomorphism. This applies individually and to the coproduct.
6. Apply G to T → U → truncGE a U. The first term after G is ≤ a-1+c = m-1.
The long exact sequence identifies H^m(G(v)) as an isomorphism, individually and
on the coproduct. These two steps use lem-sf-derived-truncation-triangle and
lem-sf-derived-homology-long-exact; no extension closure of P is used.
7. Transport the conclusions of steps 5-6 through the canonical comparisons in
step 4 to obtain the two maps with coproduct inside G.
8. In the target category use step 2 to identify the cohomology of each coproduct
of G(u) or G(v) with the coproduct of the cohomology maps. Each summand is invertible
by steps 5-6, so these coproduct maps are invertible as well.
9. All arrows are natural transformations: good truncation, coproducts, G and
cohomology preserve the commuting squares, and the inverses are natural. For the
empty family all coproducts are zero, and the additive triangulated functor G
preserves zero. No bound on the original K is used. -/
theorem amplitude_truncation_family_comparison
    (A : Type uA) [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] (hPzero : P 0)
    (hPsum : ∀ (J : Type w) (X : J → A), (∀ j, P (X j)) → P (∐ X))
    (G : DerivedCategory A ⥤ DerivedCategory B) [G.CommShift ℤ] [G.IsTriangulated]
    (c : ℕ)
    (hGge : ∀ (L : DerivedCategory A) (a : ℤ), L.IsGE a → (G.obj L).IsGE a)
    (hGle : ∀ (L : DerivedCategory A) (b : ℤ), L.IsLE b →
      (∀ j : ℤ, P ((homologyFunctor A j).obj L)) → (G.obj L).IsLE (b + (c : ℤ)))
    (I : Type w) (K : Discrete I ⥤ DerivedCategory A)
    (hK : ∀ (s : I) (j : ℤ), P ((homologyFunctor A j).obj (K.obj ⟨s⟩))) (m : ℤ) :
    (∀ s : I,
      ((TStructure.t.truncGE (m - (c : ℤ))).obj
        ((TStructure.t.truncLE m).obj (K.obj ⟨s⟩))).IsGE (m - (c : ℤ)) ∧
      ((TStructure.t.truncGE (m - (c : ℤ))).obj
        ((TStructure.t.truncLE m).obj (K.obj ⟨s⟩))).IsLE m ∧
      ∀ j : ℤ, P ((homologyFunctor A j).obj
        ((TStructure.t.truncGE (m - (c : ℤ))).obj
          ((TStructure.t.truncLE m).obj (K.obj ⟨s⟩))))) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory A)).map
        (TStructure.t.truncLEι m)) (colim ⋙ G ⋙ homologyFunctor B m)).app K) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory A)).map
        (whiskerLeft (TStructure.t.truncLE m) (TStructure.t.truncGEπ (m - (c : ℤ)))))
      (colim ⋙ G ⋙ homologyFunctor B m)).app K) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory B)).map
        (whiskerRight (TStructure.t.truncLEι m) G))
      (colim ⋙ homologyFunctor B m)).app K) ∧
    IsIso ((whiskerRight
      ((whiskeringRight (Discrete I) (DerivedCategory A) (DerivedCategory B)).map
        (whiskerRight
          (whiskerLeft (TStructure.t.truncLE m) (TStructure.t.truncGEπ (m - (c : ℤ)))) G))
      (colim ⋙ homologyFunctor B m)).app K) := by
  sorry

end DerivedCategory
