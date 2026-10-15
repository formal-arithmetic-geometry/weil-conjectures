/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Paper.SiteSheafificationSectionsLocal

/-!
# Injective module sheaves on a ringed-site hypercover

Source: Stacks Project, Hypercoverings, Tags 01GE and 01GW, ringed-module analogue
(blueprint: lem-weil-pbc-ringed-hypercover-injective-augmentation).

The conclusion is the explicit exact-sequence formulation of the augmentation
quasi-isomorphism. The matching hypothesis is expressed by local lifting of every
compatible lower-simplex tuple over the augmentation object. This includes degree zero.
-/

@[expose] public section

universe u v r

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory

/-- The canonical augmented alternating section sequence of an injective module sheaf
on a representable hypercover is exact, without affineness or weak contractibility.

Source: Stacks Project, Hypercoverings, Tags 01GE and 01GW, ringed-module analogue
(blueprint: lem-weil-pbc-ringed-hypercover-injective-augmentation).

The matching condition says that each tuple of lower simplices over `w : T ⟶ W`
lifts on a covering sieve. For `n = 0` there are no lower simplices. For `n = 1`
it says that two vertices with the same augmentation lift locally to an edge.
In higher degrees it is local surjectivity onto the finite matching limit;
including all lower simplex operators includes the degenerate faces determined
by the proper faces. On a subcanonical site this is exactly the sheaf-epimorphism
condition, by the sectionwise-limit and locally-surjective-epi lemmas in the proof DAG.

Proof for stage 3, following the node's eight steps:
1. Form represented free module presheaves P_A(V) = R(V)[Hom(V,A)] using
   lem-weil-pbc-free-yoneda-presheaf-module, and sheafify using
   def-weil-presheaf-modules-sheafification. Alternating faces square to zero.
2. A cycle has finite support. Close its labels under faces and augmentation.
   Lift the finitely many base labels locally using the degree-zero covering;
   refine successively, using def-weil-pbc-sites-and-cohomology.
3. Inductively prescribe cone faces. The simplicial identities make them compatible.
   By lem-weil-pbc-site-sheaf-sets-limits-sectionwise and
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective, lift them locally. Only finitely
   many successive refinements are needed in each degree.
4. Extend the cone maps on the original finite label sets. The alternating cone
   identity gives boundary times cone plus cone times boundary equal to restriction.
   Thus each cycle is locally a boundary, even when labels coalesce on restriction.
5. Apply lem-weil-pbc-site-r-module-presheaf-sheafification-exact with fixed ring Z
   to the underlying abelian complex, not with the variable ring sheaf R.
   Use lem-pc-sites-sheafification-underlying-sets and
   lem-weil-pbc-site-sheafification-sections-local to deduce zero homology sheaves.
   Hence the represented free module sheaf resolution is exact.
6. Sheafification adjunction and free Yoneda identify Hom(F_A,I) with I(A),
   by evaluation at the identity. Precomposition gives exactly the displayed sums
   and the canonical restriction augmentation.
7. By def-sp-injective-resolutions, a dual cocycle factors through the preceding
   image and extends to the preceding free sheaf. Thus it is a boundary.
   The final free-sheaf epimorphism makes the left augmentation injective.
8. Naturality over W and semilinearity make every displayed map R(W)-linear,
   with the action on I(U_n) restricted along e_n. Thus the same kernel-image
   equalities hold as R(W)-modules. This exact augmented sequence is equivalent
   to the asserted quasi-isomorphism (def-weil-abstract-derived-category), after
   putting zero in negative degrees. -/
theorem ringedHypercover_injective_augmentation_exact
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.toGrothendieck.Subcanonical]
    (R : Sheaf J.toGrothendieck CommRingCat.{max u r})
    (I : ringedSiteModules.{max u v r}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R)) [Injective I]
    (W : C) (U : SimplicialObject C)
    (e : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj W)
    (hcover : ∀ (n : ℕ) (T : C) (w : T ⟶ W)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n →
        (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.obj (op Δ))),
      (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ e.app (op Δ) = w) →
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ U.map α.op = p Δ' h' (α ≫ θ)) →
      ∃ S : Sieve T, S ∈ J.toGrothendieck T ∧
        ∀ (V : C) (f : V ⟶ T), S f →
          ∃ t : V ⟶ U _⦋n⦌,
            t ≫ e.app (op (SimplexCategory.mk n)) = f ≫ w ∧
            ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
              t ≫ U.map θ.op = f ≫ p Δ h θ) :
    Function.Injective (I.val.map (e.app (op (SimplexCategory.mk 0))).op) ∧
    Function.Exact
      (I.val.map (e.app (op (SimplexCategory.mk 0))).op)
      (fun s : I.val.obj (op (U _⦋0⦌)) ↦
        ∑ j : Fin 2, (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s) ∧
    ∀ n : ℕ, Function.Exact
      (fun s : I.val.obj (op (U _⦋n⦌)) ↦
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s)
      (fun s : I.val.obj (op (U _⦋n + 1⦌)) ↦
        ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • I.val.map (U.δ j).op s) := by
  sorry

end CategoryTheory
