/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Products and sequential derived limits of open extensions

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
`det-sf-open-closed-extension-zero-limits`, clauses (1)--(3); Stacks Project,
Tags 09BN, 0152, 070I and 08TC
(blueprint: det-sf-open-closed-extension-zero-limits).

The ring sheaf is an arbitrary monoid object in abelian sheaves. The module functors
are the recorded open-closed module-object functors, without commutative or constant
coefficient hypotheses. Derived categories use the standard localization universe.
The closed localization is descended as a composite, so no independent choice of a
localization on the closed stratum is needed.

## Main definitions

* `ringSheafDerivedCategory`: the existing derived category in its standard universe.
* `ringSheafDerivedOpenExtension`: termwise descent of the recorded exact open extension.
* `ringSheafDerivedDirectImage`: the recorded total right derived functor of direct image.
* `ringSheafDerivedClosedLocalization`: termwise descent of the exact composite `i_* i^*`.

## Main statement

* `proEtale_openExtension_products_derivedLimits`: the natural triangle, preservation of
  derived products and sequential Roos limits, and preservation of sheaf products.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The unbounded derived category of modules over an arbitrary pro-etale ring sheaf,
using the standard localization of the recorded module category. This is only a transparent
specialization of `DerivedCategory`, not a new localization or module category.
Source: Stacks, Tag 05RU; blueprint clause (1)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
abbrev ringSheafDerivedCategory (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  @DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
    _ _ (HasDerivedCategory.standard _)

/-- The inherited additive shifts on the standard derived category, packaged for the
Roos-limit interface which takes the whole integer-indexed family as one instance.
Source: Stacks, Tags 05RU and 08TC; blueprint clause (2)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
instance ringSheafDerivedCategory_shiftAdditive (X : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ∀ n : ℤ, (shiftFunctor (ringSheafDerivedCategory X B) n).Additive :=
  fun _ ↦ inferInstance

/-- Exact open extension applied termwise and descended through quasi-isomorphisms.
Its coefficients on the open are the actual inverse image of `B`.
Source: Stacks, Tags 03DI, 03DJ and 015F; blueprint clauses (1)--(2)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
def ringSheafDerivedOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B) ⥤
      ringSheafDerivedCategory X B :=
  letI := HasDerivedCategory.standard
    (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) ((upperStar Ab.{u + 1} j).obj B))
  letI := HasDerivedCategory.standard (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
  (ringSheafOpenExtension j B).mapDerivedCategory

/-- Total right derived direct image over the inverse-image ring. The existence proof
passed to the recorded universal-pair construction uses the functorial K-injective
replacement in the Grothendieck abelian module category. Thus the result is determined
up to its unique unit-compatible isomorphism and computed on every K-injective resolution.
Source: Stacks, Tags 070K and 070Y; blueprint clause (1)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
def ringSheafDerivedDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafDerivedCategory T ((upperStar Ab.{u + 1} f).obj B) ⥤
      ringSheafDerivedCategory X B :=
  letI := HasDerivedCategory.standard
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B))
  letI := HasDerivedCategory.standard (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
  letI := Mod.isGrothendieckAbelian.{u + 1} ((upperStar Ab.{u + 1} f).obj B)
  (ringSheafDirectImage f B).rightDerivedFunctorOfQuasiIsoResolutions
    (fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u + 1} _).obj K,
      (CochainComplex.toKInjectiveResolution.{u + 1} _).app K, inferInstance,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} _ K).2⟩)

/-- Termwise descent of `i_* i^*` for the specified complementary immersions. Exactness
of `i_*` is the recorded open-closed sequence theorem; inverse image is exact on carriers.
On every representative this is exactly the third term in the blueprint's triangle,
with the ring on the closed stratum equal to the inverse image of `B`.
Source: Stacks, Tags 09BM, 09AH and 015F; blueprint clause (1)
(blueprint: det-sf-open-closed-extension-zero-limits). -/
def ringSheafDerivedClosedLocalization {X Z U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafDerivedCategory X B ⥤ ringSheafDerivedCategory X B :=
  letI := HasDerivedCategory.standard (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B)
  letI : PreservesFiniteColimits (ringSheafDirectImage i B) :=
    (proEtale_openClosed_sequence_ring_sheaf i j hU B).2.2.2.2.2.2.1
  letI : PreservesFiniteLimits (ringSheafInverseImage i B ⋙ ringSheafDirectImage i B) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (ringSheafInverseImage i B ⋙ ringSheafDirectImage i B) :=
    comp_preservesFiniteColimits _ _
  (ringSheafInverseImage i B ⋙ ringSheafDirectImage i B).mapDerivedCategory

/-- Open extension has a distinguished triangle natural in the input, preserves small
products on both derived categories and module sheaves, and sends every sequential Roos
limit to a sequential Roos limit. The existential product instance in the sequential clause
asserts existence of the image product; it imposes no additional hypothesis on the sequence.

Source: Weil blueprint, det-sf-open-closed-extension-zero-limits, clauses (1)--(3);
Stacks, Tags 09BN, 0152, 070I and 08TC
(blueprint: det-sf-open-closed-extension-zero-limits).

Proof:
1. The size convention fixes the sites and coefficient universes. The module categories
   are Grothendieck abelian (lem-weil-pbc-ring-sheaves-grothendieck), so
   lem-sfb-grothendieck-k-injective gives a K-injective representative J of K.
   def-sfb-right-derived-functor computes Rj_*K by j_*J. The exact sheaf functors from
   det-sf-open-closed-sequence-ring-sheaf and det-sf-open-closed-pullback-limits descend
   termwise and are triangulated by lem-sf-exact-functor-derived-triangulated.
2. Apply the open-closed sheaf sequence in each degree to j_*J. On every open-site
   object V, V times_X U = V, naturally and compatibly with the coefficient actions;
   hence j^*j_*J = J. The resulting short exact sequence of complexes gives the displayed
   triangle by lem-weil-pbc-complex-ses-triangle. Its boundary is natural on complexes.
   Compute derived morphisms on K-injectives using lem-weil-pbc-kinjective-hom-derived;
   additive functors preserve homotopies, so the three arrows are natural on D(U).
3. The same sheaf sequence identifies j_!N with the kernel of j_*N to i_*i^*j_*N.
   Sheaf products are sectionwise. Direct image j_* preserves them by evaluation on
   fibre products, i_* preserves them by its adjunction, and i^* preserves them by
   det-sf-open-closed-pullback-limits. Naturality identifies the product of the unit maps
   with the unit on the product. Kernels commute with products sectionwise, giving
   the canonical product comparison isomorphism, including the empty product.
4. det-pe-products-derived identifies derived products with termwise products on both
   sites. Apply the sheaf comparison degreewise to representatives. Its naturality in
   the differentials makes it a chain isomorphism, and its composites with every
   projection identify its localization with the canonical derived product comparison.
5. For any sequence put P = product K_n and let s be its transition shift. The canonical
   comparison phi: j_!P to product j_!K_n commutes with s: compose with each projection
   and use pr_n s = pr_(n+1) followed by t_n. Additivity gives compatibility with 1-s.
   Apply the triangulated j_! to any Roos triangle of L and transport its two product
   terms through phi. This is the Roos triangle of j_!L, as in def-weil-derived-limit.
   Products give existence by lem-weil-derived-limit-existence; any other chosen image
   Roos limit is isomorphic, with no canonical choice of cone asserted. -/
theorem proEtale_openExtension_products_derivedLimits
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    (∃ (a : ringSheafDerivedOpenExtension j B ⟶ ringSheafDerivedDirectImage j B)
      (b : ringSheafDerivedDirectImage j B ⟶ ringSheafDerivedDirectImage j B ⋙
        ringSheafDerivedClosedLocalization i j hU B)
      (c : ringSheafDerivedDirectImage j B ⋙ ringSheafDerivedClosedLocalization i j hU B ⟶
        ringSheafDerivedOpenExtension j B ⋙ shiftFunctor (ringSheafDerivedCategory X B) (1 : ℤ)),
      ∀ K, Triangle.mk (a.app K) (b.app K) (c.app K) ∈
        distTriang (ringSheafDerivedCategory X B)) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I)
      (ringSheafDerivedOpenExtension j B)) ∧
    (∀ (K : ℕ → ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B))
      (t : ∀ n : ℕ, K (n + 1) ⟶ K n) [HasProduct K]
      (L : ringSheafDerivedCategory U ((upperStar Ab.{u + 1} j).obj B)),
      IsDerivedLimit t L →
      Exists fun [hP : HasProduct (fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).obj (K n))] ↦
        IsDerivedLimit (K := fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).obj (K n))
          (fun n : ℕ ↦ (ringSheafDerivedOpenExtension j B).map (t n))
          ((ringSheafDerivedOpenExtension j B).obj L)) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I) (ringSheafOpenExtension j B)) := by
  sorry

end AlgebraicGeometry.ProEtale
