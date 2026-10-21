/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Composition of K-injective-normalized derived comparisons

Source: Stacks Project, derived.tex, Tag 070Y (`lemma-K-injective-defined`), and the
explicit successive-resolution composition argument in the DAG
(blueprint: lem-sf-normalized-derived-comparison-composition).

The normalization uses the shared resolution and localization identifications. No exact
restriction functor is required to preserve K-injective complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u0 u1 u2 v0 v1 v2 w0 w1 w2
universe uA0 uA1 uA2 uB0 uB1 uB2 vA0 vA1 vA2 vB0 vB1 vB2
universe wA0 wA1 wA2 wB0 wB1 wB2

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The canonical localization identification for a specified equality of exact functors.
Source: the canonical localization identifications stipulated in the composition statement;
Stacks Tag 070Y (blueprint: lem-sf-normalized-derived-comparison-composition).
This is the existing induced equality isomorphism followed by the existing composition
isomorphism, with the exactness instances of the composite supplied explicitly. -/
noncomputable def normalizedDerivedComparisonCompositionLocalizationIso
    {C0 : Type u0} {C1 : Type u1} {C2 : Type u2}
    [Category.{v0} C0] [Category.{v1} C1] [Category.{v2} C2]
    [Abelian C0] [Abelian C1] [Abelian C2]
    [HasDerivedCategory.{w0} C0] [HasDerivedCategory.{w1} C1]
    [HasDerivedCategory.{w2} C2]
    (r02 : C2 ⥤ C0) (r12 : C2 ⥤ C1) (r01 : C1 ⥤ C0)
    [r02.Additive] [r12.Additive] [r01.Additive]
    [PreservesFiniteLimits r02] [PreservesFiniteColimits r02]
    [PreservesFiniteLimits r12] [PreservesFiniteColimits r12]
    [PreservesFiniteLimits r01] [PreservesFiniteColimits r01]
    (e : r02 = r12 ⋙ r01) :
    r02.mapDerivedCategory ≅ r12.mapDerivedCategory ⋙ r01.mapDerivedCategory :=
  letI := comp_preservesFiniteLimits r12 r01
  letI := comp_preservesFiniteColimits r12 r01
  mapDerivedCategoryNatIso (eqToIso e) ≪≫ mapDerivedCategoryCompIso r12 r01

/-- Precisely the supplied normalization on every K-injective complex and every resolution
of its restricted complex, including invertibility of the termwise F-image of that resolution.
Source: the normalization displayed in the node, Stacks Tag 070Y
(blueprint: lem-sf-normalized-derived-comparison-composition).
The identity-resolution comparison for G is its inverse derived unit, with the shared
Q/Qh identifications; the final target isomorphism implements Fr = sG. -/
def IsKInjectiveNormalizedDerivedComparison
    {A : Type u0} {A' : Type u1} {B : Type u2} {B' : Type uB0}
    [Category.{v0} A] [Category.{v1} A'] [Category.{v2} B] [Category.{vB0} B']
    [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
    [HasDerivedCategory.{w0} A] [HasDerivedCategory.{w1} A']
    [HasDerivedCategory.{w2} B] [HasDerivedCategory.{wB0} B']
    (F : A ⥤ B) (G : A' ⥤ B') [F.Additive] [G.Additive]
    (r : A' ⥤ A) (s : B' ⥤ B) [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (e : r ⋙ F = G ⋙ s)
    (enoughA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enoughA' : ∀ K : CochainComplex A' ℤ,
      ∃ (I : CochainComplex A' ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (β : r.mapDerivedCategory ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions enoughA ≅
      G.rightDerivedFunctorOfQuasiIsoResolutions enoughA' ⋙ s.mapDerivedCategory) : Prop :=
  ∀ (H : CochainComplex A' ℤ) [H.IsKInjective]
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (a : (r.mapHomologicalComplex (.up ℤ)).obj H ⟶ I) [QuasiIso a],
    ∃ hFa : IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a)),
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA a).inv ≫
        (normalizedDerivedComparisonComplexIso F G r s enoughA enoughA' β H).hom ≫
        s.mapDerivedCategory.map
          (G.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enoughA' (𝟙 H)).hom ≫
        (normalizedDerivedComparisonTargetIso F G r s e H).inv =
      @CategoryTheory.inv _ _ _ _ _ hFa

/-- Normalized comparisons compose, using the canonical localization identifications.
Source: Stacks Tag 070Y and the node's explicit composition argument
(blueprint: lem-sf-normalized-derived-comparison-composition).

Proof: (1) For a K-injective H in A2 choose u : r12(H) -> J and v : r01(J) -> I
K-injective resolutions, using enough1 and enough0. Exactness of r01 makes
w = r01(u) followed by v a quasi-isomorphism with K-injective target I
(lem-weil-pbc-exact-functor-derived-factorization). The c maps are isomorphisms by
lem-sf-kinjective-derived-map-computation and the derived units are invertible on I,J,H
by def-sfb-right-derived-functor.
(2) Apply lem-sf-normalized-derived-comparison-common-resolution to beta01 at r12(H),
using u and v: with A = s01(c_u), B = c_w and X = P0(F0(v)), obtain
B inverse followed by beta01 followed by A = X inverse.
(3) The normalizations of beta12 at (H,u) and beta02 at (H,w), after applying s01
where necessary, give the analogous equations with T = s02(eta_H) and
Y = P0(F0(r01(u))). The stipulated strict equalities and canonical localization maps
identify the endpoints.
(4) Insert A inverse followed by A between beta01 and s01(beta12). The two
normalizations give Y inverse X inverse. Functoriality gives P0(F0(w)) = XY,
so the beta02 equation has the same right side. Cancel B inverse and T inverse.
(5) For arbitrary L in D(A2), represent L by N and choose a resolution N -> H.
Its localized map is an isomorphism q : L -> Q2(H). Expand naturality of both beta02
and the two-factor composite at q; r02 = r12 r01 and s02 = s12 s01 identify their
source and target functors (def-weil-abstract-derived-category).
(6) The equality at H and cancellation of the image of q give the equality at L.
Every resolution is chosen in its own category; preservation of K-injectives is unused. -/
theorem normalizedDerivedComparison_composition
    {A0 : Type uA0} {A1 : Type uA1} {A2 : Type uA2}
    {B0 : Type uB0} {B1 : Type uB1} {B2 : Type uB2}
    [Category.{vA0} A0] [Category.{vA1} A1] [Category.{vA2} A2]
    [Category.{vB0} B0] [Category.{vB1} B1] [Category.{vB2} B2]
    [Abelian A0] [Abelian A1] [Abelian A2] [Abelian B0] [Abelian B1] [Abelian B2]
    [HasDerivedCategory.{wA0} A0] [HasDerivedCategory.{wA1} A1]
    [HasDerivedCategory.{wA2} A2] [HasDerivedCategory.{wB0} B0]
    [HasDerivedCategory.{wB1} B1] [HasDerivedCategory.{wB2} B2]
    (F0 : A0 ⥤ B0) (F1 : A1 ⥤ B1) (F2 : A2 ⥤ B2)
    [F0.Additive] [F1.Additive] [F2.Additive]
    (enough0 : ∀ K : CochainComplex A0 ℤ,
      ∃ (I : CochainComplex A0 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough1 : ∀ K : CochainComplex A1 ℤ,
      ∃ (I : CochainComplex A1 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (enough2 : ∀ K : CochainComplex A2 ℤ,
      ∃ (I : CochainComplex A2 ℤ) (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a)
    (r01 : A1 ⥤ A0) (r12 : A2 ⥤ A1) (r02 : A2 ⥤ A0)
    (s01 : B1 ⥤ B0) (s12 : B2 ⥤ B1) (s02 : B2 ⥤ B0)
    [r01.Additive] [r12.Additive] [r02.Additive]
    [s01.Additive] [s12.Additive] [s02.Additive]
    [PreservesFiniteLimits r01] [PreservesFiniteColimits r01]
    [PreservesFiniteLimits r12] [PreservesFiniteColimits r12]
    [PreservesFiniteLimits r02] [PreservesFiniteColimits r02]
    [PreservesFiniteLimits s01] [PreservesFiniteColimits s01]
    [PreservesFiniteLimits s12] [PreservesFiniteColimits s12]
    [PreservesFiniteLimits s02] [PreservesFiniteColimits s02]
    (er : r02 = r12 ⋙ r01) (es : s02 = s12 ⋙ s01)
    (e01 : r01 ⋙ F0 = F1 ⋙ s01) (e12 : r12 ⋙ F1 = F2 ⋙ s12)
    (e02 : r02 ⋙ F0 = F2 ⋙ s02)
    (β01 : r01.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ⋙ s01.mapDerivedCategory)
    (β12 : r12.mapDerivedCategory ⋙ F1.rightDerivedFunctorOfQuasiIsoResolutions enough1 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s12.mapDerivedCategory)
    (β02 : r02.mapDerivedCategory ⋙ F0.rightDerivedFunctorOfQuasiIsoResolutions enough0 ≅
      F2.rightDerivedFunctorOfQuasiIsoResolutions enough2 ⋙ s02.mapDerivedCategory)
    (h01 : IsKInjectiveNormalizedDerivedComparison F0 F1 r01 s01 e01 enough0 enough1 β01)
    (h12 : IsKInjectiveNormalizedDerivedComparison F1 F2 r12 s12 e12 enough1 enough2 β12)
    (h02 : IsKInjectiveNormalizedDerivedComparison F0 F2 r02 s02 e02 enough0 enough2 β02)
    (L : DerivedCategory A2) :
    β02.hom.app L =
      (F0.rightDerivedFunctorOfQuasiIsoResolutions enough0).map
        ((normalizedDerivedComparisonCompositionLocalizationIso r02 r12 r01 er).hom.app L) ≫
      β01.hom.app (r12.mapDerivedCategory.obj L) ≫
      s01.mapDerivedCategory.map (β12.hom.app L) ≫
      (normalizedDerivedComparisonCompositionLocalizationIso s02 s12 s01 es).inv.app
        ((F2.rightDerivedFunctorOfQuasiIsoResolutions enough2).obj L) := by
  sorry

end CategoryTheory.Functor
