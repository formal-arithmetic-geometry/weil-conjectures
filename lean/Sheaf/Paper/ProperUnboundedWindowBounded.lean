/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Paper.ModuleObjects
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts

/-!
# Proper pushforward and uniformly bounded coproducts

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-proper-unbounded-window-ii/sk-lem-proper-unbounded-window-ii-bounded.md
(blueprint: det-proper-unbounded-window-ii-bounded).

Both coproducts are ambient unbounded derived coproducts. They are exhibited by colimit
cofans, so their existence is part of the conclusion, rather than an extra hypothesis.
The displayed `desc` is the canonical comparison: its composite with the i-th injection
is the derived pushforward of the i-th source injection. By uniqueness of colimits the
assertion is independent of the exhibited cofans.

Ind-constructibility is `ObjectProperty.ind.{u + 1}` of the recorded finite constant-model
predicate, computed in the module-object category, imposed on every cohomology object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper derived module pushforward commutes with sums of ind-constructible complexes
in a common integer interval, for the finite subextension E of the fixed algebraic closure.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window-ii-bounded, statement
(blueprint: det-proper-unbounded-window-ii-bounded).

Proof for stage 3:
1. The module categories are Grothendieck abelian and have K-injective resolutions
   (prop-pur-kinjective-resolutions-exist) and enough injectives
   (lem-sp-grothendieck-enough-injectives). The additive left exact module pushforward
   is the recorded full composite (sk-def-sfb-module-pushforward-pullback), and its
   total right derivation is additive, triangulated and shift-compatible
   (lem-pc-right-derived-functor-triangulated). Coproduct universality defines the
   comparison and makes it natural in componentwise maps.
2. Ambient derived sums are termwise (lem-kun-grothendieck-derived-coproducts).
   The cone formula (def-weil-abstract-derived-category) identifies the sum of the
   cones of chain maps with the cone of their sum, including its boundary and shift.
   Thus sums of distinguished triangles are distinguished. Cohomology commutes with
   these sums and truncations retain ind-constructibility (det-ambient-ind-derived-sums).
3. Properness gives quasi-compactness and quasi-separatedness
   (def-weil-proper-morphism, def-weil-finite-type-morphism,
   lem-pc-separated-quasi-separated). Higher direct images commute with sums on the
   heart by det-proper-heart-continuity-direct-image. No global fibre dimension bound
   is needed here. Its ring-sheaf formulation is applied to the actual pulled-back
   condensed coefficients, with the equivalent internal-module encoding and the
   restriction of scalars in the full module pushforward.
4. If b<a, every cohomology object of every input vanishes, so all inputs and their
   images are zero (lem-weil-pbc-unbounded-derived-iso-cohomology). This includes the
   empty family. If a=b, identify M_i with H^a(M_i)[-a]
   (lem-sf-derived-concentrated-single). By lem-sp-derived-functor-single-identification
   and src-right-derived-functor-plus-compatibility, H^n of the comparison is the
   sum comparison for R^(n-a)p_* on these sheaves. For n-a>=0 use step 3; for n-a<0
   both sides vanish by an injective resolution starting in degree zero. Naturality
   and the coprojection equation identify this map with the canonical comparison.
   Cohomology detects isomorphisms (lem-weil-pbc-unbounded-derived-iso-cohomology).
5. For a<b, use the truncation triangle tau_le_(b-1) M_i -> M_i -> H^b(M_i)[-b]
   (def-kun-truncations, lem-weil-pbc-truncation-triangle), identifying tau_le_b M_i
   with M_i by cohomology. Its outer terms are ind-constructible, in intervals
   [a,b-1] and [b,b] (det-ambient-ind-derived-sums). Induction on b-a gives the
   comparison isomorphism for the first terms; step 4 gives it for the third terms.
6. Sum the pushed-forward triangles for the upper row and push forward the summed
   source triangles for the lower row. Both are distinguished by steps 1 and 2.
   The comparison maps form a morphism of triangles: check the first two squares
   on every coprojection using functoriality. For the boundary square do the same
   with the shifted coprojections and naturality of the functor's shift isomorphism;
   this gives exactly the shifted first component. The first and third comparisons
   are isomorphisms, so the middle one is too (lem-sf-triangle-morphism-iso).
-/
theorem properUnboundedWindowBounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (a b : ℤ) (I : Type (u + 1))
    (M : I → DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hM : ∀ (i : I) (r : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ r).obj (M i)))
    (hbound : ∀ (i : I) (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (M i))) :
    ∃ (c : Cofan M) (_ : IsColimit c)
      (d : Cofan (fun i ↦
        (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
          (M i))) (hd : IsColimit d),
      IsIso (hd.desc (Cofan.mk
        ((CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar
          (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.map
          (c.inj i)))) := by
  classical
  -- The existing qcqs theorem only needs the common lower cohomology bound.
  have _ := hM
  let C := pulledBackModuleObjects (Profinite.continuousMapRingObj E) X
  let F := (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have hN (i : I) : (M i).IsGE a :=
    (DerivedCategory.isGE_iff (M i) a).2 (fun r hr ↦ hbound i r (Or.inl hr))
  have : PreservesColimit (Discrete.functor M) F :=
    CondensedRing.condensed_boundedBelow_preservesCoproduct
      (Profinite.continuousMapRingObj E) p I a M hN
  let c : Cofan M := Cofan.mk (∐ M) (Sigma.ι M)
  let d : Cofan (fun i ↦ F.obj (M i)) :=
    Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i))
  have hd : IsColimit d :=
    (isColimitMapCoconeCofanMkEquiv F M c.inj).1
      (isColimitOfPreserves F (coproductIsCoproduct M))
  refine ⟨c, coproductIsCoproduct M, d, hd, ?_⟩
  change IsIso (hd.desc d)
  have hid : hd.desc d = 𝟙 d.pt := hd.hom_ext (by simp)
  rw [hid]
  infer_instance

/-- Proper derived module pushforward commutes with sums of ind-constructible complexes
in a common integer interval, for the finite-subextension-valued condensed algebraic closure.
Source: blueprint main-20261015, sk-lem-proper-unbounded-window-ii-bounded, statement
(blueprint: det-proper-unbounded-window-ii-bounded).

Proof for stage 3:
1. The module categories are Grothendieck abelian and have K-injective resolutions
   (prop-pur-kinjective-resolutions-exist) and enough injectives
   (lem-sp-grothendieck-enough-injectives). The additive left exact module pushforward
   is the recorded full composite (sk-def-sfb-module-pushforward-pullback), and its
   total right derivation is additive, triangulated and shift-compatible
   (lem-pc-right-derived-functor-triangulated). Coproduct universality defines the
   comparison and makes it natural in componentwise maps.
2. Ambient derived sums are termwise (lem-kun-grothendieck-derived-coproducts).
   The cone formula (def-weil-abstract-derived-category) identifies the sum of the
   cones of chain maps with the cone of their sum, including its boundary and shift.
   Thus sums of distinguished triangles are distinguished. Cohomology commutes with
   these sums and truncations retain ind-constructibility (det-ambient-ind-derived-sums).
3. Properness gives quasi-compactness and quasi-separatedness
   (def-weil-proper-morphism, def-weil-finite-type-morphism,
   lem-pc-separated-quasi-separated). Higher direct images commute with sums on the
   heart by det-proper-heart-continuity-direct-image. No global fibre dimension bound
   is needed here. Its ring-sheaf formulation is applied to the actual pulled-back
   condensed coefficients, with the equivalent internal-module encoding and the
   restriction of scalars in the full module pushforward.
4. If b<a, every cohomology object of every input vanishes, so all inputs and their
   images are zero (lem-weil-pbc-unbounded-derived-iso-cohomology). This includes the
   empty family. If a=b, identify M_i with H^a(M_i)[-a]
   (lem-sf-derived-concentrated-single). By lem-sp-derived-functor-single-identification
   and src-right-derived-functor-plus-compatibility, H^n of the comparison is the
   sum comparison for R^(n-a)p_* on these sheaves. For n-a>=0 use step 3; for n-a<0
   both sides vanish by an injective resolution starting in degree zero. Naturality
   and the coprojection equation identify this map with the canonical comparison.
   Cohomology detects isomorphisms (lem-weil-pbc-unbounded-derived-iso-cohomology).
5. For a<b, use the truncation triangle tau_le_(b-1) M_i -> M_i -> H^b(M_i)[-b]
   (def-kun-truncations, lem-weil-pbc-truncation-triangle), identifying tau_le_b M_i
   with M_i by cohomology. Its outer terms are ind-constructible, in intervals
   [a,b-1] and [b,b] (det-ambient-ind-derived-sums). Induction on b-a gives the
   comparison isomorphism for the first terms; step 4 gives it for the third terms.
6. Sum the pushed-forward triangles for the upper row and push forward the summed
   source triangles for the lower row. Both are distinguished by steps 1 and 2.
   The comparison maps form a morphism of triangles: check the first two squares
   on every coprojection using functoriality. For the boundary square do the same
   with the shifted coprojections and naturality of the functor's shift isomorphism;
   this gives exactly the shifted first component. The first and third comparisons
   are isomorphisms, so the middle one is too (lem-sf-triangle-morphism-iso).
-/
theorem properUnboundedWindowBounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (a b : ℤ) (I : Type (u + 1))
    (M : I → DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hM : ∀ (i : I) (r : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ r).obj (M i)))
    (hbound : ∀ (i : I) (r : ℤ), r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj (M i))) :
    ∃ (c : Cofan M) (_ : IsColimit c)
      (d : Cofan (fun i ↦
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          (M i))) (hd : IsColimit d),
      IsIso (hd.desc (Cofan.mk
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
          (c.inj i)))) := by
  classical
  -- The existing qcqs theorem only needs the common lower cohomology bound.
  have _ := hM
  let C := pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X
  let F := (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor
  have : HasColimitsOfSize.{u + 1, u + 1} C :=
    IsGrothendieckAbelian.hasColimits C
  have : HasCoproducts.{u + 1} C := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{u + 1} (DerivedCategory C) := derived_hasCoproducts
  have hN (i : I) : (M i).IsGE a :=
    (DerivedCategory.isGE_iff (M i) a).2 (fun r hr ↦ hbound i r (Or.inl hr))
  have : PreservesColimit (Discrete.functor M) F :=
    CondensedRing.condensed_boundedBelow_preservesCoproduct
      (Profinite.padicAlgClRingObj ℓ) p I a M hN
  let c : Cofan M := Cofan.mk (∐ M) (Sigma.ι M)
  let d : Cofan (fun i ↦ F.obj (M i)) :=
    Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i))
  have hd : IsColimit d :=
    (isColimitMapCoconeCofanMkEquiv F M c.inj).1
      (isColimitOfPreserves F (coproductIsCoproduct M))
  refine ⟨c, coproductIsCoproduct M, d, hd, ?_⟩
  change IsIso (hd.desc d)
  have hid : hd.desc d = 𝟙 d.pt := hd.hom_ext (by simp)
  rw [hid]
  infer_instance

end AlgebraicGeometry.ProEtale
