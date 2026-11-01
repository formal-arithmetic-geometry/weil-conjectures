/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperBoundedBelowCoproducts
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import WeilConjectures.Compactification.Defs

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

/-- Proper direct image commutes with sums of ind-constructible complexes in a common
integer interval for a finite subextension of the fixed algebraic closure.
Source: blueprint latest, part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-proper-direct-image-of-unbounded-complexes/sk-lem-proper-unbounded-window/
`sk-lem-proper-unbounded-window-ii-bounded.md` (statement) and `.proof.md` (proof)
(blueprint: det-proper-unbounded-window-ii-bounded).

Proof for stage 3 (the node's proof steps):
1. Comparison. For T = X, Y abelian sheaves have a closed additive tensor and are
   Grothendieck (lem-weil-pbc-sheaf-tensor-closed), so internal Lambda_T-modules are
   Grothendieck (lem-sfb-modobj-grothendieck), with enough injectives
   (lem-sp-grothendieck-enough-injectives) and K-injective resolutions
   (lem-sfb-grothendieck-k-injective). Derived coproducts are termwise
   (lem-kun-grothendieck-derived-coproducts). The left exact module pushforward
   (sk-def-sfb-module-pushforward-pullback) has a triangulated, shift-compatible total
   derivation F = Rp_* (lem-pc-right-derived-functor-triangulated). The comparison
   eta_M is `hd.desc` of the cofan with legs F(iota_i); it is natural in componentwise maps.
2. Prerequisites. Properness makes p of finite type and Y is quasi-compact
   (def-weil-proper-morphism, sk-def-sfb-dc-setting). The fibre bound
   (lem-fin-finite-type-fibre-dimension-bound) and its invariance under field extension
   (lem-sf-field-extension-dimension-upper-bound) give the geometric fibre bound needed by
   sk-lem-proper-heart-bound. Cohomology commutes with ambient sums and truncations keep
   D_ic (det-ambient-ind-derived-sums). If b < a every input, its sum and its images are
   zero (lem-weil-pbc-unbounded-derived-iso-cohomology), so eta_M is invertible.
3. Case a = b (induction on b - a for every a). Put B_i = H^a(M_i); then M_i = B_i[-a]
   (lem-sf-derived-concentrated-single) and the sum is (sum B_i)[-a]
   (det-ambient-ind-derived-sums). By src-right-derived-functor-plus-compatibility and
   lem-sp-shift-identification, H^n(eta_M) is sum R^(n-a)p_* B_i -> R^(n-a)p_*(sum B_i)
   (the source's printed n+a is corrected to n-a). For n - a >= 0 it is invertible by
   sk-lem-proper-heart-bound; for n - a < 0 both sides vanish. Cohomology detects
   isomorphisms (lem-weil-pbc-unbounded-derived-iso-cohomology).
4. Case a < b. Use the truncation triangle A_i -> M_i -> C_i -> A_i[1] with
   A_i = tau_le(b-1) M_i and C_i = H^b(M_i)[-b] (lem-weil-pbc-truncation-triangle), where
   tau_le(b) M_i -> M_i is invertible. A and C stay in D_ic, with intervals [a, b-1] and
   [b, b] (det-ambient-ind-derived-sums). Induction gives eta_A, step 3 gives eta_C.
5. Sum the triangles and apply F (lower row); sum their F-images (upper row). Both are
   distinguished (lem-sfb-coproduct-distinguished-triangles,
   lem-pc-right-derived-functor-triangulated). The comparisons form a triangle morphism:
   the first two squares by functoriality on coprojections, the boundary square by the
   shifted coprojections and naturality of the shift comparison of F, with fourth
   component eta_A[1]. As eta_A and eta_C are isomorphisms, so is eta_M
   (lem-sf-triangle-morphism-iso); this holds for the empty family too.
-/
theorem properUnboundedWindowBounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (a b : ℤ) (I : Type (u + 1))
    (M : I → DerivedCategory (pulledBackModuleObjects
      (Profinite.continuousMapRingObj E) X))
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

/-- Proper direct image commutes with sums of ind-constructible complexes in a common
integer interval for the condensed algebraic closure.
Source: blueprint latest, part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-proper-direct-image-of-unbounded-complexes/sk-lem-proper-unbounded-window/
`sk-lem-proper-unbounded-window-ii-bounded.md` (statement) and `.proof.md` (proof)
(blueprint: det-proper-unbounded-window-ii-bounded).

Proof for stage 3 (the node's proof steps):
1. Comparison. For T = X, Y abelian sheaves have a closed additive tensor and are
   Grothendieck (lem-weil-pbc-sheaf-tensor-closed), so internal Lambda_T-modules are
   Grothendieck (lem-sfb-modobj-grothendieck), with enough injectives
   (lem-sp-grothendieck-enough-injectives) and K-injective resolutions
   (lem-sfb-grothendieck-k-injective). Derived coproducts are termwise
   (lem-kun-grothendieck-derived-coproducts). The left exact module pushforward
   (sk-def-sfb-module-pushforward-pullback) has a triangulated, shift-compatible total
   derivation F = Rp_* (lem-pc-right-derived-functor-triangulated). The comparison
   eta_M is `hd.desc` of the cofan with legs F(iota_i); it is natural in componentwise maps.
2. Prerequisites. Properness makes p of finite type and Y is quasi-compact
   (def-weil-proper-morphism, sk-def-sfb-dc-setting). The fibre bound
   (lem-fin-finite-type-fibre-dimension-bound) and its invariance under field extension
   (lem-sf-field-extension-dimension-upper-bound) give the geometric fibre bound needed by
   sk-lem-proper-heart-bound. Cohomology commutes with ambient sums and truncations keep
   D_ic (det-ambient-ind-derived-sums). If b < a every input, its sum and its images are
   zero (lem-weil-pbc-unbounded-derived-iso-cohomology), so eta_M is invertible.
3. Case a = b (induction on b - a for every a). Put B_i = H^a(M_i); then M_i = B_i[-a]
   (lem-sf-derived-concentrated-single) and the sum is (sum B_i)[-a]
   (det-ambient-ind-derived-sums). By src-right-derived-functor-plus-compatibility and
   lem-sp-shift-identification, H^n(eta_M) is sum R^(n-a)p_* B_i -> R^(n-a)p_*(sum B_i)
   (the source's printed n+a is corrected to n-a). For n - a >= 0 it is invertible by
   sk-lem-proper-heart-bound; for n - a < 0 both sides vanish. Cohomology detects
   isomorphisms (lem-weil-pbc-unbounded-derived-iso-cohomology).
4. Case a < b. Use the truncation triangle A_i -> M_i -> C_i -> A_i[1] with
   A_i = tau_le(b-1) M_i and C_i = H^b(M_i)[-b] (lem-weil-pbc-truncation-triangle), where
   tau_le(b) M_i -> M_i is invertible. A and C stay in D_ic, with intervals [a, b-1] and
   [b, b] (det-ambient-ind-derived-sums). Induction gives eta_A, step 3 gives eta_C.
5. Sum the triangles and apply F (lower row); sum their F-images (upper row). Both are
   distinguished (lem-sfb-coproduct-distinguished-triangles,
   lem-pc-right-derived-functor-triangulated). The comparisons form a triangle morphism:
   the first two squares by functoriality on coprojections, the boundary square by the
   shifted coprojections and naturality of the shift comparison of F, with fourth
   component eta_A[1]. As eta_A and eta_C are isomorphisms, so is eta_M
   (lem-sf-triangle-morphism-iso); this holds for the empty family too.
-/
theorem properUnboundedWindowBounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (a b : ℤ) (I : Type (u + 1))
    (M : I → DerivedCategory (pulledBackModuleObjects
      (Profinite.padicAlgClRingObj ℓ) X))
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
        ((CondensedRing.lowerStar
          (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar
          (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.map
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
