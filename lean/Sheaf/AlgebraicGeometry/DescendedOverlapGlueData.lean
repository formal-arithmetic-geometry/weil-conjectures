/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!
# Descended overlap transitions before gluing

Source: Stacks Project, Descent, Tag 0AP4, construction of U_ij and transition maps.
(blueprint: lem-pd-descended-overlap-glue-data).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- The effective local models have open overlap transitions and lifts of the intersections.

Source: Stacks Project, Descent, Tag 0AP4, proof through the construction of gluing data;
Tags 03N0 and 02W0 for descent of opens and morphisms, respectively.
(blueprint: lem-pd-descended-overlap-glue-data).

Proof:
1. Inside U_i, take the inverse image of U_k under its inclusion in V. Given two
   transports over the same map to Y, membership in this intersection is preserved:
   compatibility with D makes the two inclusions agree after transport, and inverse
   transport gives the reverse implication. The pullback square for q_i identifies
   U_i with W_i times_Y X. Transport invariance of q_i and the pullback universal
   property identify E_i with the canonical descent datum. Base change of the fpqc
   singleton p makes q_i an fpqc singleton. Tag 03N0 descends the invariant intersection
   to a unique open O_ik of W_i. Set Z(i,k) to its open subscheme and f i k to its
   inclusion. The diagonal intersection is all U_i, so uniqueness gives O_ii = W_i
   and f i i is an isomorphism.
2. The common intersection U_i times_V U_k identifies the pullbacks of Z(i,k) and
   Z(k,i) along p. Its identity commutes with the canonical descent data just identified.
   Tag 02W0 descends this identity to t i k over Y, and descends its inverse to t k i.
   Injectivity proves the inverse identities and t i i = identity. The restriction of
   q_i to the intersection factors through the descended open, giving r i k. The
   factorization equations are r i k followed by f i k = first projection followed by
   q_i, and r i k followed by t i k and f k i = second projection followed by q_k.
   Descent of the open identifies its pullback along q_i with this intersection,
   giving the asserted cartesian square for r i k.
3. On triple intersections, uniqueness in Tag 03N0 identifies the overlap domains.
   Restrict the transitions there and use the pullback universal property to obtain
   t' i k l. Its second projection is the first projection followed by t i k.
   After fpqc base change the three cyclic restrictions are identities on the same
   triple intersection; injectivity in Tag 02W0 gives the cyclic cocycle equation.
   The f i k are open immersions by construction. No covering assumption on U is used,
   and no ambient glued scheme or map from it to Y is asserted. Empty I gives empty
   families with all assertions vacuous; empty individual opens descend to empty opens.
-/
theorem exists_descended_overlap_glue_data
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (Z : I × I → Scheme.{u}) (f : ∀ i k, Z (i, k) ⟶ (W i).left)
      (t : ∀ i k, Z (i, k) ⟶ Z (k, i)),
      (∀ i k, IsOpenImmersion (f i k)) ∧
      (∀ i, IsIso (f i i)) ∧
      (∀ i, t i i = 𝟙 _) ∧
      (∃ (t' : ∀ i k l, Limits.pullback (f i k) (f i l) ⟶ Limits.pullback (f k l) (f k i)),
        (∀ i k l, t' i k l ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i k) ∧
        (∀ i k l, t' i k l ≫ t' k l i ≫ t' l i k = 𝟙 _)) ∧
      (∀ i k, ∃ (r : Limits.pullback (U i).ι (U k).ι ⟶ Z (i, k)),
        IsPullback r (pullback.fst (U i).ι (U k).ι) (f i k) (q i) ∧
        r ≫ t i k ≫ f k i = pullback.snd (U i).ι (U k).ι ≫ q k) := by sorry

end CategoryTheory.Over.DescentDatum
