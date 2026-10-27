/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Clopen realization of a restricted relation after base change

Source: Stacks Project, Groupoids, Tag 02VD; More on Groupoids, Tag 03X5, conclusion (h)
(blueprint: lem-a1-clopen-relation-base-change-identification).

All existentially named structural maps are specified by their projections. In particular,
these are the induced maps, and the isomorphisms preserve all three structural maps.
The coproduct assertion uses the two actual open-subscheme inclusions as its cocone.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A clopen restriction of an arbitrary base change of a scheme equivalence relation
is the induced clopen open subscheme, the iterated endpoint pullback, and the pullback
of the original relation along the object square. It represents the restricted
pointwise equivalence relation.

Source: Stacks Project, Groupoids, Tag 02VD (the displayed Cartesian identification),
with the clopen realization used in More on Groupoids, Tag 03X5, conclusion (h)
(blueprint: lem-a1-clopen-relation-base-change-identification).

Proof:
1. Write Y = R ×_T B and X = U ×_T B. The inverse images of V under the two
   induced endpoint maps are clopen, since scheme maps are continuous. Their
   intersection C and its complement D are clopen, with the induced open structures
   (def-weil-open-immersion).
2. Form the coproduct of C and D (lem-weil-pbc-scheme-coproduct-family). Glue the
   two coprojections over the disjoint open cover of Y to obtain the inverse of the
   map from the coproduct to Y (lem-weil-pbc-scheme-morphism-gluing). The two
   composites are identities by gluing uniqueness and the coproduct property.
3. Each endpoint of C factors uniquely through V. More generally a map to Y factors
   uniquely through C precisely when both endpoints factor through V, by
   lem-weil-pbc-morphism-factors-through-open-subscheme. All factors are over B.
4. The three maps from C give its map to the iterated endpoint pullback. The middle
   projection of that pullback factors uniquely through C by step 3. These maps
   are inverse: check their three projections and cancel the open immersion of V
   (lem-weil-pbc-open-immersion-monomorphism, def-pc-fibre-product).
5. A point of (V ×_B V) ×_(U ×_T U) R consists of two V-coordinates and an R-coordinate
   with the prescribed endpoints. Its R-coordinate and the common B-coordinate
   give a map to Y. This yields the inverse maps between the two displayed pullbacks.
   Both composites fix every projection, so are identities by def-pc-fibre-product.
6. For H over B, the pullback property identifies X(H) with U(H) over the composite
   H → B → T. The open immersion V → X is injective on H-points. Step 3 identifies
   C(H) with exactly the R(H)-points whose endpoints lie in that image. Restrict the
   original reflexive, symmetric and transitive relation to this subset. Joint
   injectivity follows from the original relation and unique open factorization.
-/
theorem clopen_relation_base_change_identification
    {T U R B : Scheme.{u}} (fU : U ⟶ T) (fR : R ⟶ T)
    (s t : R ⟶ U) (hs : s ≫ fU = fR) (ht : t ≫ fU = fR)
    (hrel : ∀ (H : Scheme.{u}) (hH : H ⟶ T),
      Function.Injective
        (fun r : {g : H ⟶ R // g ≫ fR = hH} ↦ (r.1 ≫ s, r.1 ≫ t)) ∧
      Equivalence (fun a b : {g : H ⟶ U // g ≫ fU = hH} ↦
        ∃ r : H ⟶ R, r ≫ s = a.1 ∧ r ≫ t = b.1))
    (fB : B ⟶ T) (V : (pullback fU fB).Opens) (hV : IsClopen V.carrier) :
    ∃ (sB tB : pullback fR fB ⟶ pullback fU fB),
      sB ≫ pullback.fst fU fB = pullback.fst fR fB ≫ s ∧
      sB ≫ pullback.snd fU fB = pullback.snd fR fB ∧
      tB ≫ pullback.fst fU fB = pullback.fst fR fB ≫ t ∧
      tB ≫ pullback.snd fU fB = pullback.snd fR fB ∧
      ∃ (C D : (pullback fR fB).Opens),
        C = (sB ⁻¹ᵁ V) ⊓ (tB ⁻¹ᵁ V) ∧
        IsClopen C.carrier ∧ IsCompl C D ∧
        Nonempty (IsColimit (BinaryCofan.mk C.ι D.ι)) ∧
        ∃ (sC tC : C.toScheme ⟶ V.toScheme),
          sC ≫ V.ι = C.ι ≫ sB ∧ tC ≫ V.ι = C.ι ≫ tB ∧
          ∃ (e : C.toScheme ≅ pullback (pullback.snd V.ι sB ≫ tB) V.ι),
            e.hom ≫ pullback.fst (pullback.snd V.ι sB ≫ tB) V.ι ≫
              pullback.snd V.ι sB = C.ι ∧
            e.hom ≫ pullback.fst (pullback.snd V.ι sB ≫ tB) V.ι ≫
              pullback.fst V.ι sB = sC ∧
            e.hom ≫ pullback.snd (pullback.snd V.ι sB ≫ tB) V.ι = tC ∧
            ∃ (j : R ⟶ pullback fU fU),
              j ≫ pullback.fst fU fU = s ∧ j ≫ pullback.snd fU fU = t ∧
              ∃ (m : pullback (V.ι ≫ pullback.snd fU fB)
                  (V.ι ≫ pullback.snd fU fB) ⟶ pullback fU fU),
                m ≫ pullback.fst fU fU =
                  pullback.fst (V.ι ≫ pullback.snd fU fB)
                    (V.ι ≫ pullback.snd fU fB) ≫ V.ι ≫ pullback.fst fU fB ∧
                m ≫ pullback.snd fU fU =
                  pullback.snd (V.ι ≫ pullback.snd fU fB)
                    (V.ι ≫ pullback.snd fU fB) ≫ V.ι ≫ pullback.fst fU fB ∧
                ∃ (k : pullback m j ⟶ pullback fR fB),
                  k ≫ pullback.fst fR fB = pullback.snd m j ∧
                  k ≫ pullback.snd fR fB =
                    pullback.fst m j ≫
                      pullback.fst (V.ι ≫ pullback.snd fU fB)
                        (V.ι ≫ pullback.snd fU fB) ≫ V.ι ≫ pullback.snd fU fB ∧
                  ∃ (e' : pullback (pullback.snd V.ι sB ≫ tB) V.ι ≅ pullback m j),
                    e'.hom ≫ k =
                      pullback.fst (pullback.snd V.ι sB ≫ tB) V.ι ≫
                        pullback.snd V.ι sB ∧
                    e'.hom ≫ pullback.fst m j ≫
                        pullback.fst (V.ι ≫ pullback.snd fU fB)
                          (V.ι ≫ pullback.snd fU fB) =
                      pullback.fst (pullback.snd V.ι sB ≫ tB) V.ι ≫
                        pullback.fst V.ι sB ∧
                    e'.hom ≫ pullback.fst m j ≫
                        pullback.snd (V.ι ≫ pullback.snd fU fB)
                          (V.ι ≫ pullback.snd fU fB) =
                      pullback.snd (pullback.snd V.ι sB ≫ tB) V.ι ∧
                    ∀ (H : Scheme.{u}) (hH : H ⟶ B),
                      (∀ a : H ⟶ U, a ≫ fU = hH ≫ fB →
                        ∃! aB : H ⟶ pullback fU fB,
                          aB ≫ pullback.fst fU fB = a ∧
                          aB ≫ pullback.snd fU fB = hH) ∧
                      Function.Injective (fun a :
                        {g : H ⟶ V.toScheme // g ≫ V.ι ≫ pullback.snd fU fB = hH} ↦
                          a.1 ≫ V.ι) ∧
                      (∀ r : H ⟶ R, r ≫ fR = hH ≫ fB →
                        ((∃! c : H ⟶ C.toScheme,
                            c ≫ C.ι ≫ pullback.fst fR fB = r ∧
                            c ≫ C.ι ≫ pullback.snd fR fB = hH) ↔
                          (∃ a : H ⟶ V.toScheme,
                            a ≫ V.ι ≫ pullback.fst fU fB = r ≫ s ∧
                            a ≫ V.ι ≫ pullback.snd fU fB = hH) ∧
                          (∃ b : H ⟶ V.toScheme,
                            b ≫ V.ι ≫ pullback.fst fU fB = r ≫ t ∧
                            b ≫ V.ι ≫ pullback.snd fU fB = hH))) ∧
                      Function.Injective (fun c :
                        {g : H ⟶ C.toScheme // g ≫ C.ι ≫ pullback.snd fR fB = hH} ↦
                          (c.1 ≫ sC, c.1 ≫ tC)) ∧
                      Equivalence (fun a b :
                        {g : H ⟶ V.toScheme // g ≫ V.ι ≫ pullback.snd fU fB = hH} ↦
                          ∃ c : H ⟶ C.toScheme,
                            c ≫ sC = a.1 ∧ c ≫ tC = b.1) := by
  sorry

end AlgebraicGeometry
