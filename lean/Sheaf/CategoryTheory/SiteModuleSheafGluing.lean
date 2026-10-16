/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.SiteModuleSheafGluingAux

/-!
# Gluing module sheaves on an arbitrary covering of a site

Source: Stacks Project, Sites, Tag 04TR, Lemma `sites-lemma-glue-sheaves`, with
componentwise module operations (blueprint: lem-weil-pbc-site-module-sheaf-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uR w v

open CategoryTheory Opposite

namespace SheafOfModules

/-- Effective gluing of module sheaves along a covering of a ringed site.

Source: Stacks Project, Sites, Tag 04TR
(blueprint: lem-weil-pbc-site-module-sheaf-gluing).

`A` is a sheaf of rings with sectionwise commutativity `hcomm`, equivalently a
sheaf of commutative rings; ring homomorphisms need no extra compatibility with it.
The localizations are taken inside `Over U`; relocalization identifies
`Over (Uᵢ i)` with the original site's slice over the domain of `Uᵢ i`.
The overlap isomorphism is specified by its linear equivalences `φ i j W a b` on
sections, where `a : W ⟶ Uᵢ i` and `b : W ⟶ Uᵢ j`. Such pairs are exactly objects
of the slice over the fibre product. The condition `hnatural` is precisely naturality
of that isomorphism; its inverse is natural because the components are equivalences.
Likewise, testing `hcocycle` on all triples of arrows is exactly equality of the
restricted sheaf morphisms on the triple fibre product. Thus no choice of fibre
products or comparison isomorphisms enters the statement.

Proof:
1. For `V → U`, take tuples of sections of `Fᵢ i` on `Uᵢ i ×_U V` satisfying the
   overlap equations. Restrict the components to define restriction maps
   (def-weil-pbc-sites-and-cohomology, def-pur-localized-ringed-site).
2. Give these tuples componentwise addition, zero, negation and scalar multiplication.
   Linearity of `φ` preserves compatibility and proves the module restriction laws
   (def-weil-sheaf-of-modules-category).
3. Glue a matching family separately in every component. The resulting components
   satisfy the overlap equations by separatedness after pulling back the covering.
   Uniqueness is componentwise. Thus the module presheaf is a sheaf.
4. Over `Uᵢ k`, evaluate the k-th component along the graph of `W → Uᵢ k`.
   The inverse sends a section to the tuple obtained by the transition maps `φ k i`;
   the cocycle gives compatibility, naturality and linearity of these maps.
5. Pull the `(k,k,k)` cocycle back to the diagonal. Cancellation gives the identity
   there. This proves one inverse equation; the tuple equation pulled back along
   the graph proves the other, without requiring any covering arrow to be mono.
6. Pull the tuple equation back along the two arrows from a test object to an
   overlap. This is the asserted compatibility between `e` and `φ`.
-/
theorem exists_moduleSheaf_of_cover
    {C : Type uC} [Category.{vC} C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (U : C) (I : Type w) (Uᵢ : I → Over U)
    (hcover : Presieve.ofArrows (fun i ↦ (Uᵢ i).left) (fun i ↦ (Uᵢ i).hom) ∈ J U)
    (A : Sheaf (J.toGrothendieck.over U) RingCat.{uR})
    (hcomm : ∀ (W : (Over U)ᵒᵖ) (r s : A.obj.obj W), r * s = s * r)
    (Fᵢ : ∀ i : I, ringedSiteModules.{max uC vC w v, uR, vC, max uC vC}
      (A.over (Uᵢ i)))
    (φ : ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j),
      (Fᵢ i).val.obj (op (Over.mk (T := Over U) a)) ≃ₗ[A.obj.obj (op W)]
        (Fᵢ j).val.obj (op (Over.mk (T := Over U) b)))
    (hnatural : ∀ (i j : I) (W V : Over U) (k : V ⟶ W)
      (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i j V (k ≫ a) (k ≫ b) ((Fᵢ i).val.map
        (Over.homMk (U := Over.mk (T := Over U) (k ≫ a)) (V := Over.mk (T := Over U) a)
          k rfl).op x) =
        (Fᵢ j).val.map
          (Over.homMk (U := Over.mk (T := Over U) (k ≫ b)) (V := Over.mk (T := Over U) b) k rfl).op
            (φ i j W a b x))
    (hcocycle : ∀ (i j k : I) (W : Over U)
      (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j) (c : W ⟶ Uᵢ k)
      (x : (Fᵢ i).val.obj (op (Over.mk (T := Over U) a))),
      φ i k W a c x = φ j k W b c (φ i j W a b x)) :
    ∃ F : ringedSiteModules.{max uC vC w v, uR, vC, max uC vC} A,
      ∃ e : ∀ i : I, F.over (Uᵢ i) ≅ Fᵢ i,
        ∀ (i j : I) (W : Over U) (a : W ⟶ Uᵢ i) (b : W ⟶ Uᵢ j)
          (x : F.val.obj (op W)),
          φ i j W a b ((e i).hom.val.app (op (Over.mk (T := Over U) a)) x) =
            (e j).hom.val.app (op (Over.mk (T := Over U) b)) x  := by
  obtain ⟨F, e, e_inv, heinv, he, hcompat⟩ :=
    exists_moduleSheaf_of_cover_with_maps.{uC, vC, uR, w, v}
      J U I Uᵢ hcover A hcomm Fᵢ φ hnatural hcocycle
  let eIso : ∀ i : I, F.over (Uᵢ i) ≅ Fᵢ i := fun i =>
    { hom := e i, inv := e_inv i, hom_inv_id := he i, inv_hom_id := heinv i }
  refine ⟨F, eIso, ?_⟩
  exact hcompat

end SheafOfModules
