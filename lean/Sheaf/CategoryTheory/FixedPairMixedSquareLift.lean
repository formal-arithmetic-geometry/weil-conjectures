/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # Mixed comparison squares on fixed pairs

Source: blueprint main-20261015, `sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`,
final sentence on scalar and finite-to-common compatibility, expanded in the five proof steps
of the auxiliary node (blueprint: lem-fd-fixed-pair-mixed-square-lift).

The four transports are the existing `IsoAlgebra.mapOfNatIso` functors. Their commutation
isomorphisms are the inverses of the isomorphisms in the node, because functor composition
in Lean is written in diagrammatic order. Coherence equations are expressed as equality of
parallel natural transformations; this includes identities, composites, inverses and whiskerings.
-/

@[expose] public section

set_option autoImplicit false

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ uA vA uB vB

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- A compatible mixed comparison square lifts to the specified fixed-pair transports, with
its given forward and inverse components and its exact intertwining equation. Parallel
natural transformations into any fixed-pair category are equal whenever their underlying
components agree. This applies to every specified identity or cocycle equation between
composites and whiskerings of the lifted comparisons.

Source: blueprint main-20261015, `sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`,
final sentence on scalar and finite-to-common compatibility; the auxiliary node's proof steps
1--5 (blueprint: lem-fd-fixed-pair-mixed-square-lift).

Proof plan:
1. For a transport L with c : L U ≅ V L, the structure is c inverse followed by L(theta),
   with inverse L(theta inverse) followed by c. Naturality of c and the original intertwiner
   equation show that L on arrows is an intertwiner. Functoriality follows from that of L.
   These are precisely the four existing mapOfNatIso functors for b0, b1, rs and rp inverse,
   using def-weil-endofunctor-fixed-pair-category.
2. Cancel the mixed-square equation by the inverse components of b0, rp, rs and b1. The
   resulting equation starts at G1(J1(Ts K)) and ends at Tp(J0(F0 K)). Only isomorphisms of
   objects are inverted; no inverse functor is used (def-nagata-category).
3. Apply naturality of j to theta : F0 K --> K and substitute the equation from step 2.
   This gives exactly the displayed intertwining equation, so j_K is a pair morphism.
4. Cancel j_K and G1(j_K) to obtain the inverse intertwiner. Their composites are identities
   on underlying arrows. Naturality of j and its inverse gives the natural isomorphism of
   pair functors, since the forgetful functor is faithful.
5. Evaluate each specified parallel equation at a source object. Forgetting preserves
   identity, composition, inverse components and both whiskerings. The assumed equation
   on underlying arrows therefore implies equality of pair arrows by faithfulness, and
   componentwise equality implies equality of natural transformations. The same argument
   applies to coefficient-stage inclusions, since no functor is assumed an equivalence. -/
theorem fixedPair_mixedSquare_lift
    {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
    {D₀ : Type u₂} [Category.{v₂} D₀] {D₁ : Type u₃} [Category.{v₃} D₁]
    (F₀ : C₀ ⥤ C₀) (F₁ : C₁ ⥤ C₁) (G₀ : D₀ ⥤ D₀) (G₁ : D₁ ⥤ D₁)
    (J₀ : C₀ ⥤ D₀) (J₁ : C₁ ⥤ D₁) (Ts : C₀ ⥤ C₁) (Tp : D₀ ⥤ D₁)
    (b₀ : F₀ ⋙ J₀ ≅ J₀ ⋙ G₀) (b₁ : F₁ ⋙ J₁ ≅ J₁ ⋙ G₁)
    (rs : F₀ ⋙ Ts ≅ Ts ⋙ F₁) (rp : G₀ ⋙ Tp ≅ Tp ⋙ G₁)
    (j : Ts ⋙ J₁ ≅ J₀ ⋙ Tp)
    (mixed : ∀ K : C₀,
      j.hom.app (F₀.obj K) ≫ Tp.map (b₀.hom.app K) ≫ rp.hom.app (J₀.obj K) =
        J₁.map (rs.hom.app K) ≫ b₁.hom.app (Ts.obj K) ≫ G₁.map (j.hom.app K)) :
    (∃ jLift : mapOfNatIso rs.symm ⋙ mapOfNatIso b₁.symm ≅
        mapOfNatIso b₀.symm ⋙ mapOfNatIso rp.symm,
      (∀ K : IsoAlgebra F₀, (jLift.hom.app K).hom.f = j.hom.app K.carrier) ∧
      (∀ K : IsoAlgebra F₀, (jLift.inv.app K).hom.f = j.inv.app K.carrier) ∧
      (∀ K : IsoAlgebra F₀,
        b₁.inv.app (Ts.obj K.carrier) ≫
            J₁.map (rs.inv.app K.carrier ≫ Ts.map K.str.hom) ≫ j.hom.app K.carrier =
          G₁.map (j.hom.app K.carrier) ≫ rp.inv.app (J₀.obj K.carrier) ≫
            Tp.map (b₀.inv.app K.carrier ≫ J₀.map K.str.hom))) ∧
    (∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
      (U : B ⥤ B) (P Q : A ⥤ IsoAlgebra U) (α β : P ⟶ Q),
      (∀ X : A, (α.app X).hom.f = (β.app X).hom.f) → α = β) := by
  have square (K : C₀) :
      b₁.inv.app (Ts.obj K) ≫ J₁.map (rs.inv.app K) ≫ j.hom.app (F₀.obj K) =
        G₁.map (j.hom.app K) ≫ rp.inv.app (J₀.obj K) ≫ Tp.map (b₀.inv.app K) := by
    have h := congrArg
      (fun f ↦ b₁.inv.app (Ts.obj K) ≫ J₁.map (rs.inv.app K) ≫ f ≫
        rp.inv.app (J₀.obj K) ≫ Tp.map (b₀.inv.app K)) (mixed K)
    simpa [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc] using h
  have intertwining (K : IsoAlgebra F₀) :
      b₁.inv.app (Ts.obj K.carrier) ≫
          J₁.map (rs.inv.app K.carrier ≫ Ts.map K.str.hom) ≫ j.hom.app K.carrier =
        G₁.map (j.hom.app K.carrier) ≫ rp.inv.app (J₀.obj K.carrier) ≫
          Tp.map (b₀.inv.app K.carrier ≫ J₀.map K.str.hom) := by
    have hn := j.hom.naturality K.str.hom
    simp only [Functor.comp_map] at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ Tp.map (J₀.map K.str.hom)) (square K.carrier)
  let component (K : IsoAlgebra F₀) :
      (mapOfNatIso rs.symm ⋙ mapOfNatIso b₁.symm).obj K ≅
        (mapOfNatIso b₀.symm ⋙ mapOfNatIso rp.symm).obj K :=
    ObjectProperty.isoMk _ (Algebra.isoMk (j.app K.carrier) (by
      change G₁.map (j.hom.app K.carrier) ≫
          (rp.inv.app (J₀.obj K.carrier) ≫
            Tp.map (b₀.inv.app K.carrier ≫ J₀.map K.str.hom)) =
        (b₁.inv.app (Ts.obj K.carrier) ≫
          J₁.map (rs.inv.app K.carrier ≫ Ts.map K.str.hom)) ≫ j.hom.app K.carrier
      simpa only [Category.assoc] using (intertwining K).symm))
  let lift : mapOfNatIso rs.symm ⋙ mapOfNatIso b₁.symm ≅
      mapOfNatIso b₀.symm ⋙ mapOfNatIso rp.symm :=
    NatIso.ofComponents component (fun φ ↦
      ObjectProperty.hom_ext _ (Algebra.Hom.ext (j.hom.naturality φ.hom.f)))
  refine ⟨⟨lift, ?_, ?_, intertwining⟩, ?_⟩
  · intro K
    rfl
  · intro K
    rfl
  · intro A _ B _ U P Q α β h
    apply NatTrans.ext
    funext X
    exact ObjectProperty.hom_ext _ (Algebra.Hom.ext (h X))

end CategoryTheory.Endofunctor.IsoAlgebra
