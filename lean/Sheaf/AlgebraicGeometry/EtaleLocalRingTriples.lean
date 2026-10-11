/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Sheaf.AlgebraicGeometry.EtaleResidueTriples

/-!
# Affine pointed étale neighbourhoods and residue-field triples

Source: Stacks Project, Tags 03PQ, 04HT and 04HX
(blueprint: lem-weil-pbc-etale-local-ring-triples).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Stacks, Tags 03PQ, 04HT and 04HX
(blueprint: lem-weil-pbc-etale-local-ring-triples).

Proof:
1. Factor the point through the affine chart. Its prime is the kernel of the
corresponding ring map, and its residue-field map is the map in `SpecToEquivOfField`
(def-weil-affine-spectrum, def-weil-residue-field, def-weil-geometric-point).
2. Shrink any pointed neighbourhood to an affine open containing its point
(lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink).
3. The category of all neighbourhoods is cofiltered by Tag 03PQ
(lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered). The pointed chart itself
gives a nonempty affine subcategory. Shrink the fibre products and
equalizers to affine neighbourhoods. Fullness gives cofilteredness of the affine
subcategory (lem-weil-pbc-colimit-initial-full-subcategory).
4. Shrink inside the inverse image of the chosen chart. Every affine neighbourhood
then receives a map from one factoring through the chart. The full inclusion is
initial, and its opposite preserves the ring colimit
(lem-weil-pbc-colimit-initial-full-subcategory).
5. For a neighbourhood over the chart, the residue field is finite separable over
that of the base (lem-weil-pbc-etale-algebra-residue-field-separable, Tag 04HT).
Its embedding into Ω therefore lands in the relative separable closure
(def-weil-pbc-relative-separable-closure). Cancellation of the open immersion shows
that its ring is étale over A (lem-weil-pbc-etale-composition-cancellation).
The equation that the point lies over x, cancelled through the open immersion,
shows that q lies over p and that the residue-field embedding is compatible over κ(p).
6. For morphisms, cancellation of the open immersion identifies Y-morphisms over
the chart with U-morphisms. The affine spectrum anti-equivalence identifies these
with A-ring maps (def-weil-affine-spectrum). Carrying one specified point to the
other is exactly commutation of the maps to Ω, equivalently inverse-image equality
of primes and agreement of residue embeddings. This gives full faithfulness.
7. Conversely a triple gives its point by composing B → κ(q) → K → Ω.
Compatibility over κ(p) makes it a point over x. Étale composition gives a
neighbourhood of Y (lem-weil-pbc-etale-composition-cancellation). Its prime and
residue embedding recover the given triple, proving essential surjectivity and
the claimed equivalence with its specified effect on rings and points.
8. Under this equivalence the global-section diagram is naturally the diagram B.
Transport the colimit cocone along it and along the initial inclusion; the resulting
isomorphisms commute with every coprojection (def-weil-pbc-category-colimit,
lem-weil-pbc-colimit-initial-full-subcategory).

The three colimits are expressed by universal cocones, avoiding any additional
existence hypothesis or choice of a small skeleton. -/
theorem etale_local_ring_triples
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c => IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c => ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    IsCofiltered N ∧ Q.ι.Initial ∧
      (∀ c : N, ∃ d : NU, Nonempty (d.obj ⟶ c)) ∧
      (∀ (c : NU) (z : c.obj.obj.1.left.residueField
          (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).1),
        (SpecToEquivOfField Ω c.obj.obj.1.left c.obj.obj.2.left).2 z ∈ K) ∧
      ∃ (E : NUᵒᵖ ≌ T) (δ : DU ≅ E.functor ⋙ DT),
        (∀ c : NU,
          let t := E.functor.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) ∧
        ∃ (cn : Cocone D) (cu : Cocone DU) (ct : Cocone DT),
          Nonempty (IsColimit cn) ∧ Nonempty (IsColimit cu) ∧ Nonempty (IsColimit ct) ∧
          ∃ (r : cu.pt ≅ cn.pt) (s : cn.pt ≅ ct.pt),
            (∀ c : NUᵒᵖ, cu.ι.app c ≫ r.hom = cn.ι.app (Q.ι.op.obj c)) ∧
            (∀ c : NUᵒᵖ, cn.ι.app (Q.ι.op.obj c) ≫ s.hom =
              δ.hom.app c ≫ ct.ι.app (E.functor.obj c)) := by
  sorry

end AlgebraicGeometry.Scheme
