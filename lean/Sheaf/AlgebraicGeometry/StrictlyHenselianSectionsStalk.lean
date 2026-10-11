/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Sections over a strictly henselian local scheme and the geometric stalk

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-sections-stalk).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- For an abelian sheaf on a strictly henselian local scheme the global germ is an
isomorphism, natural in the sheaf. Source: Stacks Project, Lemma Tag 03QO.
(blueprint: lem-weil-pbc-strictly-henselian-sections-stalk)

Proof:
1. By `def-weil-pbc-geometric-stalks`, the stalk is the colimit of the sections over the
   opposite category of pointed etale neighbourhoods. The germ is the coprojection at
   `(Spec R, s)`. The coprojections commute with sheaf morphisms, giving naturality.
2. For a pointed neighbourhood `(U, ū)`, shrink through the image of `ū` to an affine
   chart `Spec A`, by `lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`.
   The resulting ring map `R → A` is etale, and the marked prime lies over the maximal
   ideal of `R`, by `def-weil-affine-spectrum` and `def-weil-etale-morphism`.
3. By `lem-weil-pbc-etale-algebra-residue-field-separable`, the residue extension is
   finite separable. Strict henselianity and `lem-pc-sepclosed-finite-sep-trivial` make
   it an isomorphism. The affine chart identifies this with the residue map at `u`.
4. Henselianity gives simple-root lifting by `lem-weil-pbc-henselian-local-root-lifting`.
   The lemma `lem-weil-pbc-root-lifting-etale-retraction` gives an algebra retraction
   `A → R` carrying the maximal ideal back to the marked prime.
5. Taking spectra and composing with the chart inclusion gives a section `Spec R → U`
   through `u`: its composite to `Spec R` is the identity by functoriality of `Spec`.
6. The residue map of this section is inverse to that of `U → Spec R`. The field map
   of `ū` composed with the latter equals that of `s`, so the section sends `s` to `ū`.
   This uses `def-weil-geometric-point` and `def-weil-residue-field`, and works for every
   algebraically closed Ω over the residue field, not only a chosen closure.
7. The pointed neighbourhood category is cofiltered by
   `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`. Its full subcategory on
   `(Spec R, s)` maps to every neighbourhood by steps 2-6 and has only the identity
   endomorphism. Apply `lem-weil-pbc-colimit-initial-full-subcategory` and
   `lem-weil-pbc-colimit-constant-connected-diagram`. The resulting colimit comparison
   is precisely the germ coprojection and is an isomorphism; step 1 gives naturality. -/
theorem strictlyHenselianSections_geometricStalk_isIso
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : s default = IsLocalRing.closedPoint R) :
    (∀ (F : Sheaf (smallEtaleTopology (Spec (.of R)))
      (AddCommGrpCat.{(max u v) + 1})),
      IsIso ((Scheme.pointSmallEtale s).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of R))))
        (Over.homMk s (Category.comp_id s)) F.obj)) ∧
    (∀ (F G : Sheaf (smallEtaleTopology (Spec (.of R)))
      (AddCommGrpCat.{(max u v) + 1})) (φ : F ⟶ G),
      (Scheme.pointSmallEtale s).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (Over.homMk s (Category.comp_id s)) F.obj ≫
        (Scheme.pointSmallEtale s).sheafFiber.map φ =
      φ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (Over.homMk s (Category.comp_id s)) G.obj) := by
  sorry

end AlgebraicGeometry.Scheme
