/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Normalization commutes with a further purely inseparable extension

Source: Stacks Project, `varieties.tex`, Tags 0C3N, 038M and 038O
(blueprint: lem-trf-normalization-inseparable-base-change).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Normalization commutes with a further finite purely inseparable extension when the
first normalization is geometrically normal.

Source: Stacks Project, `varieties.tex`, Tags 0C3N, 038M and 038O
(blueprint: lem-trf-normalization-inseparable-base-change).

Proof, following the four proof steps of the node:

1. Purely inseparable base change is a homeomorphism (`lem-pc-homeo-pure-insep`),
so each base change of the integral C is irreducible and nonempty, and its reduction
Xᵢ is integral. Its normalization is finite, surjective and an isomorphism on a dense
normal open by `lem-weil-pbc-reduced-algebraic-normalization-field-change` and
`lem-sc-normalization-exists`. Its local rings are normal domains by
`lem-sbc-integral-closure-finite-normal-product`.

2. Set Y = N₁ ×_{k₁} k₂. Geometric normality makes Y reduced and normal, and the
purely inseparable homeomorphism to N₁ makes it integral. The base change of ν₁
is finite (`lem-weil-pbc-finite-morphism-permanence`); composing with the base change
of the reduction immersion gives the canonical finite map q : Y → C_{k₂}.
Since Y is reduced, q factors uniquely through X₂. On affine rings its finite module
structure factors through the nilradical quotient, so the factor is finite. Over the
open corresponding to the first dense normal locus, Y is the base change of that
locus. This open is reduced because it is an open of Y; its reduction therefore is
the corresponding open of X₂. Thus the factor is an isomorphism on a dense open U₂.

3. X₂ is locally Noetherian (`lem-weil-pbc-finite-type-over-noetherian`); Y and N₂
are normal, finite and surjective over X₂. Their inverse images of U₂ are dense,
and ν₂ is an isomorphism over U₂ because U₂ is normal. Apply
`lem-sbc-finite-normal-dense-open-iso` to obtain e : N₂ ≅ Y over X₂, hence C_{k₂}.
Any two isomorphisms over C_{k₂} are over X₂ because its reduction immersion is mono.
They agree over U₂. Affine locally their maps into the domain of normalization agree
after injection into its fraction field, hence agree everywhere. This gives uniqueness
only among isomorphisms over C_{k₂}. For any field extension L/k₂, the base change
of N₂ identifies with N₁ ×_{k₁} L, proving geometric normality over k₂.

4. Pull back any closed immersion D₁ → N₁ along N₂ → N₁ induced by e.
Pullback pasting identifies this inverse image with D₁ ×_{k₁} k₂, compatibly with
both projections. Taking reductions gives the displayed isomorphism with its equations
over D₁ and k₂. If D₁ is finite over k₁, its field base change is finite over k₂
(`lem-weil-pbc-finite-morphism-permanence`). Its reduction is affine locally the
nilradical quotient of a finite algebra, hence is still finite. Transporting across
the displayed isomorphism proves finiteness of the reduced inverse image itself.
-/
theorem normalization_inseparable_base_change
    (k k1 k2 : Type u)
    [Field k] [Field k1] [Field k2]
    [Algebra k k1] [Algebra k1 k2] [Algebra k k2]
    [IsScalarTower k k1 k2]
    [Module.Finite k k1] [IsPurelyInseparable k k1]
    [Module.Finite k1 k2] [IsPurelyInseparable k1 k2]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsIntegral C]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k))] :
    ∃ (h1 : IsIntegral ((pullback (C ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subscheme)) (h2 : IsIntegral
((pullback (C ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k k2)))).nilradical.subscheme)),
      (∀ (L : Type u) [Field L] [Algebra k1 L],
        ∀ z : ↥(pullback ((@Scheme.fromNormalization _ h1) ≫
          (pullback (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
          pullback.snd (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom
(algebraMap k1 L)))),
          IsDomain ((pullback ((@Scheme.fromNormalization _ h1) ≫
          (pullback (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
          pullback.snd (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom
(algebraMap k1 L)))).presheaf.stalk z) ∧
          IsIntegrallyClosed ((pullback ((@Scheme.fromNormalization _ h1) ≫
          (pullback (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
          pullback.snd (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom
(algebraMap k1 L)))).presheaf.stalk z)) →
      ∃ e : @Scheme.normalization _ h2 ≅ pullback ((@Scheme.fromNormalization _ h1) ≫ (pullback (C
        ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
        k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
        (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1 k2))),
        (e.hom ≫ (pullback.map ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec
          (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
          k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
          (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
          k2))) (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k2)))
            ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫ pullback.fst (C ↘ Spec
              (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k1))))
            (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k k1)))
            (by simp [Category.assoc, pullback.condition])
            (by
              simpa only [Category.comp_id, Category.id_comp, ← Spec.map_comp,
                ← CommRingCat.ofHom_comp] using
                congrArg (fun f : k →+* k2 ↦ Spec.map (CommRingCat.ofHom f))
                  (IsScalarTower.algebraMap_eq k k1 k2).symm)) = (@Scheme.fromNormalization _ h2) ≫
          (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
          k2)))).nilradical.subschemeι) ∧
        (∀ e' : @Scheme.normalization _ h2 ≅ pullback ((@Scheme.fromNormalization _ h1) ≫
          (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
          k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
          (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
          k2))),
          e'.hom ≫ (pullback.map ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec
            (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
            k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
            (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
            k2))) (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k2)))
            ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫ pullback.fst (C ↘ Spec
              (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k1))))
            (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k k1)))
            (by simp [Category.assoc, pullback.condition])
            (by
              simpa only [Category.comp_id, Category.id_comp, ← Spec.map_comp,
                ← CommRingCat.ofHom_comp] using
                congrArg (fun f : k →+* k2 ↦ Spec.map (CommRingCat.ofHom f))
                  (IsScalarTower.algebraMap_eq k k1 k2).symm)) = (@Scheme.fromNormalization _ h2) ≫
          (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
          k2)))).nilradical.subschemeι → e' = e) ∧
        (∀ (L : Type u) [Field L] [Algebra k2 L],
          ∀ z : ↥(pullback ((@Scheme.fromNormalization _ h2) ≫ (pullback (C ↘ Spec (CommRingCat.of
            k)) (Spec.map (CommRingCat.ofHom (algebraMap k k2)))).nilradical.subschemeι ≫
            pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
            k2)))) (Spec.map (CommRingCat.ofHom (algebraMap k2 L)))),
            IsDomain ((pullback ((@Scheme.fromNormalization _ h2) ≫ (pullback (C ↘ Spec
              (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k2)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k2)))) (Spec.map (CommRingCat.ofHom (algebraMap k2
              L)))).presheaf.stalk z) ∧
            IsIntegrallyClosed ((pullback ((@Scheme.fromNormalization _ h2) ≫ (pullback (C ↘ Spec
              (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k2)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k2)))) (Spec.map (CommRingCat.ofHom (algebraMap k2
              L)))).presheaf.stalk z)) ∧
        (∀ (D1 : Scheme.{u}) (d1 : D1 ⟶ @Scheme.normalization _ h1)
          (_ : IsClosedImmersion d1),
          ∃ eD : (pullback d1 (e.hom ≫ pullback.fst ((@Scheme.fromNormalization _ h1) ≫ (pullback
            (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
            k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
            (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
            k2))))).nilradical.subscheme ≅ (pullback (d1 ≫ (@Scheme.fromNormalization _ h1) ≫
            (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
            k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
            (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
            k2)))).nilradical.subscheme,
            (eD.hom ≫ (pullback (d1 ≫ (@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec
              (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
              k2)))).nilradical.subschemeι ≫ pullback.fst (d1 ≫ (@Scheme.fromNormalization _ h1) ≫
              (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
              k2))) = (pullback d1 (e.hom ≫ pullback.fst ((@Scheme.fromNormalization _ h1) ≫
              (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
              k2))))).nilradical.subschemeι ≫ pullback.fst d1 (e.hom ≫ pullback.fst
              ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
              pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap
              k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1 k2))))) ∧
            (eD.hom ≫ (pullback (d1 ≫ (@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec
              (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
              k2)))).nilradical.subschemeι ≫ pullback.snd (d1 ≫ (@Scheme.fromNormalization _ h1) ≫
              (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
              k2))) = (pullback d1 (e.hom ≫ pullback.fst ((@Scheme.fromNormalization _ h1) ≫
              (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k
              k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1
              k2))))).nilradical.subschemeι ≫ pullback.snd d1 (e.hom ≫ pullback.fst
              ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
              pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap
              k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1 k2)))) ≫
              (@Scheme.fromNormalization _ h2) ≫ (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k2)))).nilradical.subschemeι ≫ pullback.snd (C ↘
              Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k2)))) ∧
            (IsFinite (d1 ≫ (@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of
              k)) (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
              pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap
              k k1)))) → IsFinite ((pullback d1 (e.hom ≫ pullback.fst ((@Scheme.fromNormalization
              _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom
              (algebraMap k k1)))).nilradical.subschemeι ≫ pullback.snd (C ↘ Spec (CommRingCat.of
              k)) (Spec.map (CommRingCat.ofHom (algebraMap k k1)))) (Spec.map (CommRingCat.ofHom
              (algebraMap k1 k2))))).nilradical.subschemeι ≫ pullback.snd d1 (e.hom ≫ pullback.fst
              ((@Scheme.fromNormalization _ h1) ≫ (pullback (C ↘ Spec (CommRingCat.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k k1)))).nilradical.subschemeι ≫
              pullback.snd (C ↘ Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap
              k k1)))) (Spec.map (CommRingCat.ofHom (algebraMap k1 k2)))) ≫
              (@Scheme.fromNormalization _ h2) ≫ (pullback (C ↘ Spec (CommRingCat.of k)) (Spec.map
              (CommRingCat.ofHom (algebraMap k k2)))).nilradical.subschemeι ≫ pullback.snd (C ↘
              Spec (CommRingCat.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k2)))))) := by
  sorry

end AlgebraicGeometry
