/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of closed subschemes to finite constant fields

Source: Weil conjectures blueprint, main-20261015, `sec-deligne-laumon-general`,
`sk-i-dl-general-real/lem-zl-bertini-finite-cover-curve.proof.md`, final paragraph
(blueprint: lem-zl-bertini-finite-field-descent).

The isomorphism over `Spec k` and its equation after projection to `X₀` express equality
as closed subschemes of the geometric fibre. They retain the scheme structure, including
nilpotents. The resulting automorphism of `C` is a scheme automorphism; it is semilinear
on the coefficient field and need not be a morphism over `k`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- A closed subscheme of a finite-type geometric fibre descends to a finite constant-field
extension, and some positive power of geometric Frobenius restricts to an automorphism.
Source: blueprint main-20261015, `lem-zl-bertini-finite-cover-curve.proof.md`, final paragraph
(blueprint: lem-zl-bertini-finite-field-descent).

Proof:
1. The root-field description of `lem-weil-unique-subfield-of-closure` makes the fields
   `F_{q^n}`, ordered by divisibility of positive indices, a directed union equal to `k`.
   Every algebraic element generates a finite field and hence belongs to one such field.
   Compatible maps on these subfields give the colimit map by evaluating at any stage
   containing an element; common multiples prove independence and the ring identities.
2. Their spectra form an affine inverse system with limit `Spec k`, by
   `lem-weil-pbc-limit-affine-transition`. Each stage is quasi-compact and quasi-separated
   (`lem-weil-pbc-affine-scheme-qcqs`), as required by `thm-pd-spreading-out`.
3. Base change preserves finite type (`lem-sfb-finite-type-composition-base-change`).
   On an affine chart a closed immersion is induced by a quotient ring
   (`def-weil-closed-immersion`), so the induced structure map of `C` is finite type too
   (`def-weil-finite-type-morphism`). This retains the defining ideals, not just their zeros.
4. Fields are Noetherian. Finite-type schemes over them are locally Noetherian by
   `pqf-lem-locnoeth-lft`, and thus quasi-separated by
   `lem-weil-pbc-locally-noetherian-quasi-separated`. Quasi-compactness and
   quasi-separatedness of their structure maps follow from
   `lem-weil-pbc-qcqs-morphism-permanence`. The maps are locally finitely presented by
   `pqf-lem-lft-fp-locnoeth`, hence finitely presented (`def-sbc-locally-finite-presentation`).
5. Apply the object clause of `thm-pd-spreading-out` to descend `C`. Its morphism clause
   then descends the given inclusion into the already defined model of `X` after enlarging
   the finite field. Base-change associativity (`def-pc-base-change`) gives compatibility.
6. The descended morphism is locally finite type: finite algebra generators on source
   charts also generate over the target chart, since the base field factors through it.
   Principal localizations preserve finite type. The Noetherian target and the preceding
   quasi-compactness and quasi-separatedness give finite presentation, using
   `pqf-lem-lft-fp-locnoeth` and `lem-weil-pbc-qcqs-morphism-permanence` once more.
7. Apply `lemma-nagata-closed-immersion-stage-exists` to obtain a closed immersion at a
   later positive stage. The descended isomorphism commutes with its actual embedding,
   giving the asserted closed subscheme after base change, including nilpotents.
8. By `lem-weil-unique-subfield-of-closure`, geometric Frobenius to the `m`th power fixes
   `F_{q^m}`. Base change of the identity of the descended subscheme together with this
   coefficient automorphism gives an automorphism of its base change, with inverse from
   the inverse coefficient automorphism. Conjugate by the descended isomorphism. The
   projection equations and `def-weil-frobenius-detailed` identify its composite with `i`
   with the `m`th power of the ambient geometric Frobenius composed with `i`. -/
theorem exists_closed_subscheme_finiteField_descent (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (C : Scheme.{u}) (i : C ⟶ (D.geometricFiber X₀).left) [IsClosedImmersion i] :
    ∃ (m : ℕ) (hm : 1 ≤ m) (Cₘ : Over (Spec (CommRingCat.of (D.extensionSubfield m hm))))
      (iₘ : Cₘ ⟶ (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀),
      IsClosedImmersion iₘ.left ∧
      (∃ e : Over.mk (i ≫ (D.geometricFiber X₀).hom) ≅
          (Over.pullback (Spec.map
            (CommRingCat.ofHom (D.extensionSubfield m hm).subtype))).obj Cₘ,
        e.hom.left ≫
            pullback.fst Cₘ.hom
              (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
            iₘ.left ≫
            pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) =
          i ≫ pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      ∃ φ : Aut C, φ.hom ≫ i = i ≫ (D.geometricFrobenius X₀ ^ m).hom :=
  sorry

end WeilConjectures.FiniteFieldDatum
