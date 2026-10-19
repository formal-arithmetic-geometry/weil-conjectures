/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyOfFinitePresentation
import Sheaf.FieldTheory.AlgebraicSeparableSmooth

/-!
# Finite étale descent to finite intermediate fields

Source: Stacks Project, Fundamental Groups, Tag 0BTV (lemma-limit), specialized to
constant-field base changes (blueprint: lem-wf-finite-etale-field-limit-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The specified base change `X₀ ×_K Spec A`, using the chosen fibre product.
Source: Stacks Tag 0BTV, field-system specialization
(blueprint: lem-wf-finite-etale-field-limit-descent). -/
abbrev fieldExtensionBase {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) (A : Type u) [Field A] [Algebra K A] : Scheme.{u} :=
  Limits.pullback X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The canonical map between the specified constant-field base changes induced by a
`K`-algebra map. It preserves the projection to `X₀` and induces `Spec φ` on scalars.
Source: Stacks Tag 0BTV and the fibre-product universal property
(blueprint: lem-wf-finite-etale-field-limit-descent). -/
def fieldExtensionBaseMap {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) {A B : Type u} [Field A] [Field B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) :
    fieldExtensionBase X₀ B ⟶ fieldExtensionBase X₀ A :=
  Limits.pullback.map X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K B)))
    X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (𝟙 X₀.left) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext x
      exact (φ.commutes x).symm)

/-- Finite étale covers, all their morphisms, and equality of morphisms descend to finite
intermediate fields of a separable algebraic extension.

Source: Stacks Tag 0BTV (lemma-limit), specialized to the finite intermediate fields
(blueprint: lem-wf-finite-etale-field-limit-descent).

Proof:
1. The finite intermediate fields form a small nonempty directed system with union L,
   by lem-kun-algebraic-separable-smooth; its least stage is K.
2. Every field base change is separated of finite type, hence qcqs, by
   lem-pod-separated-finite-type-base-change and lem-weil-pbc-qcqs-over-affine.
   The transition maps are affine by lem-weil-pbc-affine-morphism-permanence.
3. Spec L is the limit of the field spectra by lem-weil-pbc-spec-small-colimit-limit.
   The fibre-product universal property (def-pc-fibre-product) exhibits X_L as the
   limit of the specified X_E, with exactly these projections.
4. Finite étale covers are locally finitely presented (def-weil-etale-morphism), and
   finite plus locally finitely presented is finitely presented by
   lem-trf-finite-morphism-finite-presentation.
5. Object descent in thm-pd-spreading-out gives a finitely presented model. Its source
   is qcqs by lem-weil-pbc-qcqs-morphism-permanence.
6. On a tail, lem-weil-pbc-descend-finite makes this model finite. Finite presentation
   and qcqs persist by lem-weil-pbc-qcqs-morphism-permanence.
7. On a further tail, lem-weil-pbc-descend-etale makes it étale; it remains finite by
   lem-weil-pbc-finite-morphism-permanence. Pullback pasting identifies its limit with
   the original cover, giving (1).
8. The morphism clause of thm-pd-spreading-out gives (2). The two comparison isomorphisms
   preserve the projections to the original covers, so they are the canonical pullback
   associativity identifications, not arbitrary changes of coordinates.
9. The equality clause of thm-pd-spreading-out gives (3) for the two finitely presented
   covers. Every larger index is a finite intermediate field containing the initial one.
-/
theorem finiteEtale_fieldLimit_descent {K L : Type u} [Field K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L] (X₀ : Over (Spec (.of K)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (∀ P : (fieldExtensionBase X₀ L).FiniteEtale,
      ∃ (E : IntermediateField K L), FiniteDimensional K E ∧
        ∃ P_E : (fieldExtensionBase X₀ E).FiniteEtale,
          Nonempty ((pullback (fieldExtensionBaseMap X₀ E.val)).obj P_E ≅ P)) ∧
    (∀ (E : IntermediateField K L), FiniteDimensional K E →
      ∀ (P Q : (fieldExtensionBase X₀ E).FiniteEtale)
        (f : (pullback (fieldExtensionBaseMap X₀ E.val)).obj P ⟶
          (pullback (fieldExtensionBaseMap X₀ E.val)).obj Q),
      ∃ (E' : IntermediateField K L) (_ : FiniteDimensional K E') (h : E ≤ E')
        (f' : (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj P ⟶
          (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj Q)
        (eP : (pullback (fieldExtensionBaseMap X₀ E'.val)).obj
            ((pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj P) ≅
          (pullback (fieldExtensionBaseMap X₀ E.val)).obj P)
        (eQ : (pullback (fieldExtensionBaseMap X₀ E'.val)).obj
            ((pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj Q) ≅
          (pullback (fieldExtensionBaseMap X₀ E.val)).obj Q),
        eP.hom.hom.left ≫ Limits.pullback.fst P.obj.hom
            (fieldExtensionBaseMap X₀ E.val) =
          Limits.pullback.fst _ (fieldExtensionBaseMap X₀ E'.val) ≫
            Limits.pullback.fst P.obj.hom
              (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)) ∧
        eQ.hom.hom.left ≫ Limits.pullback.fst Q.obj.hom
            (fieldExtensionBaseMap X₀ E.val) =
          Limits.pullback.fst _ (fieldExtensionBaseMap X₀ E'.val) ≫
            Limits.pullback.fst Q.obj.hom
              (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)) ∧
        eP.inv ≫ (pullback (fieldExtensionBaseMap X₀ E'.val)).map f' ≫ eQ.hom = f) ∧
    (∀ (E : IntermediateField K L), FiniteDimensional K E →
      ∀ (P Q : (fieldExtensionBase X₀ E).FiniteEtale) (f h : P ⟶ Q),
        (pullback (fieldExtensionBaseMap X₀ E.val)).map f =
          (pullback (fieldExtensionBaseMap X₀ E.val)).map h →
        ∃ (E' : IntermediateField K L) (_ : FiniteDimensional K E') (hE : E ≤ E'),
          (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion hE))).map f =
            (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion hE))).map h) :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
