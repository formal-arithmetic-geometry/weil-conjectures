/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.SheafTensor
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous-function condensation of topological modules

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, first two sentences
(blueprint: lem-sfb-topological-module-condensation).

The action is specified on the canonical images of presheaf pure tensors, without
identifying sections of the sheaf tensor with tensor products of sections.

## Main definitions

- `Profinite.continuousModuleTensorGenerator`: the canonical image of a presheaf pure tensor.

## Main statements

- `Profinite.topologicalModule_condensation`: the additive functor with all specified formulas.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace Profinite

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The canonical image of a pure tensor in the underlying presheaf of the sheaf tensor.
Source: blueprint `lem-sfb-subfield-flat.proof.md`, continuous scalar action, and the
sheaf-tensor comparison of `sk-def-sfb-sheaf-tensor`
(blueprint: lem-sfb-topological-module-condensation). -/
noncomputable def continuousModuleTensorGenerator
    (F : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) (S : Profinite.{u})
    (a : C(S, R)) (h : F.obj.obj (op S)) :
    ((continuousCoefficientRingObj R ⊗ F).obj.obj (op S)) :=
  (Functor.LaxMonoidal.μ
    (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (continuousCoefficientRingObj R) F).app (op S)
      (TensorProduct.tmul ℤ (ULift.up a) h)

/-- Continuous functions condense topological modules additively, with their specified
pointwise action, maps, finite-product comparison and regular-module normalization.
Source: blueprint main-20261015 `lem-sfb-subfield-flat.proof.md`, first two sentences
(blueprint: lem-sfb-topological-module-condensation).

Proof: (1) Form C(S,M) with pointwise addition and precomposition. A compatible family
on a finite jointly surjective profinite cover descends as a function. The coproduct of
that cover is compact and its target Hausdorff, so the surjection is a quotient map
(`lem-sfb-compact-hausdorff-surjection-quotient`); the descended function is continuous.
The empty space has exactly one section. No separation property of M is needed.
(2) Joint continuity of scalar multiplication makes (a,h) ↦ (s ↦ a(s) • h(s)) continuous.
Pointwise distributivity extends this bilinearly to the objectwise integer tensor;
precomposition commutes with this extension.
(3) The universal property of sheafification (`def-weil-pbc-sheafification`) gives the
unique action on the sheaf tensor (`sk-def-sfb-sheaf-tensor`). Strong monoidality sends
the pointwise unit and associativity equations to the internal module identities.
The ring-object normalization of `det-def-sfb-ring-object-sheaf` identifies the scalar
multiplication and unit with those of the given continuous coefficient ring object.
(4) Postcompose with continuous linear maps. Pointwise linearity gives action
compatibility before sheafification, hence after sheafification by uniqueness.
Evaluation verifies preservation of identities, compositions and sums.
(5) Continuous maps into a product are exactly tuples of continuous maps. These inverse
coordinate maps commute with restrictions and actions. Projections separate sections,
so their cone is a product also in internal modules, including the empty family.
(6) For M = R the section sheaf is the given scalar sheaf. Both its action and ring
multiplication extend the same pointwise presheaf multiplication, so uniqueness
identifies it with the regular module.
-/
theorem topologicalModule_condensation :
    ∃ (F : TopModuleCat.{u} R ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (continuousCoefficientRingObj R)),
    ∃ (e : ∀ (M : TopModuleCat.{u} R) (S : Profinite.{u}),
      (F.obj M).X.obj.obj (op S) ≃+ C(S, M)),
      F.Additive ∧
      (∀ (M : TopModuleCat.{u} R) (S T : Profinite.{u}) (q : T ⟶ S)
        (h : (F.obj M).X.obj.obj (op S)),
        e M T ((F.obj M).X.obj.map q.op h) = (e M S h).comp q.hom.hom) ∧
      (∀ (M : TopModuleCat.{u} R),
        (∀ (S : Profinite.{u}) (a : C(S, R)) (h : C(S, M)) (s : S),
          e M S ((ModObj.smul (M := continuousCoefficientRingObj R)
            (X := (F.obj M).X)).hom.app (op S)
              (continuousModuleTensorGenerator R (F.obj M).X S a ((e M S).symm h))) s =
                a s • h s) ∧
        (∀ (g : continuousCoefficientRingObj R ⊗ (F.obj M).X ⟶ (F.obj M).X),
          (∀ (S : Profinite.{u}) (a : C(S, R)) (h : C(S, M)) (s : S),
            e M S (g.hom.app (op S)
              (continuousModuleTensorGenerator R (F.obj M).X S a ((e M S).symm h))) s =
                a s • h s) →
          g = ModObj.smul (M := continuousCoefficientRingObj R) (X := (F.obj M).X))) ∧
      (∀ (M N : TopModuleCat.{u} R) (f : M ⟶ N) (S : Profinite.{u})
        (h : (F.obj M).X.obj.obj (op S)) (s : S),
        e N S ((F.map f).hom.hom.app (op S) h) s = f.hom (e M S h s)) ∧
      (∀ (I : Type u) [Finite I] (M : I → TopModuleCat.{u} R),
        ∃ (p : F.obj (TopModuleCat.of R (∀ i, M i)) ≅ ∏ᶜ fun i ↦ F.obj (M i)),
          (∀ i, p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i =
            F.map (TopModuleCat.ofHom (ContinuousLinearMap.proj i))) ∧
          (∀ (S : Profinite.{u})
            (h : (F.obj (TopModuleCat.of R (∀ i, M i))).X.obj.obj (op S)) (i : I) (s : S),
            e (M i) S (((p.hom ≫ Pi.π (fun i ↦ F.obj (M i)) i).hom.hom.app (op S)) h) s =
              e (TopModuleCat.of R (∀ i, M i)) S h s i) ∧
          (∀ (S : Profinite.{u}) (h : (∏ᶜ fun i ↦ F.obj (M i)).X.obj.obj (op S))
            (i : I) (s : S),
            e (TopModuleCat.of R (∀ i, M i)) S (p.inv.hom.hom.app (op S) h) s i =
              e (M i) S ((Pi.π (fun i ↦ F.obj (M i)) i).hom.hom.app (op S) h) s)) ∧
      (∃ (r : F.obj (TopModuleCat.of R R) ≅ Mod.regular (continuousCoefficientRingObj R)),
        ∀ (S : Profinite.{u}) (h : (F.obj (TopModuleCat.of R R)).X.obj.obj (op S)),
          (r.hom.hom.hom.app (op S) h).down = e (TopModuleCat.of R R) S h) := by
  sorry

end Profinite
