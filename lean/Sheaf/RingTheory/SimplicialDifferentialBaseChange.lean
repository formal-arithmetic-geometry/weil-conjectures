/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change of augmented simplicial differential complexes

Source: Stacks Project, Tags 08QZ and 00RV
(blueprint: lem-trf-simplicial-differential-base-change).

The comparison is specified simultaneously for all augmented simplicial algebras.
The tensor algebra is characterized by its pushout universal property in
`CommRingCat`, with both inclusions retained. Thus `inclusion p * base a'`
is precisely the pure tensor `p ⊗ a'`, including when either ring is zero.
No object or map is chosen from the existence theorem below.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory Opposite Simplicial

namespace Algebra.CotangentResolution

/-- The full base-change assertion, including the actual pushout algebras,
the universal-differential models, the comparison and its inverse on tensors,
and naturality for augmentation-preserving maps. The models and maps are
specified on every differential generator, so they cannot be arbitrary maps.
Source: Stacks, Tags 08QZ and 00RV
(blueprint: lem-trf-simplicial-differential-base-change). -/
structure SimplicialDifferentialBaseChange {R R' T : CommRingCat.{u}}
    (α : R ⟶ R') (β : R' ⟶ T) where
  baseChange : Augmentation (Arrow.mk (α ≫ β)) → Augmentation (Arrow.mk β)
  inclusion : ∀ P : Augmentation (Arrow.mk (α ≫ β)),
    P.algebra ⟶ (baseChange P).algebra
  pushout : ∀ (P : Augmentation (Arrow.mk (α ≫ β))) (n : ℕ),
    CategoryTheory.IsPushout (P.base.app (op ⦋n⦌)) α
      ((inclusion P).app (op ⦋n⦌)) ((baseChange P).base.app (op ⦋n⦌))
  inclusion_augmentation : ∀ (P : Augmentation (Arrow.mk (α ≫ β))) (n : ℕ),
    (inclusion P).app (op ⦋n⦌) ≫ (baseChange P).augmentation.app (op ⦋n⦌) =
      P.augmentation.app (op ⦋n⦌)
  sourceModel : ∀ P : Augmentation (Arrow.mk (α ≫ β)), DifferentialModel P
  targetModel : ∀ P : Augmentation (Arrow.mk (α ≫ β)), DifferentialModel (baseChange P)
  iso : ∀ P : Augmentation (Arrow.mk (α ≫ β)),
    (sourceModel P).module ≅ (targetModel P).module
  generator : ∀ (P : Augmentation (Arrow.mk (α ≫ β))) (n : ℕ) (t : T)
    (p : P.algebra.obj (op ⦋n⦌)),
    (iso P).hom.app (op ⦋n⦌)
        (((sourceModel P).termIso n).inv (differentialGenerator P n t p)) =
      ((targetModel P).termIso n).inv
        (differentialGenerator (baseChange P) n t ((inclusion P).app (op ⦋n⦌) p))
  inverse_generator : ∀ (P : Augmentation (Arrow.mk (α ≫ β))) (n : ℕ)
    (t : T) (p : P.algebra.obj (op ⦋n⦌)) (a' : R'),
    (iso P).inv.app (op ⦋n⦌)
        (((targetModel P).termIso n).inv (differentialGenerator (baseChange P) n t
          ((inclusion P).app (op ⦋n⦌) p * (baseChange P).base.app (op ⦋n⦌) a'))) =
      ((sourceModel P).termIso n).inv (differentialGenerator P n (β a' * t) p)
  baseChangeMap : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))},
    AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P' →
      AugmentedMap (𝟙 (Arrow.mk β)) (baseChange P) (baseChange P')
  baseChangeMap_inclusion : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))}
    (h : AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P'),
    inclusion P ≫ (baseChangeMap h).map = h.map ≫ inclusion P'
  sourceMap : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))},
    AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P' →
      ((sourceModel P).module ⟶ (sourceModel P').module)
  sourceMap_generator : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))}
    (h : AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P') (n : ℕ) (t : T)
    (p : P.algebra.obj (op ⦋n⦌)),
    (sourceMap h).app (op ⦋n⦌)
        (((sourceModel P).termIso n).inv (differentialGenerator P n t p)) =
      ((sourceModel P').termIso n).inv
        (differentialGenerator P' n t (h.map.app (op ⦋n⦌) p))
  targetMap : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))},
    AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P' →
      ((targetModel P).module ⟶ (targetModel P').module)
  targetMap_generator : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))}
    (h : AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P') (n : ℕ) (t : T)
    (q : (baseChange P).algebra.obj (op ⦋n⦌)),
    (targetMap h).app (op ⦋n⦌)
        (((targetModel P).termIso n).inv (differentialGenerator (baseChange P) n t q)) =
      ((targetModel P').termIso n).inv (differentialGenerator (baseChange P') n t
        ((baseChangeMap h).map.app (op ⦋n⦌) q))
  naturality : ∀ {P P' : Augmentation (Arrow.mk (α ≫ β))}
    (h : AugmentedMap (𝟙 (Arrow.mk (α ≫ β))) P P'),
    sourceMap h ≫ (iso P').hom = (iso P).hom ≫ targetMap h

namespace SimplicialDifferentialBaseChange

/-- Applying the alternating-complex functor gives the specified chain
isomorphism, with the same degree `-n` components and zero positive terms.
Source: Stacks, Tags 08QZ and 08PN
(blueprint: lem-trf-simplicial-differential-base-change). -/
def complexIso {R R' T : CommRingCat.{u}} {α : R ⟶ R'} {β : R' ⟶ T}
    (S : SimplicialDifferentialBaseChange α β)
    (P : Augmentation (Arrow.mk (α ≫ β))) :
    differentialComplex (f := Arrow.mk (α ≫ β)) (S.sourceModel P) ≅
      differentialComplex (f := Arrow.mk β) (S.targetModel P) :=
  (negativeComplex (ModuleCat.{u} T)).mapIso (S.iso P)

/-- Localization sends the displayed chain isomorphism to the claimed
isomorphism in `D(T)`, retaining both inverse morphisms.
Source: Stacks, Tag 08QZ
(blueprint: lem-trf-simplicial-differential-base-change). -/
def derivedIso {R R' T : CommRingCat.{u}} {α : R ⟶ R'} {β : R' ⟶ T}
    [HasDerivedCategory.{v} (ModuleCat.{u} T)]
    (S : SimplicialDifferentialBaseChange α β)
    (P : Augmentation (Arrow.mk (α ≫ β))) :
    (DerivedCategory.Q (C := ModuleCat.{u} T)).obj
        (differentialComplex (f := Arrow.mk (α ≫ β)) (S.sourceModel P)) ≅
      (DerivedCategory.Q (C := ModuleCat.{u} T)).obj
        (differentialComplex (f := Arrow.mk β) (S.targetModel P)) :=
  (DerivedCategory.Q (C := ModuleCat.{u} T)).mapIso (S.complexIso P)

/-- The degree `-n` map and inverse have exactly the prescribed tensor formulas.
Source: Stacks, Tags 08QZ and 00RV
(blueprint: lem-trf-simplicial-differential-base-change).

Proof: the extension-by-zero coordinate isomorphism used in complexGenerator
identifies degree `-n` with simplicial degree `n`. Naturality of this coordinate
isomorphism reduces both equations to generator and inverse_generator of S.
At positive degrees there are only the zero-module maps. -/
theorem complexIso_generators {R R' T : CommRingCat.{u}} {α : R ⟶ R'} {β : R' ⟶ T}
    (S : SimplicialDifferentialBaseChange α β)
    (P : Augmentation (Arrow.mk (α ≫ β))) (n : ℕ) (t : T)
    (p : P.algebra.obj (op ⦋n⦌)) (a' : R') :
    (S.complexIso P).hom.f (-(n : ℤ))
        (complexGenerator (f := Arrow.mk (α ≫ β)) (S.sourceModel P) n t p) =
      complexGenerator (f := Arrow.mk β) (S.targetModel P) n t
        ((S.inclusion P).app (op ⦋n⦌) p) ∧
      (S.complexIso P).inv.f (-(n : ℤ))
          (complexGenerator (f := Arrow.mk β) (S.targetModel P) n t
            ((S.inclusion P).app (op ⦋n⦌) p * (S.baseChange P).base.app (op ⦋n⦌) a')) =
        complexGenerator (f := Arrow.mk (α ≫ β)) (S.sourceModel P) n (β a' * t) p := by
  sorry

end SimplicialDifferentialBaseChange

/-- Augmented simplicial differential base change exists, without flatness or
polynomial hypotheses, naturally for every augmentation-preserving map.
Source: Stacks, Tags 08QZ and 00RV
(blueprint: lem-trf-simplicial-differential-base-change).

Proof: (1) In each degree form P_n ⊗_R R', with both inclusions; its pushout
universal property induces all simplicial maps. The augmentation is
p ⊗ a' ↦ ε(p)β(a'). Uniqueness in the universal property gives the simplicial
identities and compatibility with the augmentation and with every augmented map.
(2) Apply lem-weil-pbc-kahler-differentials-base-change (00RV) in each degree,
interchanging its tensor factors. It gives E: Ω[P/R] ⊗_R R' ≃ Ω[Q/R'] with
E(dp ⊗ a') = a' d(p ⊗ 1).
(3) The tensor universal property gives mutually inverse maps
(Ω[P/R] ⊗_R R') ⊗_Q T → Ω[P/R] ⊗_P T,
(ω ⊗ a') ⊗ t ↦ ω ⊗ β(a')t, and ω ⊗ t ↦ (ω ⊗ 1) ⊗ t.
The P- and Q-balancing relations identify their two composites with identities.
Composing with E tensored over Q gives the forward comparison. Since
 d(p ⊗ a') = a' d(p ⊗ 1), its inverse is exactly the stated formula.
(4) For any augmented R-algebra map h, the universal derivation induces the
map dp ⊗ t ↦ d(h(p)) ⊗ t. The augmentation equation ensures tensor balancing.
Both composites with the comparison agree on these generators; these generate
the whole module. Apply this to every simplicial operator (in particular every
face and degeneracy) and every component of an augmented simplicial map.
This constructs the normalized sourceMap, targetMap, and naturality equation.
(5) Apply negativeComplex: compatibility with the faces commutes with their
alternating sums, with zero outgoing differential in degree zero and zero
positive terms. Termwise inverse identities give inverse chain maps. Applying
the derived localization functor preserves these identities, as in derivedIso.
None of these constructions uses flatness, polynomial terms or a resolution. -/
theorem exists_simplicialDifferentialBaseChange {R R' T : CommRingCat.{u}}
    (α : R ⟶ R') (β : R' ⟶ T) : Nonempty (SimplicialDifferentialBaseChange α β) := by
  sorry

end Algebra.CotangentResolution
