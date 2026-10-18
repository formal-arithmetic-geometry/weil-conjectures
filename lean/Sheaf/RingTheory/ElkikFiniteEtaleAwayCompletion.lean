/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.RingTheory.IntegralOverHenselianPair
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Elkik equivalence for finite algebras étale away from an ideal

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé V, Theorem 1.2.4,
printed p. 64 (blueprint: lem-per-elkik-finite-etale-away-completion).

Algebras and algebra homomorphisms are encoded by `Under B`. The canonical functor is
Mathlib's `CommRingCat.tensorProd`, restricted by `ObjectProperty.lift` to the finite
algebras étale away from the ideal. Its well-definedness is part of the theorem's conclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace CommRingCat

/-- The objects of the category in Elkik's theorem: finite `B`-algebras whose spectrum is
étale over `Spec B` minus `V(I)`. Its full subcategory has all `B`-algebra homomorphisms.

Source: ILO, Exposé V, Theorem 1.2.4, printed p. 64
(blueprint: lem-per-elkik-finite-etale-away-completion). -/
def finiteEtaleAwayProperty (B : CommRingCat.{u}) (I : Ideal B) : ObjectProperty (Under B) :=
  fun C ↦ Module.Finite B C ∧
    Etale (Spec.map C.hom ∣_
      ⟨(PrimeSpectrum.zeroLocus (I : Set B))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (I : Set B)).isOpen_compl⟩)

/-- For a Noetherian henselian pair, tensoring with the adic completion gives an equivalence
between the categories of finite algebras étale away from the ideal and its extension.
The existential `h` asserts that the canonical tensor functor lands in the target category;
it supplies only a proof to `ObjectProperty.lift`, not an unspecified functor or map.
The last clause records the algebraization of every object of the target category.

Source: ILO, Exposé V, Theorem 1.2.4, printed p. 64 (Elkik, Théorème 5)
(blueprint: lem-per-elkik-finite-etale-away-completion).

Proof:
1. Finite module generators remain generators after tensoring. Étaleness is preserved by
   base change (`lem-weil-pbc-etale-scheme-base-change`), and the inverse image of the
   complement of V(I) is the complement of V(I B̂). This gives h. The natural comparison
   of `lem-weil-pbc-completion-finite-module-tensor` identifies this tensor product with
   completion; on pure tensors it sends a ⊗ c to a times the image of c, hence is an
   algebra isomorphism natural in C.
2. For finite algebras C₁,C₂, finite-type Noetherianity and finite-algebra integrality
   (`lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-finite-algebra-is-integral`)
   apply. The pair (C₂,IC₂) is henselian by `lem-weil-pbc-integral-over-henselian-pair`.
   Apply `lem-per-etale-away-completion-hom-lifting`: maps between the completions lift
   uniquely. Completed B-algebra maps are B̂-linear coordinatewise modulo Iⁿ, so this gives
   exactly the Hom bijections for full faithfulness of the restricted tensor functor.
3. For a target algebra E, `lem-weil-pbc-adic-completion-noetherian` and
   `lem-weil-pbc-module-completion-complete` make B̂ Noetherian and complete. Apply
   `lem-per-completed-etale-jacobian-torsion` for a completed polynomial presentation with
   power-torsion kernel and cokernel of the conormal differential. By
   `lem-weil-pbc-adic-completion-mod-power`, B/Iⁿ = B̂/IⁿB̂, so the completed polynomial
   rings over B and B̂, their derivatives, and this presentation agree.
4. `lem-per-rig-etale-jacobian-algebraization` gives a finite-type B-algebra D, étale off
   V(I), with completion E. Module completeness and finite-type Noetherianity identify
   D/ID with E/IE, finite over B/I.
5. Spec D is separated by affine-morphism permanence. Its whole closed fibre is finite,
   hence proper (`lem-per-affine-proper-finite`). Apply
   `lem-per-henselian-pair-proper-clopen-lift` to split off a proper clopen W with this
   whole closed fibre. The closed-embedding-affine lemma and affine-morphism permanence
   make W affine. Write W = Spec C. Proper and affine imply finite by
   `lem-per-affine-proper-finite`. The open inclusion and étale-composition permanence
   (`lem-weil-pbc-etale-composition-cancellation`) make C étale off V(I).
6. Since W contains the whole closed fibre, restriction identifies D/IⁿD with C/IⁿC
   for every n ≥ 1, compatibly. Their inverse limits identify E with Ĉ, and Step 1
   identifies Ĉ with B̂ ⊗ C. These maps are B̂-linear modulo every Iⁿ and therefore in
   the inverse limit. This is the last clause and essential surjectivity. Together with
   Step 2 it proves that the restricted canonical functor is an equivalence.
-/
theorem elkik_finiteEtaleAway_completion
    (B : CommRingCat.{u}) [IsNoetherianRing B] (I : Ideal B) [HenselianRing B I] :
    ∃ h : ∀ C : (finiteEtaleAwayProperty B I).FullSubcategory,
      finiteEtaleAwayProperty (.of (AdicCompletion I B))
        (I.map (algebraMap B (AdicCompletion I B)))
        ((tensorProd B (.of (AdicCompletion I B))).obj C.obj),
      ((finiteEtaleAwayProperty (.of (AdicCompletion I B))
          (I.map (algebraMap B (AdicCompletion I B)))).lift
        ((finiteEtaleAwayProperty B I).ι ⋙ tensorProd B (.of (AdicCompletion I B)))
        h).IsEquivalence ∧
      ∀ E : (finiteEtaleAwayProperty (.of (AdicCompletion I B))
          (I.map (algebraMap B (AdicCompletion I B)))).FullSubcategory,
        ∃ C : (finiteEtaleAwayProperty B I).FullSubcategory,
          Nonempty ((tensorProd B (.of (AdicCompletion I B))).obj C.obj ≅ E.obj) := by
  sorry

end CommRingCat
