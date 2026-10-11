/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Sheaf.AlgebraicGeometry.MeromorphicModule

/-!
# Meromorphic sections and generic-point products

Source: Stacks Project, Divisors, Tag 0EMH (divisors-lemma-quasi-coherent-K).
(blueprint: lem-sc-meromorphic-sheaf-generic-product).

The stalk identifications are normalized on ordinary sections. Multiplication of meromorphic
sections is characterized by the local fraction formula, so the final clause concerns the
canonical meromorphic action, not an arbitrary action transported from a product.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The canonical generic-stalk identifications give bijections on sections, compatible with
restriction and multiplication. Source: Stacks, Tag 0EMH, with the generic-stalk computation
in Tag 0EMF (blueprint: lem-sc-meromorphic-sheaf-generic-product).

Proof: (1) By lem-sc-ass-weakass-locally-noetherian, no embedded associated points means
that all weakly associated points are generic. A quasi-compact open has a finite affine
Noetherian cover; lem-weil-pbc-noetherian-open-subscheme-noetherian and
lem-sc-noetherian-finite-irreducible-components give finitely many components. Apply
lem-sc-meromorphic-weakass-generic-product (Tag 0EMF).
(2) A generic local ring has dimension zero and is Artinian. Every nonunit is nilpotent,
hence a zero-divisor, so localization at non-zero-divisors fixes it. Sheafification preserves
stalks and localization commutes with their filtered colimits. Evaluating the product on U
retains exactly the generic points in U, and the comparison is the germ map.
(3) For invertible L, the same product theorem gives the module comparison. Stalks commute
with tensor products (Modules Tag 01CE), yielding K(L)_η = O_η tensor L_η = L_η.
The stalk action rule of def-weil-pbc-module-stalk sends a product to the product of germs;
the fraction rule (a/b)(m/c) = (am)/(bc) and the germ restriction rule give the two
compatibilities below. The recorded meromorphicModule_tensor_iso identifies the localized
module used here with K_X tensor L. -/
theorem meromorphicSheaf_generic_product
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h_no_embedded : ∀ x : X,
      (∃ a : X.presheaf.stalk x, IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        (⊥ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)).colon {a}) →
      x ∈ genericPoints X)
    (L : X.Modules) [L.IsInvertible] :
    letI (x : X) : Module (X.presheaf.stalk x) (L.presheaf.stalk x) :=
      inferInstanceAs (Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x))
    ∃ (eK : ∀ η : {x : X // x ∈ genericPoints X},
        (meromorphicModule X (unit X)).presheaf.stalk η.val ≃+ X.presheaf.stalk η.val)
      (eL : ∀ η : {x : X // x ∈ genericPoints X},
        (meromorphicModule X L).presheaf.stalk η.val ≃+ L.presheaf.stalk η.val)
      (mul : ∀ U : X.Opens, Γ(meromorphicModule X (unit X), U) →
        Γ(meromorphicModule X L, U) → Γ(meromorphicModule X L, U)),
      (∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
        (a : Γ(X, U)),
        eK η ((meromorphicModule X (unit X)).presheaf.germ U η.val hη
          ((toMeromorphicModule X (unit X)).val.app (op U) a)) =
            X.presheaf.germ U η.val hη a) ∧
      (∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
        (m : Γ(L, U)),
        eL η ((meromorphicModule X L).presheaf.germ U η.val hη
          ((toMeromorphicModule X L).val.app (op U) m)) = L.presheaf.germ U η.val hη m) ∧
      (∀ U : X.Opens, Function.Bijective
        (fun s : Γ(meromorphicModule X (unit X), U) ↦
          fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
            eK ⟨η.val, η.property.1⟩
              ((meromorphicModule X (unit X)).presheaf.germ U η.val η.property.2 s))) ∧
      (∀ U : X.Opens, Function.Bijective
        (fun t : Γ(meromorphicModule X L, U) ↦
          fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
            eL ⟨η.val, η.property.1⟩
              ((meromorphicModule X L).presheaf.germ U η.val η.property.2 t))) ∧
      (∀ (U V : X.Opens) (i : V ⟶ U) (η : {x : X // x ∈ genericPoints X})
        (hV : η.val ∈ V) (hU : η.val ∈ U) (s : Γ(meromorphicModule X (unit X), U))
        (t : Γ(meromorphicModule X L, U)),
        eK η ((meromorphicModule X (unit X)).presheaf.germ V η.val hV
            ((meromorphicModule X (unit X)).presheaf.map i.op s)) =
          eK η ((meromorphicModule X (unit X)).presheaf.germ U η.val hU s) ∧
        eL η ((meromorphicModule X L).presheaf.germ V η.val hV
            ((meromorphicModule X L).presheaf.map i.op t)) =
          eL η ((meromorphicModule X L).presheaf.germ U η.val hU t)) ∧
      (∀ (U : X.Opens) (a : Γ(X, U)) (m : Γ(L, U))
        (b c : meromorphicDenominators X U),
        mul U (meromorphicFraction X (unit X) U (LocalizedModule.mk a b))
          (meromorphicFraction X L U (LocalizedModule.mk m c)) =
            meromorphicFraction X L U (LocalizedModule.mk (a • m) (b * c))) ∧
      (∀ (U V : X.Opens) (i : V ⟶ U) (s : Γ(meromorphicModule X (unit X), U))
        (t : Γ(meromorphicModule X L, U)),
        (meromorphicModule X L).presheaf.map i.op (mul U s t) =
          mul V ((meromorphicModule X (unit X)).presheaf.map i.op s)
            ((meromorphicModule X L).presheaf.map i.op t)) ∧
      (∀ (U : X.Opens) (η : {x : X // x ∈ genericPoints X}) (hη : η.val ∈ U)
        (s : Γ(meromorphicModule X (unit X), U)) (t : Γ(meromorphicModule X L, U)),
        eL η ((meromorphicModule X L).presheaf.germ U η.val hη (mul U s t)) =
          eK η ((meromorphicModule X (unit X)).presheaf.germ U η.val hη s) •
            eL η ((meromorphicModule X L).presheaf.germ U η.val hη t)) := by
  sorry

end AlgebraicGeometry
