/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.RationalFunctionRing
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Rational functions and generic stalks

Source: Stacks Project, Morphisms, Lemma 01RV, first and third assertions
(blueprint: lem-sc-rational-functions-generic-stalks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- For a scheme with finitely many irreducible components, every dense open contains their
 generic points, and taking germs identifies rational functions with the product of the generic
 stalks. For an integral scheme there is one component, the whole space, and both the rational
 function ring and the generic stalk are fields. Source: Stacks Project, Lemma 01RV, first and
 third assertions (blueprint: lem-sc-rational-functions-generic-stalks).

Proof (the six steps of the node):
1. By `lem-sc-irreducible-components-cover` the components cover `X`. Remove all components
   other than the i-th to obtain a nonempty open `V_i` containing its generic point. Maximality
   of components makes these opens pairwise disjoint. An open meets a component exactly when
   it contains its generic point (`def-sc-generic-point`, `lem-sc-scheme-sober`).
2. A dense open meets each `V_i`, hence contains every generic point. Conversely an open
   containing all generic points is dense, because their closures cover `X`.
3. Germ maps respect restriction, addition and multiplication. They therefore induce a
   well-defined ring map on the colimit `def-sc-rational-functions`, with the displayed values
   on its coprojections (`def-weil-pbc-module-stalk`).
4. A section with all generic germs zero vanishes on smaller neighborhoods inside the `V_i`.
   Their disjoint union is dense, and sheaf locality makes the section zero there, proving
   injectivity (`def-pc-scheme`, `def-weil-pbc-module-stalk`, `def-sc-rational-functions`).
5. Represent each prescribed germ on a neighborhood inside `V_i`. Sheaf gluing on their
   disjoint dense union supplies a rational function with those germs, proving surjectivity
   (the same three nodes).
6. For an integral scheme, irreducibility makes `X` its only component. The generic stalk
   is a field by `lem-sc-integral-function-field-affine-fraction`, using a nonempty affine open
   and Algebra Lemma 00EU. The germ isomorphism transports this property to rational functions
   (`def-pc-integral-scheme`, `def-weil-irreducible-components`, `def-pc-scheme`). -/
theorem rationalFunctions_generic_stalks (X : Scheme.{u}) (n : ℕ)
    (components : Fin n ≃ {Z : Set X // Z ∈ irreducibleComponents X})
    (η : Fin n → X) (hη : ∀ i : Fin n, IsGenericPoint (η i) (components i).val) :
    ∃ hDense : ∀ (U : DenseOpens X) (i : Fin n), η i ∈ U.val,
      ∃ e : (X.rationalFunctionRing : Type u) ≃+* ((i : Fin n) → X.presheaf.stalk (η i)),
        (∀ (U : DenseOpens X) (f : Γ(X, U.val)) (i : Fin n),
          e ((colimit.ι (denseOpenSections X) (op U)) f) i =
            X.presheaf.germ U.val (η i) (hDense U i) f) ∧
        (IsIntegral X → n = 1 ∧ (∀ i : Fin n, (components i).val = Set.univ) ∧
          IsField (X.rationalFunctionRing : Type u) ∧
          ∀ i : Fin n, IsField (X.presheaf.stalk (η i)) ∧
            ∃ ei : (X.rationalFunctionRing : Type u) ≃+* X.presheaf.stalk (η i),
              ∀ r : X.rationalFunctionRing, ei r = e r i) := by
  sorry

end AlgebraicGeometry.Scheme
