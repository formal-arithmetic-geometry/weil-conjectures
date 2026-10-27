/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels

import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.IntegralOperationsPreserveConstructible

/-! # Rationalization of one integral Verdier duality

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-datum). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Integral duality rationalizes to a normalized datum over one coefficient field.
Source: thm-coef-rational-verdier, proof steps 1--5; current blueprint proof,
paragraphs 1--2 (blueprint: lem-coef-rational-verdier-datum).

Proof: use integral_residue_tor to put every integral constructible object in the
finite-Tor domain. Integral Verdier duality for w.omega and w.reduction supplies
preservation, the ordinary tensor presentation, signed symmetry, exactness and
invertible evaluation-defined delta. Internal Hom precomposition is linear in
its first variable. Extend its linear Hom maps by tensoring with the localized
coefficient ring; balancing, identities and reversed composition are checked on
pure tensors and extended by additivity. The unchanged-object raw localization
of the opposite category is its opposite. Localize the integral shift comparison;
every rational distinguished triangle is isomorphic to a localized integral one,
so its image is distinguished. Tensor the inverse integral Hom maps to obtain
full faithfulness. Localized delta gives essential surjectivity and natural
biduality; naturality on a pure tensor is integral naturality multiplied by its
coefficient. For evaluation, descend the quotient-normalized completion chain
map to the ordinary presentation, using uniqueness of derived representatives.
constructibleTensorCompletion makes this map invertible on constructible pairs.
Compose its inverse with ordinary evaluation and localize. Integral evaluation
naturality and naturality of completion give the required rational evaluation
identity on pure tensors; additivity gives it for all morphisms. The dualizing
object is exactly the localization of w.omega. This treats zero and torsion
objects, the empty scheme and the ground coefficient field without exceptions.
The signed symmetry is taken natural in both variables: the Koszul swap of total
tensor complexes is natural in chain maps, so its transport along the representative
isomorphism is natural on K-flat objects for all derived maps (a derived map between
K-flat objects is a roof through a K-flat resolution), and every derived object is
isomorphic to a K-flat representative. SignedSymmetry alone pins the swap only on
literal K-flat pairs, while delta uses it at the pair (RHom(K, omega), K). -/
theorem datum_exists
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E) :
    ∃ A : Datum D l hl X E wE,
      ∀ (K L K' L' : IntegralHom.Derived.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X))
        (f : K ⟶ K') (g : L ⟶ L'),
        A.ordinary.tensor.map (Prod.mkHom f g) ≫ (A.symmetry.swap K' L').hom =
          (A.symmetry.swap K L).hom ≫ A.ordinary.tensor.map (Prod.mkHom g f) := by sorry

end WeilConjectures.RationalVerdier
