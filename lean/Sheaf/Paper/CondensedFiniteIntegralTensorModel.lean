/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.LocallyFiniteAdicRealizationData
public import Sheaf.Paper.NativeAdicEncodingCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # An integral tensor presentation of a finite condensed model

Source: Bhatt--Scholze, Proposition 6.8.14(2), with Lemma 6.8.2.
(blueprint: lem-sf-condensed-finite-integral-tensor-model).
Only one finite condensed coefficient model is considered here; no object descent
from the algebraic closure or normalized functor is part of this assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

attribute [local irreducible] sections CoefficientPresentation.integralMap

/-- A constructible complex over a finite condensed coefficient field has an integral
model whose tensor extension is its native section-module presentation.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Lemma 6.8.13 and Lemma 6.8.2.
(blueprint: lem-sf-condensed-finite-integral-tensor-model).

Proof in words: use the canonical size transport on the given finite subextension E of
PadicAlgCl; this is the same index E, with coefficient type Shrink E. Internal-module and
section-module equivalences, together with the continuous-field local-freeness theorem,
identify its bounded constructible category with the continuous rational coefficient
category. Apply finite-field continuous rational derived realization, which is essentially
surjective by the integral-lattice construction and finite Postnikov induction of
Proposition 6.8.14(2). The raw rationalization has unchanged objects, so its preimage is an
actual integral constructible complex L. The integral identity comparison transports L to
sfIntegralConstructibleCategory. Its integral tensor formula and the normalized coefficient
presentation identify its extension with the finite condensed realization. Compose with
flat extension to PadicAlgCl. The balanced tensor associator identifies that composite with
extension along C.integralMap: the associator sends b tensor (a tensor m) to ba tensor m.
Finite residue maps determine the integral coefficient map by the inverse-limit property;
the pointwise normalization determines its rational inclusion. Hence these are the given
maps of C, rather than arbitrarily chosen ring identifications.
The specified coefficient isomorphism in NativeEncoding and
the exact section-module equivalence identify the other side with the displayed inverse
encoding followed by sections. Thus the tensor associator gives the asserted isomorphism.
This uses a finite-field model as input; descent of an arbitrary algebraic-closure object
is separate. Zero complexes and the empty scheme use zero integral representatives.
-/
theorem condensedFinite_integralTensor_model
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [IsCommMonObj (abRing l X)] [(sections l X).Additive]
    [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E))
    (K : ProEtale.PadicSubfieldConstructible X l E) :
    ∃ L : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X,
      Nonempty ((pbcDerivedExtend (C.integralMap l X)).obj L.obj ≅
        (sections l X).mapDerivedCategory.obj
          ((ProEtale.NativeEncoding.derivedEncoding l X).inv.obj
            ((ProEtale.derivedExtendScalarsToPadicAlgCl X l E).obj K.obj))) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
