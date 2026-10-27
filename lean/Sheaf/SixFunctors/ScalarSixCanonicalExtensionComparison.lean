/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.ScalarSixCtfGenerators

/-! # Scalar change commutes with the canonical image-factorization extension.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-canonical-extension-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Scalar change commutes with the canonical image-factorization extension.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-canonical-extension-comparison).

Proof in words: give S and the image closure the induced k-structures. The immersion
into the Noetherian finite-type X makes them separated finite type and
quasi-compact. Apply scalarSixPullback, clause (2), to the induced immersion in the
over-category. Its normalized comparison uses the published section-module locally
closed extension. The internal/sectionwise equivalence carries this extension to
openImmersionLowerShriek along i.toImage followed by the closed module pushforward
along i.imageι: the coefficient action is restriction along the published adjunct,
as fixed by ScalarSixGeometry.pushNormalization. Exactness identifies its termwise
derived functor with the ordinary open derived functor followed by the closed right
derived functor. Conjugate the normalized beta comparison by these two canonical
identifications, and evaluate at Q. This gives the stated isomorphism for arbitrary
coefficient maps, without flatness or a constructibility assumption on Q. -/
theorem sfbCanonicalExtensionScalarComparison
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
    (Q : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)) :
    Nonempty ((scalarSixChange a X.left).obj
        ((sfbLocallyClosedDerivedExtension Λ i hi).obj Q) ≅
      (sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj Q)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
