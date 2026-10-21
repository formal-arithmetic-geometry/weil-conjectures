/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Constant scalar encoding preserves the ambient pro-etale exchange

Source: Stacks Tag 07A7, with constant-module encoding Tags 093I and 03CY.
(blueprint: lem-pe-constant-exchange-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Exact constant-section restriction identifies the ringed and fixed-scalar mates.
No properness, torsion, classicality or boundedness assumption enters this comparison.
Source: Stacks Tag 07A7, and blueprint sk-thm-properbasechange, module and pro-etale
comparison paragraphs (blueprint: lem-pe-constant-exchange-encoding).
Proof: on module sheaves, restricting the scalar action along constant sections gives
an exact equivalence. Direct image in both encodings evaluates on the same base-changed
object, and the constant-section equation identifies its scalar action. Conjugate this
comparison through the normalized pullback/direct-image adjunctions to obtain the
pullback comparison. The sectionwise composition comparisons on direct images agree;
conjugation therefore identifies the two pullback squares. Apply the equivalences to
complexes. Exactness computes pullback termwise; equivalences transport K-injectives,
so the direct-image comparisons derive to isomorphisms. Their unit and counit equations
are preserved by derived adjunction. The normalized termwise characterization of the
ambient pullback comparison identifies it with this derived square. Expanding both mates
as unit, square and counit gives three commuting comparison squares. Compose them to
obtain the asserted arrow isomorphism.
-/
theorem proEtaleConstantExchange_encoding (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (hc : HEq
      (proEtaleRingCompositeCoefficients g' f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g' A))
      (proEtaleRingCompositeCoefficients f' g
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y' A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison f' A)))
    (K : proEtaleDerivedCategory X A) :
    Nonempty (Arrow.mk ((proEtaleDerivedModuleRestriction Y' A).map
      ((proEtaleAmbientRingedExchange sq
        (proEtaleConstantRing X A) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A) (proEtaleConstantRing Y' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison g A)
        (proEtaleConstantRingComparison g' A) (proEtaleConstantRingComparison f' A) hc).app K)) ≅
      Arrow.mk ((ProEtale.derivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app
          ((proEtaleDerivedModuleRestriction X A).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
