/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.VerdierExchangeData
public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! # Native finite-field-coefficient Verdier dualizing data

Source: latest blueprint fix-cor-verdier-exchange.proof.md, Step 1, and
its construction interface (blueprint: def-sf-verdier-exchange-data).

The complete recorded stage, scalar and shift data remain publicly exported.
This additive specialization supplies the actual finite-E dualizing object and
right-adjoint composition comparison on the ordinary condensed module categories.
The exchange arrow itself is the existing `CategoryTheory.Verdier.absoluteExchange`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.NormalizedClosedExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The finite-extension-coefficient dualizing complex, with coefficient unit at Spec k.
The coefficient sheaf is the structural pullback of the ordinary condensed ring E.
Source: latest blueprint fix-cor-verdier-exchange.md, definition of omega.
(blueprint: def-sf-verdier-exchange-data). -/
def finiteDualizingComplex (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    Dᵇc(T.left)⟦Profinite.continuousMapRingObj E⟧ :=
  (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E
    (Over.mkIdTerminal.from T)).obj (𝟙_ _)

/-- The finite-extension dualizing comparison is the right-adjoint mate of the
compact-support compositor at the coefficient unit, transported along f a_Y = a_X.
Source: latest blueprint fix-cor-verdier-exchange.proof.md, Step 1.
(blueprint: def-sf-verdier-exchange-data). -/
def finiteDualizingComparison (f : X ⟶ Y) :
    (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f).obj
      (finiteDualizingComplex ℓ E Y) ≅ finiteDualizingComplex ℓ E X :=
  ((boundedConstructibleUpperShriekComp ℓ E f (Over.mkIdTerminal.from Y)).app
    (𝟙_ _)).symm ≪≫
    eqToIso (congrArg
      (fun g : X ⟶ Over.mk (𝟙 (Spec (.of k))) ↦
        (ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E g).obj (𝟙_ _))
      (Over.mkIdTerminal.comp_from f))

end AlgebraicGeometry.ProEtale.CondensedRing.NormalizedClosedExchange
