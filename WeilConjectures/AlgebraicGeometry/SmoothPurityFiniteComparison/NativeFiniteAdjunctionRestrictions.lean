/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification

/-! # Native finite-coefficient adjunction restrictions

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/
sk-prop-sp-et-proet/det-sp-et-proet-adjunction-transfer.md,
comparison, compact-support restriction and Brown-restriction clauses
(blueprint: def-sp-finite-adjunction-restrictions).

These are the unchanged native helper constructions extracted from the parent comparison
module. They require no parent comparison record or adjunction-existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityFiniteComparison

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The concrete coefficient-coordinate comparison for the same compactification.
Compose the existing derived direct-image encoding with the derived exact open encoding;
no choice from a Nonempty isomorphism theorem is made.
Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-ctf-finite-foundations/sk-prop-ctf-finite-comparison/
sk-prop-sp-et-proet/det-sp-et-proet-adjunction-transfer.md, canonical compact-support
comparison (blueprint: def-sp-finite-adjunction-restrictions). -/
@[no_expose] def encodingCompactSupportComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (encX : FiniteDiscreteOrdinary.Encoding A X)
    (encZ : FiniteDiscreteOrdinary.Encoding A c.Z)
    (encY : FiniteDiscreteOrdinary.Encoding A Y) :
    CondensedRing.rightDerivedLowerShriekOfCompactification
        (FiniteDiscreteOrdinary.coefficient A) c ⋙ encY.fixedDerived.functor ≅
      encX.fixedDerived.functor ⋙ ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A c.g encY encZ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (FiniteDiscreteOrdinary.encodingDerivedOpenShriekIso A c.i encZ encX) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.SmoothPurityFiniteComparison
