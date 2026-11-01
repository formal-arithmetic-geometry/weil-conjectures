/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemFiniteAdjoint

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints).

Natural-number level n means exponent n+1. All morphisms are in ordinary derived
categories of strict systems, in the dependency's section-preserving coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

/-- Tower adjunction data with their actual counit/evaluation normalization.
The dependent sigma presentation avoids generating eliminators for a large record.
Source: blueprint (2), det-sp-tower-gluing (3)
(blueprint: def-sp-field-exceptional-system-adjoints). -/
def Adjoints (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) :=
  Σ (right : ∀ E : Index P, N P D E Y ⥤ N P D E X),
  Σ (adj : ∀ E : Index P, support P D c a E ⊣ right E),
  Σ (finite : ∀ (E : Index P) (n : ℕ), FiniteAdjoint P c E n),
  Σ (evaluation : ∀ (E : Index P) (n : ℕ),
    right E ⋙ level P D a E X n ≅ level P D a E Y n ⋙ (finite E n).right),
  Σ (leftEvaluation : ∀ (E : Index P) (n : ℕ),
    support P D c a E ⋙ level P D a E Y n ≅
      level P D a E X n ⋙ reductionCtfCompactSupport
        (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g (finite E n).closed),
  PLift (
(∀ (E : Index P) (n : ℕ) (M : N P D E X),
    HEq ((leftEvaluation E n).hom.app M).hom
      ((supportEvaluation P D E c n (b.supportCoordinates E n)).hom.app M.obj))
    ∧ (∀ (E : Index P) (n : ℕ),
    AdjunctionEvaluationNormalized
      (L := support P D c a E) (R := right E)
      (L' := reductionCtfCompactSupport (SpTowerShriek.R P.coefficients.l E.val n)
        c.i c.g (finite E n).closed) (R' := (finite E n).right)
      (U := level P D a E X n) (V := level P D a E Y n)
      (adj E) (finite E n).adj (leftEvaluation E n) (evaluation E n))
    ∧ (∀ (E F : Index P) (n m : ℕ)
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)),
    IsIso ((reductionDirectImageComparison φ c.i c.g).app ((finite E n).right.obj K).obj)))

/-- The specified right projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.right {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.1

/-- The specified adj projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.adj {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.2.1

/-- The specified finite projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.finite {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.2.2.1

/-- The specified evaluation projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.evaluation {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.2.2.2.1

/-- The specified leftEvaluation projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.leftEvaluation {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.2.2.2.2.1

/-- The specified counit projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.counit {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.2.2.2.2.2.down.2.1

/-- The specified finiteIso projection of the normalized exceptional adjunction data.
Source: blueprint (2), counit transpose
(blueprint: def-sp-field-exceptional-system-adjoints). -/
abbrev Adjoints.finiteIso {P : PurityFiniteSetting.{u}} {D : Models P}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {b : FieldShriekSystem.Laws P D c} {a : Domains P D c}
    (A : Adjoints P D c b a) :=
  A.2.2.2.2.2.down.2.2

end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
