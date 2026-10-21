/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.ProjectionMateExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Quotient coefficient presentations

Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation).

## Main definitions

`QuotientAt` specifies the quotient coefficient and its exact derived restriction.
`quotientCorner` and `forgetQuotient` are the resulting ringed site and scalar functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.proofsInPublic true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w uData vData wData xData yData zData

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

/-- The type of binary endofunctors, abstracting the ambient category.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def binaryEndofunctorType (C : Type uData) [Category.{vData} C] := C × C ⥤ C

/-- The type of a derived tensor model over the quotient ring.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientTensorType (A : RingedTensorCorner.{u, w})
    (ring : Sheaf A.topology CommRingCat.{u})
    [derived : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))] :=
  binaryEndofunctorType (@DerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))
      inferInstance inferInstance derived)

/-- Abstract data for a quotient coefficient presentation.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation). -/
structure QuotientAtData (R : Type uData) (M : R → Type vData)
    (S : (r : R) → M r → Prop) (D : R → Type wData)
    (T : (r : R) → D r → Type xData)
    (L C : (r : R) → M r → Prop) (E : (r : R) → M r → Type yData) where
  ring : R
  map : M ring
  surjective : S ring map
  derived : D ring
  tensor : T ring derived
  exactLimits : L ring map
  exactColimits : C ring map
  coefficient : E ring map

/-- Exactness of quotient restriction on finite limits.
Source: Stacks 03EL
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientExactLimits (A : RingedTensorCorner.{u, w})
    (ring : Sheaf A.topology CommRingCat.{u}) (m : A.ring ⟶ ring) : Prop :=
  PreservesFiniteLimits (restrictScalars.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).map m))

/-- Exactness of quotient restriction on finite colimits.
Source: Stacks 03EL
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientExactColimits (A : RingedTensorCorner.{u, w})
    (ring : Sheaf A.topology CommRingCat.{u}) (m : A.ring ⟶ ring) : Prop :=
  PreservesFiniteColimits (restrictScalars.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).map m))

/-- Identification with the quotient unit in degree zero.
Source: Stacks 03EL
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientCoefficientType (A : RingedTensorCorner.{u, w})
    (Q : CochainComplex A.mateModules ℤ) (ring : Sheaf A.topology CommRingCat.{u})
    (m : A.ring ⟶ ring) :=
  Q ≅ (CochainComplex.singleFunctor A.mateModules 0).obj
    ((restrictScalars.{u} ((sheafCompose A.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).map m)).obj
      (unit ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring)))

/-- The type of a chosen derived category for the quotient module category.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientDerivedType (A : RingedTensorCorner.{u, w})
    (ring : Sheaf A.topology CommRingCat.{u}) :=
  HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj ring))

/-- The local surjectivity predicate for a quotient ring map.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientSurjective (A : RingedTensorCorner.{u, w})
    (ring : Sheaf A.topology CommRingCat.{u}) (m : A.ring ⟶ ring) : Prop :=
  Presheaf.IsLocallySurjective A.topology m.hom

/-- A quotient ring, local surjectivity, derived model, exact restriction and coefficient unit.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-coefficient-presentation). -/
abbrev QuotientAt (A : RingedTensorCorner.{u, w})
    (Q : CochainComplex A.mateModules ℤ) :=
  QuotientAtData (Sheaf A.topology CommRingCat.{u}) (fun ring ↦ A.ring ⟶ ring)
    (quotientSurjective A)
    (quotientDerivedType A)
    (fun ring d ↦ @quotientTensorType A ring d)
    (quotientExactLimits A) (quotientExactColimits A) (quotientCoefficientType A Q)

/-- The specified derived category of quotient modules.
Source: Stacks 03EL
(blueprint: def-sbc-quotient-coefficient-presentation). -/
abbrev QuotientAt.derived {A : RingedTensorCorner.{u, w}}
    {Q : CochainComplex A.mateModules ℤ} (q : QuotientAt A Q) :
    HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj q.ring)) :=
  QuotientAtData.derived q

/-- The specified finite-limit exactness of quotient restriction.
Source: Stacks 03EL
(blueprint: def-sbc-quotient-coefficient-presentation). -/
abbrev QuotientAt.exactLimits {A : RingedTensorCorner.{u, w}}
    {Q : CochainComplex A.mateModules ℤ} (q : QuotientAt A Q) :
    PreservesFiniteLimits (restrictScalars.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).map q.map)) :=
  QuotientAtData.exactLimits q

/-- The specified finite-colimit exactness of quotient restriction.
Source: Stacks 03EL
(blueprint: def-sbc-quotient-coefficient-presentation). -/
abbrev QuotientAt.exactColimits {A : RingedTensorCorner.{u, w}}
    {Q : CochainComplex A.mateModules ℤ} (q : QuotientAt A Q) :
    PreservesFiniteColimits (restrictScalars.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).map q.map)) :=
  QuotientAtData.exactColimits q


/-- The quotient ringed site on the original underlying site.
Source: Stacks 03EL (blueprint: def-sbc-quotient-coefficient-presentation). -/
def quotientCorner {A : RingedTensorCorner.{u, w}}
    {Q : CochainComplex A.mateModules ℤ} (q : QuotientAt A Q) : RingedTensorCorner.{u, w} where
  site := A.site
  topology := A.topology
  ring := q.ring
  derived := QuotientAtData.derived q
  tensor := q.tensor

/-- Actual derived restriction of scalars along the quotient ring map.
Source: Stacks 03EL (blueprint: def-sbc-quotient-coefficient-presentation). -/
def forgetQuotient {A : RingedTensorCorner.{u, w}}
    {Q : CochainComplex A.mateModules ℤ} (q : QuotientAt A Q) :
    (quotientCorner q).mateDerived ⥤ A.mateDerived :=
  @Functor.mapDerivedCategory
    (quotientCorner q).mateModules inferInstance inferInstance (QuotientAtData.derived q)
    A.mateModules inferInstance inferInstance A.derived
    (restrictScalars.{u}
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).map q.map))
    inferInstance (QuotientAt.exactLimits q) (QuotientAt.exactColimits q)


end SheafOfModules.StrictQuotientExchange
