/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum


/-!
# The product comparison maps

Source: current blueprint `def-sf-kv-maps`, node `def-sf-kv-maps`
(blueprint: `def-sf-kv-maps`).

This module records the four canonical comparison arrows at each of the finite,
integral, rational, and common-stage coefficient systems.  The operations in a
stage are the geometric external product, compact-support direct image,
exceptional inverse image, and internal Hom supplied by the six-functor datum.
Only the compact-support Künneth arrow is required to be an isomorphism here;
the other three arrows are comparison maps whose invertibility is asserted by
the forward theorems named in the source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace WeilConjectures

/-- A single coefficient-stage package of the four product comparison arrows.

The object type is the stage's finite-Tor constructible category.  The fields
`external`, `lowerShriek`, `exceptional`, `internalHom`, and `verdierDual` are
its already supplied geometric operations.  The four arrows are respectively
`Ku_!`, `α`, `β`, and `κ`; `ku_isIso` records that the first is built from
isomorphisms, while no invertibility is imposed on the remaining arrows at the
definition stage.  Source: clauses (i)--(iv) of `def-sf-kv-maps`
(blueprint: def-sf-kv-maps). -/
structure KunnethComparisonStage (Obj : Type u) [Category.{v} Obj] where
  external : Obj → Obj → Obj
  lowerShriek : Obj → Obj
  exceptional : Obj → Obj
  internalHom : Obj → Obj → Obj
  verdierDual : Obj → Obj
  kunnethShriek : ∀ M N : Obj,
    lowerShriek (external M N) ⟶ external (lowerShriek M) (lowerShriek N)
  exceptionalKunneth : ∀ M N : Obj,
    external (exceptional M) (exceptional N) ⟶ exceptional (external M N)
  externalHom : ∀ E₁ L₁ E₂ L₂ : Obj,
    external (internalHom E₁ L₁) (internalHom E₂ L₂) ⟶
      internalHom (external E₁ E₂) (external L₁ L₂)
  kunnethVerdier : ∀ M N : Obj,
    external M (verdierDual N) ⟶ internalHom (N) (exceptional M)
  kunnethShriek_isIso : ∀ M N : Obj, IsIso (kunnethShriek M N)

/-- The four product comparison maps for the fixed six-functor datum and all
four coefficient stages.  Each field is the corresponding stage package;
the stage categories and their operations are those supplied by the datum.
The finite field is the `A_{E,n}` stage, followed by `𝒪_E`, `E`, and
`̅Q_ℓ`, exactly as in the statement of `def-sf-kv-maps`.  Source: node
`def-sf-kv-maps` (blueprint: def-sf-kv-maps). -/
structure SixFunctorKunnethMaps
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorDatum D C E n hn)
    (ObjFinite ObjIntegral ObjRational ObjCommon : Type u)
    [Category.{v} ObjFinite] [Category.{v} ObjIntegral]
    [Category.{v} ObjRational] [Category.{v} ObjCommon] where
  finite : KunnethComparisonStage ObjFinite
  integral : KunnethComparisonStage ObjIntegral
  rational : KunnethComparisonStage ObjRational
  commonStage : KunnethComparisonStage ObjCommon

end WeilConjectures
