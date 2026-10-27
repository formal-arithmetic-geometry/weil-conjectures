/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalFiniteScalarMatesData

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The ambient etale scalar-mate package exists for a finite coefficient map.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps-etale).

This statement isolates the ordinary etale part of the construction: the proper/open
comparison, its adjoint mate, projection normalization, and shift compatibility.
It is strictly smaller than `ConstructionMaps`, whose remaining finite-subcategory
maps are supplied by `FiniteScalarMapsCore`.
-/
theorem finiteScalarMapsEtale_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    Nonempty (EtaleMates (RingHom.ulift.{u + 1, u + 1} a) c) := by
  sorry

end WeilConjectures.ExceptionalFiniteScalar
