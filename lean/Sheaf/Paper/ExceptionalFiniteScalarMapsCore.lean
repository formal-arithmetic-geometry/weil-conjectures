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

/-- The finite scalar maps apart from the ambient etale mate package.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps-core).

This is the finite-subcategory part of the scalar-mate construction.  It records the
left and right comparison isomorphisms, their normalization and counit equation, and
their shift compatibilities.  The ambient etale mate package is supplied separately.
-/
structure FiniteScalarMapsCore
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) where
  q : source.F ⋙ scalarY.functor ≅ scalarX.functor ⋙ target.F
  b : source.G ⋙ scalarX.functor ≅ scalarY.functor ⋙ target.G
  q_normalized (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X) :
    ((finiteTorConstructible l L (m + 1) (Nat.succ_pos m) Y).ι).map (q.hom.app K) ≫
        target.left.hom.app ((scalarX.functor).obj K) =
      (pbcDerivedExtend (proEtaleConstantRingMap (T := Y) a)).map (source.left.hom.app K) ≫
        (leftScalarMap a c).app K.obj
  counit (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y) :
    q.hom.app (source.G.obj N) ≫ target.F.map (b.hom.app N) ≫
        target.adjunction.counit.app ((scalarY.functor).obj N) =
      (scalarY.functor).map (source.adjunction.counit.app N)
  qShift : q.hom.CommShift ℤ
  bShift : b.hom.CommShift ℤ

/-- The finite-subcategory scalar-mate core exists.
Source: Zheng, Construction 2.26 and Proposition 2.29; Stacks 0GL6, 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-maps-core).

The proof is the proper/open scalar comparison transported through the two finite-Tor
full subcategories.  The ambient comparison is invertible by the proper coefficient
extension theorem and etale compact scalar coherence; the finite operation
realizations and full faithfulness give the displayed normalization and counit
identities, while the chosen derived shifts transport the two shift equations.
-/
theorem finiteScalarMapsCore_exists
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
    (c : Compactification f)
    (scalarX : Scalar l E L n m a X) (scalarY : Scalar l E L n m a Y)
    (source : Operation l E n c) (target : Operation l L m c) :
    Nonempty (FiniteScalarMapsCore l E L n m a c scalarX scalarY source target) := by
  sorry

end WeilConjectures.ExceptionalFiniteScalar
