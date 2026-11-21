/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsCore
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMapsEtale

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The normalized scalar mates exist once the finite operation and scalar packages exist.

The statement packages the canonical proper/open comparison, its counit transpose,
the two shift compatibilities, and the ordinary-etale mate data. It is strictly
smaller than `Construction`, since the scalar and operation packages are inputs. -/
theorem finiteScalarMaps_exists
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
    Nonempty (ConstructionMaps l E L n m a c scalarX scalarY source target) := by
  obtain ⟨core⟩ :=
    finiteScalarMapsCore_exists D l _hl E L n m a f c scalarX scalarY source target
  obtain ⟨etale⟩ := finiteScalarMapsEtale_exists D l _hl E L n m a f c
  exact ⟨{
    q := core.q
    b := core.b
    q_normalized := core.q_normalized
    counit := core.counit
    qShift := core.qShift
    bShift := core.bShift
    etale := etale
  }⟩

end WeilConjectures.ExceptionalFiniteScalar
