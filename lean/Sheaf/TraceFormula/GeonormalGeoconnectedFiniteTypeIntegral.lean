/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# Geometrically normal connected finite-type schemes are geometrically integral

Source: literature/stacks-project/properties.tex, Tag 033M, applied to finite-type
field base changes (blueprint: lem-trf-geonormal-geoconnected-finite-type-integral).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A nonempty finite-type geometrically connected scheme whose field base changes have
normal local domains is geometrically integral.

Source: Stacks Project, Tag 033M and the connected-normal component argument in Tag 057K
(blueprint: lem-trf-geonormal-geoconnected-finite-type-integral).

Proof:
1. Fix a field extension `K/k`. By `lem-sfb-finite-type-composition-base-change`, the
   projection of the base change to `Spec K` is locally of finite type and quasi-compact.
   A field is Noetherian because its ideals are zero or the unit ideal. Thus `Spec K`
   is locally Noetherian (`pqf-def-locnoeth`), and `pqf-lem-locnoeth-lft` makes the
   base change locally Noetherian. Quasi-compactness over the affine `Spec K` then
   makes it Noetherian.
2. Geometric normality gives the normal-domain condition at every stalk. Clause (2)
   of `rem-pc-regular-normal` decomposes this Noetherian scheme into finitely many
   disjoint clopen normal integral components. By geometric connectedness
   (`def-weil-connected-scheme`), it is nonempty and connected. The component of a
   chosen point and its open-and-closed complement partition the space. Connectedness
   forces the complement to be empty, so the whole base change is integral.
3. The extension was arbitrary. By `def-pc-geometrically-irreducible`, integrality
   of every field base change is precisely geometric integrality.
-/
theorem geometricallyIntegral_of_geometricallyConnected_of_geometricallyNormal
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [Nonempty X]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))]
    (hnormal : ∀ (K : Type u) [Field K] [Algebra k K],
      ∀ x : ↥(Limits.pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        IsDomain ((Limits.pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x) ∧
          IsIntegrallyClosed ((Limits.pullback (X ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x)) :
    GeometricallyIntegral (X ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry
