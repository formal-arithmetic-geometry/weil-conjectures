/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarOperation
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalar
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMaps

/-!
# Finite scalar mates for the exceptional adjunction

## Implementation details

The proof of `WeilConjectures.ExceptionalFiniteScalar.exceptionalFiniteScalarMates` proceeds in
eight steps.

1. On the ordinary étale categories, a constructible `K` of Tor interval `[u, v]` over `A` has a
   flat constructible model `P` supported in `[u, v]` (as `T` is of finite type over `k`). It is
   K-flat, so `K ⊗^L_A B` is computed by `P ⊗_A B`, whose terms are flat over `B` and
   constructible; hence the Tor interval `[u, v]` is kept over `B`, even for a nonflat `A → B`.
2. The comparison inverse image and the derived pullback/tensor identification carry this back
   to the pro-étale category. The scalar functor on the full subcategories is defined by the
   ambient scalar extension, so its realization is an equality; exactness and shifts are
   inherited from derived change of rings.
3. On the étale derived categories, the left map `q^e_a` is the proper coefficient comparison at
   `j_!` followed by the direct image of the open scalar tensor map; the compact scalar coherence
   theorem makes it invertible for any finite `A → B`.
4. With `U` the restriction of scalars, the scalar adjunction, the two exceptional adjunctions
   and `q^e_a` give, by Yoneda, a canonical isomorphism `U G^e_B N ≅ G^e_A U N`, the transpose of
   `F^e_A U G^e_B N ≅ U F^e_B G^e_B N ⟶ U N`.
5. The right map `b^e_a` is the transpose of `S F^e_A G^e_A L ⟶ S L` precomposed with
   `(q^e_a)⁻¹`. After restriction of scalars it is the exceptional constant-`B` tensor map, which
   is invertible; restriction detects quasi-isomorphisms, so `b^e_a` is invertible.
6. The finite-operations theorem supplies the constructible restrictions of the functors, their
   adjunction and their shifts; steps 1–2 show that all endpoints lie in the full categories, and
   `q^e`, `b^e` are transported along the site comparison, giving the counit equation.
7. Expanding the compact-support site comparison into its proper and open factors shows that the
   transported `q` is exactly the pro-étale proper scalar mate followed by the open tensor map,
   so `b` is its normalized transpose.
8. The shift equations follow from the shift compatibility of derived change of rings, of the
   pullback/tensor comparison, of the projection maps and of the open balancing map; for `b` the
   two sides of the shift equation have the same transpose.

## References

* [Zheng, Propositions 2.23, 2.29 and 3.16, Construction 2.26]
* [Stacks, Tag 0GL6]
* [Stacks, Tag 09AL]
* [Stacks, Tag 09B1]
* [Stacks, Tag 07A4]
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- Finite scalar extension preserves the actual constructible finite-Tor categories
and their Tor intervals, with literal restrictions and the canonical scalar mates.
Quotient, ramified, identity and composite unital maps are all quantified directly. -/
theorem exceptionalFiniteScalarMates
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
    (c : Compactification f) : Nonempty (Construction l E L n m a c) := by
  classical
  obtain ⟨source⟩ := finiteScalarOperation_exists D l _hl E n f c
  obtain ⟨target⟩ := finiteScalarOperation_exists D l _hl L m f c
  obtain ⟨scalarX⟩ := finiteScalar_exists D l _hl E L n m a X
  obtain ⟨scalarY⟩ := finiteScalar_exists D l _hl E L n m a Y
  obtain ⟨maps⟩ :=
    finiteScalarMaps_exists D l _hl E L n m a f c scalarX scalarY source target
  exact ⟨{
    scalarX := scalarX
    scalarY := scalarY
    source := source
    target := target
    q := maps.q
    b := maps.b
    q_normalized := maps.q_normalized
    counit := maps.counit
    qShift := maps.qShift
    bShift := maps.bShift
    etale := maps.etale
  }⟩

end WeilConjectures.ExceptionalFiniteScalar
