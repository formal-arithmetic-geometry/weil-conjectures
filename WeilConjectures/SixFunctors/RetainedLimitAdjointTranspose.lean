/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteScalarMateData
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.RamifiedScalarExceptionalLimit

/-! # Adjunction transposition through retained total limits

Source: current blueprint coefficient-extension exceptional-image proof,
sec-six-functors-basics/sk-prop-scalar-six; Stacks 0941, 079P and 07A6
(blueprint: lem-coef-retained-limit-adjoint-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteScalarMate

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

variable {l E L i D hl f c}

/-- Taking the retained total limit carries a system adjunct to the integral adjunct,
using the specified source, support-source, target and scalar identifications.
Source: normalized reconstruction adjunction calculus and the finite scalar-extension
paragraph of lem-coef-rational-operations
(blueprint: lem-coef-retained-limit-adjoint-transpose).

Proof: replace source, target, supportSource and scalarY by their normalization
formulas. Naturality of the cofinal comparison removes subsequence restriction.
Naturality of the scalar-model realization removes the lower exceptional reduction
isomorphism. The scalar-reduction normalizations are the actual reconstruction
counits, so the two adjunction triangles identify the remaining source comparison
with inverse reduction followed by the upper completion unit. Apply the upper
AdjunctionEvaluation counit equation to the system arrow q. The support-unit
normalization replaces the limit of its left evaluation by the inverse upper
completion unit. Naturality of that unit and the adjunction triangles cancel the
two units. The remaining composite is exactly F_S of the transported q followed
by epsilon_S, which is the inverse integral Hom bijection. All operations are on
whole derived-system morphisms before finite evaluations. This argument uses no
finite Tor bound beyond the constructible domains of the displayed functors and
also holds for zero arrows, identity adjunctions and empty schemes. -/
theorem retainedLimitAdjointTranspose
    (a : Context l E L i D hl f c) (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e)
    (P : RamifiedScalarExceptionalLimit.Realization a e he hp)
    (M : sfIntegralConstructibleCategory l E Y)
    (q : a.TX.obj (a.r.G.obj (a.RY.obj M)) ⟶ a.s.G.obj (a.TY.obj (a.RY.obj M))) :
    (((a.adjS.homEquiv _ _).symm
      (ObjectProperty.homMk (X := a.TIX.obj (a.GR.obj M)) (Y := a.GS.obj (a.TIY.obj M))
        (P.source.inv.app M ≫ (retainedLimit l L X e).map q.hom ≫ P.target.hom.app M))).hom) =
      P.supportSource.inv.app M ≫
        (retainedLimit l L Y e).map
          ((a.s.F.map q ≫ a.s.adjunction.counit.app (a.TY.obj (a.RY.obj M))).hom) ≫
        P.scalarY.hom.app M := by sorry

end WeilConjectures.FiniteScalarMate
