/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.Paper.CartesianSectionData

/-! # Étale presentation of normalized compact support

The ordinary étale adjunction is restricted and transported to normalized
pro-étale systems before comparison with any chosen normalized right adjoint.
Source: current blueprint, `lem-coef-finite-exceptional.proof`, paragraphs 1--3;
ordinary-system descent in `prop-coef-integral-exceptional-adjoint`
(blueprint: lem-coef-normalized-support-etale-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FiniteAdjunctionDiagram

namespace WeilConjectures.CartesianSectionAdjoint

/-- A normalized restriction of the actual proper/open functor has the ordinary
étale presentation and the adjunction obtained by transporting its Hom bijections.
No normalized right adjoint or mapping-complex adjunction is assumed here.

Source: current blueprint, `lem-coef-finite-exceptional.proof`, paragraphs 1--3;
Zheng 4.10, 5.16, 5.22; ordinary-system descent, steps 1--3 of
`lem-coef-cartesian-section-adjoint-mates`
(blueprint: lem-coef-normalized-support-etale-presentation).

Proof: obtain the source and target comparison presentations from system
internal-Hom representability. Identify their sequence-site derived inverse and
right images with the comparison adjunctions in levelwise normalized adjoint
descent, using uniqueness with the same localized ordinary units. The normalized
counits are invertible: at each positive coefficient level the input is bounded
constructible of finite Tor amplitude and has étale origin; conservative exact
evaluation proves invertibility on systems. These bounds may vary with the level.
Construct the actual étale proper/open support functor by system compact-support
projection and its right adjoint by the étale coefficient-system adjoint theorem.
Free insertion identifies the latter's evaluations and quotient transitions with
the finite exceptional counit mates. Levelwise normalized descent therefore makes
its transported right image preserve the normalized finite-Tor domain. For the
small coefficient field use its universe lift and transport back along the
coefficient-ring equivalence; scalar restriction along an isomorphism is exact
and preserves all the displayed adjunction maps. Canonical proper/open comparison,
followed by the given support realization, gives the displayed left isomorphism.
Restrict the ambient adjunction to the normalized domains and transport it across
the comparison equivalences. On Hom sets this sends h first to target.R.map h,
then precomposes with the inverse left comparison, takes its ambient adjunction
transpose, applies source.P, and precomposes with the inverse source counit.
The inverse uses the inverse comparison equivalences and inverse ambient Hom
bijection. Their composites are identities by the comparison and ambient triangle
identities. Naturality of the same bijections constructs the stated adjunction
with exactly the displayed Hom action. This constructs no right adjoint by
assembling evaluated objects or by detecting equality of maps after evaluation. -/
theorem normalizedSupportEtalePresentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (S : Support l E c SX SZ SY)
    (F : (domain l E X).FullSubcategory ⥤ (domain l E Y).FullSubcategory)
    (e : F ⋙ (domain l E Y).ι ≅ (domain l E X).ι ⋙ S.functor) :
    ∃ (source : CartesianSectionData.Representability l E (X ↘ Spec (.of D.k)))
      (target : CartesianSectionData.Representability l E (Y ↘ Spec (.of D.k)))
      (support : Etale.SystemProjection.Support c (SystemInternalHom.coefficients l E))
      (right : SystemInternalHom.Et l E Y ⥤ SystemInternalHom.Et l E X)
      (adj : support.F ⊣ right)
      (left : F ⋙ (domain l E Y).ι ⋙ target.comparison.R ≅
        (domain l E X).ι ⋙ source.comparison.R ⋙ support.F)
      (counitIso : ∀ M : (domain l E X).FullSubcategory,
        IsIso (source.comparison.derivedAdjunction.counit.app M.obj))
      (preserves : ∀ N : (domain l E Y).FullSubcategory,
        domain l E X
          (source.comparison.P.obj (right.obj (target.comparison.R.obj N.obj))))
      (a : F ⊣ (domain l E X).lift
        ((domain l E Y).ι ⋙ target.comparison.R ⋙ right ⋙ source.comparison.P) preserves),
      ∀ (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory)
        (h : F.obj M ⟶ N),
        (a.homEquiv M N h).hom =
          (@inv _ _ _ _ (source.comparison.derivedAdjunction.counit.app M.obj)
            (counitIso M)) ≫
          source.comparison.P.map
            (adj.homEquiv _ _ (left.inv.app M ≫ target.comparison.R.map h.hom)) := by
  sorry

end WeilConjectures.CartesianSectionAdjoint
