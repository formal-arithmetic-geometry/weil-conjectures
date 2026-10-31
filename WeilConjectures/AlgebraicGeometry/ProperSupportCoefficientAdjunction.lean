/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Proper-image adjunctions and their coefficient counits

Source: SGA 4, XVII, §5; Bhatt--Scholze 6.7.2 and 6.7.6--6.7.7.
(blueprint: lem-zl-proper-support-coefficient-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

/-- Proper compact support has the finite rational pullback adjunctions, with
counits made compatible with the specified normalized coefficient maps
by automorphisms of their fixed right functors.
Source: SGA 4, XVII, §5; Bhatt--Scholze 6.7.2 and 6.7.6--6.7.7
(blueprint: lem-zl-proper-support-coefficient-adjunction).
Proof: use the identity-open compactification of the proper geometric-fibre map.
Its strict open extension is the identity, by its open unit. Applying system direct
image and the total right-derived limit identifies the recorded integral support
functor with the integral direct image. The reduction/limit adjunction restricts
to the complete constructible subcategories. Its pullback comparison is the
published whole-system completion-counit comparison, so the resulting adjunction
has the actual constructible integral pullback as its left functor.
Localize these coefficient-linear Hom bijections at the uniformizer; the unit and
counit are tensored with one. The object and pure-tensor normalization identifies
the resulting right functor with each prescribed finite support functor.
For a coefficient inclusion compare the counit composites before total limit.
Both are the transpose of scalar extension of the integral counit: the support
comparison is fixed by the mixed tensor unit, and pullback comparison is fixed by
its balanced-tensor map. The triangle identity and tensor-unit identity make these
transposes equal on the strict system, retaining quotient transitions. Realize,
restrict to constructible objects, and rationalize this equation. Conjugating by
the stage-transition and supplied finite-functor equalities gives precisely the
stated counit equation for the normalized adjunction. Compare the supplied
adjunction with that adjunction using right-adjoint uniqueness; both right functors
are the same, so the comparison is a natural automorphism. Transport along its
inverse to obtain exactly the normalized unit and counit. Empty schemes and repeated
coefficient fields use the same units, so no nonempty or strict-extension hypothesis is needed. -/
theorem properSupportCoefficientAdjunction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of D.k))] [IsProper p]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∀ (S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
        (Compactification.ofIsProper p))
      (L : (stageSystem l Ω Y).Morphism
        (stageSystem l Ω X)),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E)
        p) →
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : Stage l Ω Y E),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω p ⟨E, K⟩ F h)) →
      ∀ a : ∀ E, L.Φ E ⊣ S.system.Φ E,
      ∃ e : ∀ E, S.system.Φ E ≅ S.system.Φ E,
        ∀ {E F : Index l Ω} (h : E ≤ F)
          (K : Stage l Ω X E),
          (L.Φ F).map ((S.system.β h).hom.app K) ≫
            ((a F).ofNatIsoRight (e F)).counit.app (((stageSystem l Ω X).T h).obj K) =
          (L.β h).inv.app ((S.system.Φ E).obj K) ≫
            ((stageSystem l Ω X).T h).map
              (((a E).ofNatIsoRight (e E)).counit.app K) := by
  sorry

end WeilConjectures
