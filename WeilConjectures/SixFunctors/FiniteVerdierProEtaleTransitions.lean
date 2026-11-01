/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
import WeilConjectures.SixFunctors.Supporting.ClosedScalarDomains
import all WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginComparisonCoherence

/-! # The fixed pro-etale scalar domain and dualizing transitions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]

include hl in
/-- Scalar extension on the fixed module pro-etale site preserves the finite-Tor
constructible domain, and the comparison-pullback dualizing transitions are invertible
and satisfy the scalar identity and composition laws.

Source: cor-coef-finite-verdier.proof.md, site-comparison sentence;
Stacks 06YY and 0G7E (blueprint: lem-coef-verdier-proetale-transitions).

Proof: choose the Tor interval contained in the input's finite-Tor condition and apply
closedScalarDomains_scalar at the quotient coefficient map, retaining its first clause.
For the targets, comparison reduction is an isomorphism and comparison pullback preserves
the already proved etale dualizing isomorphism. The scalar/site mate has its identity
and composition laws by transposition of the corresponding restriction-of-scalars laws.
Substitute the etale dualizing identity. For composition, move the etale transition
through the natural comparison mate, substitute the etale cocycle, and cancel the
inverse mates in the scalar/site composition law. The argument includes equal levels
and zero objects and uses no flatness of the quotient ring. -/
theorem finiteVerdier_proEtale_transitions :
    let R := finiteDualizingCoeff l E
    let U := fun n ↦ (comparisonUpperStar (ModuleCat.{u + 1} (R n)) X).mapDerivedCategory
    let W := finiteDualizingEtaleTerm l E D X
    let S := fun {n m : ℕ} (h : m ≤ n) ↦
      pbcFixedScalarExtension (Scheme.ProEt.topology X) (finiteDualizingQuotient l E h)
    let uMap := fun {n m : ℕ} (h : m ≤ n) ↦
      (pbcComparisonReduction X (finiteDualizingQuotient l E h)).hom.app (W n) ≫
        (U m).map (finiteDualizingEtaleComparison l E D X h)
    (∀ {n m : ℕ} (h : m ≤ n) K,
      finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X ((S h).obj K)) ∧
    (∀ {n m : ℕ} (h : m ≤ n), IsIso (uMap h)) ∧
    (∀ n, uMap (le_refl n) =
      (normalizedOriginScalarUnit (Scheme.ProEt.topology X) _
        (finiteDualizingQuotient_id l E n)).hom.app ((U n).obj (W n))) ∧
    (∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      (S g).map (uMap h) ≫ uMap g =
        (pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) _ _ _
          (finiteDualizingQuotient_comp l E h g)).hom.app ((U n).obj (W n)) ≫
            uMap (g.trans h)) := by
  dsimp only
  have hu := finiteDualizingCoefficientComparisons l E D X hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m h K hK
    obtain ⟨a, b, ht⟩ := hK.2
    let T : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
    let : IsSeparated T.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of D.k)))
    let : LocallyOfFiniteType T.hom :=
      inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
    let : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
    exact (closedScalarDomains_scalar D l hl E E n m
      (finiteDualizingQuotientBase l E h) T
      a b ht.1 K hK ht).1.1
  · intro n m h
    have := (hu.1 h).2.1
    infer_instance
  · intro n
    rw [hu.2.1]
    rw [AlgebraicGeometry.ProEtale.comparisonScalarUnit X _
      (finiteDualizingQuotient_id l E n)]
    simp only [Iso.hom_inv_id_app_assoc]
  · intro n m r h g
    let φ := finiteDualizingQuotient l E h
    let ψ := finiteDualizingQuotient l E g
    let χ := finiteDualizingQuotient l E (g.trans h)
    let W := finiteDualizingEtaleTerm l E D X
    let U := (comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E r))
      X).mapDerivedCategory
    let G := pbcFixedScalarExtension (Scheme.ProEt.topology X) ψ
    let β := pbcComparisonReduction X φ
    let γ := pbcComparisonReduction X ψ
    let ζ := pbcComparisonReduction X χ
    let α := pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ
      (finiteDualizingQuotient_comp l E h g)
    let α' := pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ χ
      (finiteDualizingQuotient_comp l E h g)
    have hc := AlgebraicGeometry.ProEtale.comparisonScalarComp X φ ψ χ
      (finiteDualizingQuotient_comp l E h g) (W n)
    change U.map (α.hom.app (W n)) ≫ ζ.inv.app (W n) =
      γ.inv.app ((Etale.scalarExtension φ X).obj (W n)) ≫
        G.map (β.inv.app (W n)) ≫ α'.hom.app _ at hc
    have hc' : G.map (β.hom.app (W n)) ≫
        γ.hom.app ((Etale.scalarExtension φ X).obj (W n)) ≫ U.map (α.hom.app (W n)) =
        α'.hom.app _ ≫ ζ.hom.app (W n) := by
      apply (cancel_mono (ζ.inv.app (W n))).mp
      rw [Category.assoc, Category.assoc, hc]
      simp only [← G.map_comp_assoc, Iso.hom_inv_id_app, G.map_id,
        Category.id_comp, Iso.hom_inv_id_app_assoc, Category.assoc]
      simpa only [Functor.comp_obj] using (Category.comp_id (α'.hom.app _)).symm
    simp only [Functor.map_comp, Category.assoc]
    have hn := γ.hom.naturality (finiteDualizingEtaleComparison l E D X h)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← U.map_comp, hu.2.2.1 h g, U.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ U.map (finiteDualizingEtaleComparison l E D X (g.trans h))) hc'


end WeilConjectures
