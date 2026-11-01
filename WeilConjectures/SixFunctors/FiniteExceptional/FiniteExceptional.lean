/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalQuotientIso
import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalQuotientCoherence
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Finite exceptional inverse image and quotient coefficients

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-coef-finite-exceptional and its proof (blueprint: lem-coef-finite-exceptional).
All indices below are predecessors of positive exponents: index n means A_(n+1).
The functors are restrictions of the published intrinsic pro-etale constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

end WeilConjectures.FiniteExceptional

namespace WeilConjectures.FiniteExceptional

/-- Finite exceptional duality and the coherent, adjunction-normalized quotient maps.
Source: current blueprint sk-thm-sf-package, lem-coef-finite-exceptional and its proof
(blueprint: lem-coef-finite-exceptional).
Proof:
1. operations_preserve and the normalized bounded Hom chain give F_r adjoint G_r.
2. thm-fix-general-biduality and lem-sf-pullback-tor-amplitude put D_X f* D_Y in the
finite-Tor domain. Tensor closure follows from flat models and finite constructible
cohomology. Tensor-Hom transposition and H^0 of internal Hom give the Hom bijections.
3. Form the absolute trace transpose using compact-support composition and the
structure-map counit. Projection, the ordinary pullback counit and evaluation give
its exchange pairing. lem-sf-absolute-trace-exchange proves that this specified
exchange is invertible and identifies its Hom action.
4. The four Hom bijections (biduality, ordinary adjunction, exchange, biduality)
make D_X f* D_Y a right adjoint. Uniqueness of right adjoints gives the natural
first isomorphism with the already specified G, including its unit and counit.
5. Reduction preserves finite Tor by bounded flat models. Apply the coherent
Verdier coefficient comparisons to both duals and commute reduction past f*.
Contravariance uses the inverse of the inner comparison. Their cocycles and
naturality give the quotient cocycle for this comparison of the dual formulas.
6. Absolute dualizing coefficient change preserves the trace, by its counit
identity and compact-support composition. General finite Hom coefficient change
preserves evaluation. Projection and compact-support coefficient change preserve
the ordinary counit. Hence the transposed four Hom bijections give exactly inverse
q followed by reduction of the old counit. Thus their b is the mate defined above.
7. Mate pasting gives the displayed unit and counit equations. The dual comparison
makes b invertible. Its quotient cocycle descends from the two coherent dual
comparisons; equal indices give the scalar multiplication unit, with its required
endpoint identifications. All indices n denote the positive exponent n+1. -/
theorem finite_exceptional :
    (∀ n : ℕ, FormulaNormalized l E D hl f c n
      (dualFormulaIso l E D hl f c n)) ∧
    (∀ {m n : ℕ} (h : n ≤ m), IsIso (b l E D hl f c h)) ∧
    (∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
      (L : (domain l E Y m).FullSubcategory),
      (Q l E X k).map ((b l E D hl f c h).app L) ≫
          (b l E D hl f c k).app ((Q l E Y h).obj L) ≫
          (G l E D hl f c t).map ((reassoc l E Y h k).hom.app L) =
        (reassoc l E X h k).hom.app ((G l E D hl f c m).obj L) ≫
          (b l E D hl f c (k.trans h)).app L) ∧
    (∀ (n : ℕ) (L : (domain l E Y n).FullSubcategory),
      (b l E D hl f c (le_refl n)).app L ≫
          (G l E D hl f c n).map ((selfReduction l E Y n).hom.app L) =
        (selfReduction l E X n).hom.app ((G l E D hl f c n).obj L)) ∧
    (∀ {m n : ℕ} (h : n ≤ m) (K : (domain l E X m).FullSubcategory),
      (Q l E X h).map ((adjunction l E D hl f c m).unit.app K) ≫
          (b l E D hl f c h).app ((F l E D hl f c m).obj K) ≫
          (G l E D hl f c n).map ((q l E D hl f c h).hom.app K) =
        (adjunction l E D hl f c n).unit.app ((Q l E X h).obj K)) ∧
    (∀ {m n : ℕ} (h : n ≤ m) (L : (domain l E Y m).FullSubcategory),
      (q l E D hl f c h).hom.app ((G l E D hl f c m).obj L) ≫
          (F l E D hl f c n).map ((b l E D hl f c h).app L) ≫
          (adjunction l E D hl f c n).counit.app ((Q l E Y h).obj L) =
        (Q l E Y h).map ((adjunction l E D hl f c m).counit.app L)) := by
  refine ⟨?_, exceptional_quotient_isIso l E D hl f c,
    (exceptional_quotient_coherence l E D hl f c).1,
    (exceptional_quotient_coherence l E D hl f c).2, ?_, ?_⟩
  · intro n
    exact (dualFormula_existsUnique l E D hl f c n).exists.choose_spec
  · intro m n h K
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv
      ((G l E D hl f c n).mapIso ((q l E D hl f c h).app K))).mp
    simpa only [b, Functor.mapIso_inv, Iso.app_inv, Functor.id_obj, Functor.comp_obj] using
      unit_mateEquiv (adjunction l E D hl f c m)
        (adjunction l E D hl f c n) (q l E D hl f c h).inv K
  · intro m n h L
    have hc := mateEquiv_counit (adjunction l E D hl f c m)
      (adjunction l E D hl f c n) (q l E D hl f c h).inv L
    simpa only [b, Iso.app_hom] using
      (Iso.eq_inv_comp ((q l E D hl f c h).app
        ((G l E D hl f c m).obj L))).mp hc

end WeilConjectures.FiniteExceptional
