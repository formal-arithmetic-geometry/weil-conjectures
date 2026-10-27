/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Paper.ClassicalWeilFiltrationTransportData
import Sheaf.Paper.ClassicalFiltrationExactDiagram
import Sheaf.Paper.ClassicalFiltrationDiagramFibres
import Sheaf.Paper.ClassicalRealizationPunctualPurity

/-! # Classical Weil filtrations in the constructible heart

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, paragraphs 1 and 4;
Bhatt--Scholze, Propositions 6.8.4 and 6.8.14, Remark 6.8.15.
(blueprint: lem-zl-classical-weil-filtration-heart-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]


omit hUnits in
/-- The proposition specializes only the inherited prime-invertibility instance. No
prime-unit or auxiliary-lattice assumption is added to the geometric hypotheses.
The uniform realization is the inverse-limit realization above; the filtration itself
is arbitrary, and its given top isomorphism is retained in ZlFiltrationTransport.
Source: blueprint real-mixed-by-curves, paragraphs 1 and 4; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-weil-filtration-heart-transport). -/
def ZlClassicalFiltrationHeartTransport (iota : Ω ≃+* ℂ) : Prop :=
  letI : Fact (∀ x : (D.geometricFiber Y₀).left,
      IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _ (zlClassicalStalkInvertible D l hl Y₀ x)⟩
  ∀ R : ZlClassicalRealization D l hl Ω Y₀,
    ∀ (r : ℕ) (F : ZlClassicalFiltration D l Ω Y₀ r)
      (G : sfCommonStageWeilSheaf D l hl Y₀ Ω)
      (e : (R.weil D l hl Ω Y₀).obj (F.terms (Fin.last r)) ≅ G),
      Nonempty (ZlFiltrationTransport D l hl Ω Y₀ R r F G e iota)

omit hUnits in
/-- Realize a prescribed classical lisse Weil filtration, including its actual maps,
quotients, normalized local operators, weights and one common finite coefficient stage.
Every return period is allowed: n+1=m*d gives the local operator for an m-fold
constant extension with its iterated Weil structure, without a minimal-period assumption.
Source: blueprint real-mixed-by-curves proof, paragraphs 1 and 4; BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-weil-filtration-heart-transport).

Proof:
1. Finite type over the field makes the geometric fibre noetherian, finite-dimensional,
and a finite union of clopen connected components. Work componentwise, including empty Y.
2. Use the classical Hom colimit to put all terms, quotients, arrows, Weil maps and inverse
Weil maps over one finite coefficient field. Enlarge it for their finitely many equations.
3. Use cor-galois-lisse-representations and lem-pod-profinite-stable-lattice to replace
underlying systems by finite locally free lattices. Do not make Weil maps integral.
4. Complete the systems by inverse limits. Compose the fully faithful comparison of
lem-per-lisse-completed-system-comparison with lem-tw-lisse-rational-realization. Its
fraction rule realizes every a tensor f; lift Weil maps and inverses and their equations.
5. Normalize fibres by completed geometric pullback and point sections. The point clause
of lem-tw identifies sections with the inverse limit of finite-level adic stalks. Compare
also through J of lem-fd-rational-coefficient-category-comparison and the normalized PBC
fibres, using lem-per-continuous-rational-derived-realization.
6. Apply lem-dl-a1-constructible-fibres-exact to the realized short complexes. They are
short exact in the actual heart; conjugate the top identification by the given e.
7. At the finite field, lem-per-adic-normalized-fibre-exactness detects exactness. Exact
faithful extension of fields descends fibre exactness from the coefficient closure.
8. The finite common-stage calculus puts all this data and all its equations at one
larger field; retain the lisse models and the actual inverses there.
9. On finite cover germs, point transport is precomposition by point Frobenius. The
finite-level comparisons, inverse limits and localization preserve it. Induct on n in
the recorded localPointTransportIterate and localWeilIterate. Their return compositor is
the same semilinear scheme-map equality, so the complete local operators intertwine.
10. Conjugacy gives the same eigenvalues and hence exactly the same punctual purity for
each real weight, including zero quotients with vacuous purity.
11. Group m successive transport and Weil factors for a constant extension. The assertion
for every return period includes these grouped operators. For r=0 there are no quotient
sequences; the zero object and its identification are represented at any finite field. -/
theorem zl_classical_weil_filtration_heart_transport (iota : Ω ≃+* ℂ) :
    ZlClassicalFiltrationHeartTransport D l hl Ω Y₀ iota := by
  let : Fact (∀ x : (D.geometricFiber Y₀).left,
      IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x)) :=
    ⟨fun x ↦ @isUnit_of_invertible _ _ _ (zlClassicalStalkInvertible D l hl Y₀ x)⟩
  intro R r F G e
  obtain ⟨E, M, a, b, ha, hb, hz, hx⟩ :=
    zl_classical_filtration_exact_diagram D l hl Ω Y₀ R r F
  obtain ⟨c, d, hc, hd⟩ :=
    zl_classical_filtration_diagram_fibres D l hl Ω Y₀ R r F E M a b ha hb
  exact ⟨{
    field := E
    model := M
    terms := a
    quotients := b
    inclusion := ha
    quotient := hb
    top := a (Fin.last r) ≪≫
      (((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).inverseImage
        (sfCommonStageWeilForget D l hl Y₀ Ω)).ι).mapIso e
    top_identification := rfl
    zero := hz
    exact := hx
    terms_fibres := c
    quotient_fibres := d
    inclusion_fibres := hc
    quotient_fibres_natural := hd
    purity := fun j w ↦
      zl_classical_realization_punctual_purity D l hl Ω Y₀ R (F.quotients j) iota w
  }⟩



end WeilConjectures
