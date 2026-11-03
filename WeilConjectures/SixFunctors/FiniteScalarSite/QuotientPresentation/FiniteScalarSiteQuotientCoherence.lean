/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Successive finite quotient coherence for the canonical scalar/site mate

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower/
thm-coef-finite-hom.proof.md, final paragraph, successive quotient identities and
finite site transport; Stacks 06YY and 0D6D.
(blueprint: lem-coef-finite-hom-site-quotient-coherence).

We reuse the published finite constant-ring small-site presentations and normalized
ringed pullback comparisons. Index i denotes the positive exponent i+1. The data
below package those presentations simultaneously, so every shared vertex and lift
is literally shared. They do not assume the cocycle. The theorem asserts the
cocycle and identity normalization for these specified canonical comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.RingedDerivedComparisons

namespace WeilConjectures.FiniteScalarSite

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {X : Scheme.{u}}

/-- The exact site inverse image at a positive coefficient level.
Source: blueprint final site-transport sentence; Stacks 099R
(blueprint: lem-coef-finite-hom-site-quotient-coherence). -/
abbrev QuotientPresentation.U (d : QuotientPresentation l E X) (i : ℕ) :=
  (d.system.lift (d.nu i).morphism).edge.left

/-- Derived scalar extension on the etale small representative.
Source: Stacks 06YY (blueprint: lem-coef-finite-hom-site-quotient-coherence). -/
abbrev QuotientPresentation.Fet (d : QuotientPresentation l E X)
    {i j : ℕ} (h : j ≤ i) := (d.system.lift (d.scalarEt h).morphism).edge.left

/-- Derived scalar extension on the pro-etale small representative.
Source: Stacks 06YY (blueprint: lem-coef-finite-hom-site-quotient-coherence). -/
abbrev QuotientPresentation.Fpro (d : QuotientPresentation l E X)
    {i j : ℕ} (h : j ≤ i) := (d.system.lift (d.scalarPro h).morphism).edge.left

/-- The canonical finite coefficient/site comparison: inverse etale compositor
followed by the pro-etale compositor of the common ringed morphism. The geometric
middle two-isomorphism is the identity on that presentation.
Source: blueprint final paragraph; Stacks 0D6D
(blueprint: lem-coef-finite-hom-site-quotient-coherence). -/
def QuotientPresentation.h (d : QuotientPresentation l E X) {i j : ℕ} (hji : j ≤ i) :
    d.Fet hji ⋙ d.U j ≅ d.U i ⋙ d.Fpro hji :=
  (d.compEt hji).pullback.symm ≪≫ (d.compPro hji).pullback

/-- The quotient cocycle and the scalar identity normalization, for the actual
normalized comparisons. Here `assocEt.pullback` and `assocPro.pullback` are a^et
and a^pro of the node, so their inverses multiply the two scalar factors.
Source: blueprint thm-coef-finite-hom.proof.md, final paragraph; Stacks 06YY, 0D6D
(blueprint: lem-coef-finite-hom-site-quotient-coherence). -/
def QuotientPresentation.Coherent (d : QuotientPresentation l E X) : Prop :=
  (∀ {n m r : ℕ} (hm : m ≤ n) (hr : r ≤ m) (T : (d.et n).site.D),
    (d.U r).map ((d.assocEt hm hr).pullback.inv.app T) ≫
        (d.h (hr.trans hm)).hom.app T =
      (d.h hr).hom.app ((d.Fet hm).obj T) ≫
        (d.Fpro hr).map ((d.h hm).hom.app T) ≫
        (d.assocPro hm hr).pullback.inv.app ((d.U n).obj T)) ∧
  (∀ (i : ℕ) (T : (d.et i).site.D),
    (d.h (i := i) le_rfl).hom.app T ≫
        (d.idPro i).pullback.hom.app ((d.U i).obj T) =
      (d.U i).map ((d.idEt i).pullback.hom.app T))

/-- The canonical finite scalar/site mate satisfies the successive-quotient cocycle,
including repeated levels, and its identity quotient is the scalar unitor.
Source: current blueprint thm-coef-finite-hom.proof.md, final paragraph
(blueprint: lem-coef-finite-hom-site-quotient-coherence).

Proof: fix any of the specified simultaneous presentations d. Its scalar changes
are the identity geometric morphisms with quotient structural maps, and its site
comparisons are the transported geometric comparison. Both mixed composites have
the same inverse image and quotient structural map. The fields of d pin all
comparisons by the ordinary insertion and K-flat representative equations, including
the identity quotients. Thus the following computation applies to every such d.

For an arbitrary T choose a flat-term K-flat representative P (lem-pc-kflat-resolution).
Ringed pullback preserves flat-term K-flat representatives, so all successive scalar
and site pullbacks are computed termwise (lem-weil-pbc-ringed-topoi-derived-pullback
and lem-weil-pbc-ringed-topoi-derived-tensor-pullback). The ordinary insertion and
representative equations of Composition identify h with balanced scalar/site
association and a inverse with multiplication of the scalar factors. On a local
generator (x tensor b) tensor c both sides send it to nu(x) tensor image(b)*c.
Additivity and balancing give equality of module-sheaf maps degreewise. No complex
factors are interchanged, hence no sign occurs. Localize this cochain equality and
use the natural comparison with a resolution to obtain the stated equality at T.
For m=n or r=m, the normalized identity comparison replaces the relevant scalar
factor by x tensor 1 mapping to x; the same computation gives the unit equation,
including n=m=r. No flatness of quotient maps or bound on T is used. -/
theorem finiteHomSiteQuotientCoherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ d : QuotientPresentation l E X, d.Coherent := by
  sorry

end WeilConjectures.FiniteScalarSite
