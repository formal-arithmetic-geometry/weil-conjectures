/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralBasicRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.ConstructibleReductionGood
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenSupportStepBounds
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.ProperSupportStepBounds

/-! # The support realization domain contains constructible integral inputs

Source: Zheng, Construction 5.25; the open and proper constructibility theorems.
(blueprint: lem-sf-exceptional-support-domain)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- Reduction, open extension and proper image satisfy all intermediate support bounds.
Proof: reduction of a constructible integral object is Good. Apply open preservation,
retaining its independent integral constructibility conclusion, and then proper
preservation. These are exactly the four conjuncts of the support domain. The
compactification ambient scheme is finite type over the base because its structural
map factors through the proper map to Y. No separatedness of X or Y over the base
is needed. Empty opens and zero inputs satisfy the same preservation theorems.
Source: Zheng, Construction 5.25 and Proposition 5.24; Stacks Tags 0941 and 0D6E.
(blueprint: lem-sf-exceptional-support-domain) -/
theorem basicSupportDomain_of_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [QuasiCompact f]
    (c : Compactification f) (K : Integral l E X) (hK : sfIntegralConstructible l E X K) :
    basicSupportDomain l E o c K := by
  let U : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
  let V : Over (Spec (.of D.k)) := Over.mk (Y ↘ Spec (.of D.k))
  let : LocallyOfFiniteType U.hom := inferInstanceAs
    (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
  let : QuasiCompact U.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
  let : LocallyOfFiniteType V.hom := inferInstanceAs
    (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
  let : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
  let g : U ⟶ V := Over.homMk f (comp_over f _)
  let Z := compactAmbient (f := g) c
  let : LocallyOfFiniteType Z.hom :=
    show LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of D.k))) from inferInstance
  let : QuasiCompact Z.hom :=
    show QuasiCompact (c.g ≫ (Y ↘ Spec (.of D.k))) from inferInstance
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let : IsOpenImmersion (compactOpen (f := g) c).left := c.isOpenImmersion
  let : QuasiCompact (compactOpen (f := g) c).left := inferInstanceAs (QuasiCompact c.i)
  let : IsProper (compactProper (f := g) c).left := c.isProper
  have hR := constructibleReduction_good l E D hl U K hK
  have hJ := openSupportStep_bounds l E D hl o (compactOpen (f := g) c) _ hR K hK
  have hP := properSupportStep_bounds l E D hl o (compactProper (f := g) c) _ hJ.1
    ((ringedOpen l E c.i).obj K) hJ.2
  exact ⟨⟨hK, hR, hP.1⟩, hJ.1⟩

end WeilConjectures.IntegralSystemRealization
