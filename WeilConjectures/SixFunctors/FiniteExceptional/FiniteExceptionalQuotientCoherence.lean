/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalMateCocycle
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalMateIdentity
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalSupportMapCocycle
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalSupportMapIdentity

/-! # Finite exceptional coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- Composition and identity for the specified exceptional quotient mates.
Source: current blueprint proof paragraph 2, coherent duality comparisons and their
cocycle (blueprint: lem-sf-finite-exceptional-quotient-coherence).
Proof: the compact-support coefficient comparisons compose with the canonical scalar
tensor associators, by comparison_composition. Conjugation by finiteImageIso and
restriction through the full inclusion preserve this equation and give the same
cocycle for q. Transpose the inverse comparison equation under the three normalized
adjunctions. Naturality, the triangle identities, and mate pasting give the displayed
b cocycle. For identical indices comparison_identity identifies q with scalar
multiplication at both endpoints; transposing gives the selfReduction formula.
The equal-index scalar map is the actual identity ring map, and the chosen
selfReduction is the conjugate tensor unit, so no identifications are omitted. -/
theorem exceptional_quotient_coherence :
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
        (selfReduction l E X n).hom.app ((G l E D hl f c n).obj L)) := by
  constructor
  · exact mate_cocycle l E D hl f c
      (support_map_cocycle l E D hl f c)
  · exact mate_identity l E D hl f c
      (support_map_identity l E D hl f c)

end WeilConjectures.FiniteExceptional
