/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U6
-/
module

public import Sheaf.Paper.ConstantExtensionWeilHeartData
public import Sheaf.Paper.WeilIndSheafCategory

/-! # The ordered sheet return of actual inverse image

Source: Deligne, Weil II, (1.1.7)--(1.1.10), pp. 150--152.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Pulling the ordered Weil iterate to the distinguished sheet agrees with the
restriction iterate under the normalized pullback compositor.
Source: Deligne, Weil II, paragraph after (1.1.10), p. 152.
(blueprint: lem-zl-pullback-sheet-return-comparison)

Proof: write pi for the geometric projection and j for the distinguished sheet.
At length one, expand the defining Frobenius square of actual Weil inverse image.
Naturality and associativity of the integral-normalized pullback compositor give
the square obtained by pulling the original Weil map along j followed by pi.
For the successor length, expand both ordered iterates. Apply the preceding square
to the next Weil-map factor, then apply the induction hypothesis to the remaining
factors. Associativity of the normalized compositors identifies the two ways of
reassociating these pullbacks; their naturality moves the comparison past that
next Weil-map factor. No factors are permuted. The sheet-return identity identifies
the source with geometric q^m-Frobenius on the extended fibre, and j followed by pi
is the specified fibre isomorphism. Its Frobenius identity therefore gives exactly
the comparison on the left. The comparisons at common stages are the localized
integral comparisons; scalar localization and descent preserve these equations.
For m=1 only the base square is needed. The proof makes no connectedness or lissity
assumption and applies unchanged to zero carriers and the empty scheme. -/
theorem pullbackSheetReturnComparison (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    letI := sfWeilPrimeInvertible D l hl X₀
    letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
    letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀)
    (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω).map
      ((zlPullComp l Ω (constantExtensionSheet D m hm X₀)
        (zlFiberMap D (constantExtensionProjection D m hm X₀))).inv.app F.obj.carrier) ≫
        (constantExtensionRestrictionComparison D m hm X₀ l hl Ω F.obj.carrier).hom ≫
          (constantExtensionFiberPull D m hm X₀ l hl Ω).map
            (constantExtensionWeilIterate D l hl Ω X₀ F.obj (m - 1)).hom =
      (constantExtensionReturnComparison D m hm X₀ l hl Ω
        ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F).obj.carrier).hom ≫
        (constantExtensionSheetPull D m hm X₀ l hl Ω).map
          (constantExtensionWeilIterate D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            ((zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)).obj F).obj
            (m - 1)).hom ≫
        (zlPullComp l Ω (constantExtensionSheet D m hm X₀)
          (zlFiberMap D (constantExtensionProjection D m hm X₀))).inv.app F.obj.carrier := by
  sorry

end WeilConjectures
