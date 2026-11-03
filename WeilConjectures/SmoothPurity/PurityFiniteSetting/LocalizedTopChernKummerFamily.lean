/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChernStatementModels

/-!
# The natural family of localized Kummer classes

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.proof.md`, universal and general cases
(blueprint: lem-pur-localized-chern-kummer-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Regular sections admit a family natural under regularity-preserving base change,
normalized by the positive ordered Kummer product in every étale frame.
No assertion about ordinary Chern classes or transverse direct sums is included.

Source: `thm-pur-localized-top-chern.proof.md`, universal case, general case,
and (L2) in Step 4 (blueprint: lem-pur-localized-chern-kummer-family).

Proof:
1. For each bundle use its actual total space and zero section from
`def-pur-vector-bundle-zero-section`. On trivializing opens its zero section is
that of affine r-space. The étale-origin localization triangle and
`cor-pur-affine-space-zero-section-purity` give vanishing of its local supported
cohomology sheaves below 2r, also over a singular base.
2. `lem-pur-supported-bottom-gluing`, applied to the inverse images of opens of
the base, makes degree-2r supported classes a sheaf there. On each trivializing
open take the ordered positive Kummer product of the linear coordinates.
`lem-pur-frame-independence` identifies the products on overlaps; finite stalk
dimension follows from finite type over the fixed field. Glue these sections,
not derived objects, to a unique universally normalized zero-section class.
3. Pull that class back along the actual geometric section using the Cartesian
zero scheme. `lem-pur-supported-hom-pullback` identifies this supported pullback
with the derived Hom arrow. The canonical site, adjunction, and finite Tate
comparisons are precisely `localizedTopChernSupported` in the imported interface.
4. Pullback respects Kummer boundaries and cup products. Thus on a trivialization
the result is the ordered boundary product of the section's components. An
arbitrary étale frame of its regular zero ideal gives the same product: compare
on common affine refinements by generating-tuple invariance, equivalently pull
back the universal frame comparison before restricting along the section. This
gives the exact `Etale.frameClass` formula in the statement.
5. For any base change, the pulled-back universal class and the universal class
of the pulled-back bundle have the same coordinate restrictions. Bottom gluing
on that bundle's total space identifies them. Compose supported pullbacks with
the geometric section to get the displayed naturality law whenever the pulled-
back section remains regular. Its zero-scheme square is the canonical Cartesian
one, supplied as a conclusion. At rank zero the construction is the supported
unit (the empty product); empty supports give the zero arrow.
-/
theorem localizedTopChernKummerFamily_exists (P : PurityFiniteSetting.{u}) :
    ∃ c : P.LocalizedTopChernClasses,
      P.LocalizedTopChernBaseChange c ∧ P.LocalizedTopChernStatementFrameFormula c := by
  sorry

end WeilConjectures.PurityFiniteSetting
