/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3 -/
module

public import Sheaf.Paper.CompactSupportStrictScalarCompositionPrelude

/-! # Arithmetic selection of the strict scalar image comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Selecting arithmetic levels commutes with the proper/open scalar mate.
Source: Stacks 07A6, 0D6E, 0E8I, 0940; support realization, selection step.
(blueprint: lem-pur-strict-scalar-comparison-selection).
Proof: on ordinary strict towers the selection functor is precomposition by the
arithmetic index. Constant scalar tensor, open extension, direct image, and scalar
restriction act termwise. Thus their selection squares are identities and commute
with the ordinary scalar restriction square. Derive this commuting cube using
the specified whole-complex units; positive selection preserves K-injectives.
Take scalar-adjunction mates to obtain the same identity for the proper scalar
mate. Exact localization gives the open scalar identity. Paste the proper and
open identities, using the definitions of comparison and reindexImage, to obtain
the displayed square. This argument works on arbitrary derived strict towers. -/
theorem comparison_selection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : ℕ) (he : 1 ≤ e)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (comparison l E F i c).app ((subsequence l E X e).obj K) ≫
        (image l F c).map ((compositionSelection l E F i X e).hom.app K) ≫
        (reindexImage l F c e he).inv.app ((T l E F i X).obj K) =
      (T l E F i Y).map ((reindexImage l E c e he).inv.app K) ≫
        (compositionSelection l E F i Y e).hom.app ((image l E c).obj K) ≫
        (subsequence l F Y e).map ((comparison l E F i c).app K) := by
  sorry

end WeilConjectures.PurStrictScalar
