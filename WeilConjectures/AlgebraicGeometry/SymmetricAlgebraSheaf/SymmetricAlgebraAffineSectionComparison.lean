/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineComparisonMap
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange

/-! # Sectionwise comparison before sheafification

Source: Stacks Project, Constructions, Lemma 01LN; Schemes, Lemma 01I8;
Algebra, Lemma 0C6F.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-section-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite CategoryTheory.Functor
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

open scoped TensorProduct

end AlgebraicGeometry.SymmetricAlgebraSheaf
