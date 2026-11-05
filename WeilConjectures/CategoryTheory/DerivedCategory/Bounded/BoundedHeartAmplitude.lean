/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Finite cohomological amplitude from bounds on cohomology objects

Source: Stacks Project, derived.tex, Tag 08J5, remark-truncation-distinguished-triangle;
more-etale.tex, Tag 0G2A, lemma-derived-lower-shriek-bounded, proof of (3)
(blueprint: lem-pur-bounded-heart-amplitude).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace DerivedCategory

end DerivedCategory
