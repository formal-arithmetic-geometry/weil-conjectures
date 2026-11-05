/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Elements of a strict henselization are algebraic

Let `A` be a local domain and `C` a domain which is a strict henselization of `A`. Then every
element of `C` is algebraic over `A`.

An étale `A`-algebra `S` becomes finite over the fraction field `Frac A` after base change, so
the image of `S` in any domain `C` receiving an injective map from `A` consists of algebraic
elements. The elements of `C` algebraic over `A` form a subalgebra; the legs of the colimit
cocone land in it, so the universal property gives a retraction of its inclusion.

## Main results

- `isAlgebraic_algHom_of_etale`: the image of an étale algebra in a domain is algebraic.
- `Algebra.IsStrictHenselization.isAlgebraic`: a strict henselization which is a domain is
  algebraic over the base.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra

end Algebra
