/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Category.Profinite.Limits
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstantHom

/-!

# `LocallyConstant (-, ℤ)` sends pullbacks of profinite sets to pushouts of rings

For a cospan `X ⟶ Z ⟵ Y` of profinite sets with (explicit) pullback `P = X ×_Z Y`, the square
of rings of locally constant integer-valued functions
```
LC(Z, ℤ) ⟶ LC(X, ℤ)
   ↓          ↓
LC(Y, ℤ) ⟶ LC(P, ℤ)
```
is a pushout (`Profinite.isPushout_locallyConstant_pullback`). Ring maps `LC(S, ℤ) ⟶ A` are
continuous maps `Spec A → S` (`LocallyConstant.liftPrimeSpectrum_specMap`), so this is the
universal property of `P` tested against the spaces `Spec A`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Profinite

variable {X Y Z : Profinite.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

end Profinite
