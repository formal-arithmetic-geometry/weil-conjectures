/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.HomologyVanishingLocalizationSpan
import WeilConjectures.RingTheory.MPseudoCoherentLocalizationConeStep

/-!
# Gluing pseudo-coherence over a finite standard-open cover

Source: Stacks Project, More on Algebra, Lemma 15.66.14 (Tag 066D), with Definition 064P
and Lemma 064U (blueprint: lem-pc-ring-pseudo-coherent-localization-glue).
-/

@[expose] public section

universe w₁ w₂ v₁ u₁

open CategoryTheory

namespace DerivedCategory

end DerivedCategory
