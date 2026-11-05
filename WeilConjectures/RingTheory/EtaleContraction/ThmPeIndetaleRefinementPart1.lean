/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.Etale
public import WeilConjectures.RingTheory.ProEtale.Contraction.Covers
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Successive adjoining of étale sections

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-etale-contraction, order 1226
(blueprint: def-weil-pbc-etale-contraction).

We work dually in commutative rings: finite wide pullbacks are finite tensor
coproducts, and the two limits below are the two ring colimits in the source.
Taking the skeleton of the small model ensures exactly one representative per
algebra isomorphism class, rather than one factor for every object of the model.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CommRingCat.EtaleContraction

end CommRingCat.EtaleContraction

