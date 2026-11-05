/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.EtaleContraction.ThmPeIndetaleRefinementPart1
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian

/-!
# Properties of the étale contraction

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1227;
Stacks Project, proetale.tex, lemma-first-construction and Tag 097V
(blueprint: lem-weil-pbc-etale-contraction).
-/

@[expose] public section

universe u

namespace CommRingCat

-- The finite tensors present the step map as a pro-morphism in the opposite category.

-- The singleton containing the chosen isomorphism class supplies the next-stage map.

end CommRingCat
