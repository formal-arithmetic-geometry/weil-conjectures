/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.SemilocalNormalizationDimOne
import WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPower

/-! # Conductor control for a one-dimensional semilocal domain

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2
(blueprint: lem-sc-semilocal-dim-one-conductor)
-/

@[expose] public section

universe u v

