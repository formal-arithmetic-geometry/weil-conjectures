/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.Algebra.Category.ModuleCat.Adjunctions
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! # K-flat resolutions compatible with the coefficient-universe lift

Source: Stacks Project, more-algebra.tex, lemma-K-flat-resolution and remark-P-resolution.
-/

@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits

