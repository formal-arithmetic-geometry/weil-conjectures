/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration

public import WeilConjectures.CategoryTheory.CanonicalFiltration
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finite filtration induction

Source: the blueprint of the Weil conjectures, chapter `sec-proper-base-change`,
unit `sk-thm-properbasechange`, node `lem-sp-finite-filtration-induction`
(blueprint: lem-sp-finite-filtration-induction); Stacks Project, Homology,
Definition 0121 (`definition-filtered`), the paragraph defining `gr` before Lemma 05SP,
and Lemma 0127 (`lemma-characterize-strict`).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject

end FilteredObject

end CategoryTheory
