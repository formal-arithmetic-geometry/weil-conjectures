/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonMatchingTransport

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The section-valued comparison sheaf functor

Source: Stacks Project, Tag 0GLZ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable abbrev L {S T : Scheme.{u}} (f : T ⟶ S) :=
  Scheme.etaleSetPullback f

private noncomputable abbrev b {S T : Scheme.{u}} (f : T ⟶ S) :=
  MorphismProperty.Over.pullback @Etale ⊤ f

end AlgebraicGeometry
