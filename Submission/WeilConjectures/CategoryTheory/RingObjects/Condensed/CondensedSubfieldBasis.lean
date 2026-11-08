/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.Topology.ProfiniteCondensedRing
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Combinatorics.Quiver.ReflQuiver

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Coordinates of a finite subfield basis on condensed modules

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, first two sentences
(blueprint: lem-sfb-condensed-subfield-basis).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

private noncomputable abbrev abelianize :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  sheafCompose _ (forget₂ RingCat Ab)

private noncomputable abbrev coefficientMap
    {A B : Type} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ) :=
  abelianize.{u}.map (continuousMapRingSheafMap φ hφ)

end Profinite
