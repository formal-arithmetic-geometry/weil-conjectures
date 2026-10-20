module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Flat.QuasiCompactCover
public import Mathlib.CategoryTheory.Extensive

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# The pro-étale site of a scheme

-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable (X : Scheme.{u})

instance Basic_hasIsos : (precoverage X).HasIsos := by
  dsimp [precoverage]
  infer_instance

instance Basic_isStableUnderComposition : (precoverage X).IsStableUnderComposition := by
  dsimp [precoverage]
  infer_instance

instance Basic_isStableUnderBaseChange : (precoverage X).IsStableUnderBaseChange := by
  dsimp [precoverage]
  infer_instance

variable {S : Scheme.{u}}

end ProEt

end AlgebraicGeometry.Scheme
