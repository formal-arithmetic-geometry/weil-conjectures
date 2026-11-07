/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Submission.WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.TensorProduct.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Submission.WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
import Submission.WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChangeIsIso
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Submission.WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapPasting
import Submission.WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Submission.WeilConjectures.AlgebraicGeometry.AffineBaseChangeTensorComparisons
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullback

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Affine pushforward and arbitrary base change

Source: Stacks Project, Cohomology of Schemes, Lemma 02KG; the algebra and composition
clauses are the affine-local consequences specified by the DAG node
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-- Affine pushforward preserves quasi-coherence and its canonical base change map is invertible.
Source: Stacks Project, Lemma 02KG
(blueprint: lem-weil-pbc-affine-pushforward-base-change).
Proof: (1) affine morphisms are quasi-compact and quasi-separated, so pushforward preserves
quasi-coherence (01LC). (2) Restrict to affine opens on the two bases using the open-restriction
base change lemma; isomorphisms are detected on this basis. (3) Identify the resulting square
with spectra of R, R-prime, B and R-prime tensor B. (4) Replace F by the tilde of its sections
using the affine tilde-Gamma adjunction. The pushforward and pullback tilde comparisons identify
the base change map with r tensor m mapping to (r tensor 1) tensor m, by the adjunction unit.
Its inverse sends (r tensor b) tensor m to r tensor b*m. Thus it is an isomorphism. -/
theorem affinePushforward_baseChange {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent ∧
      IsIso (moduleBaseChangeMap f f' g g' sq.w F) := by
  constructor
  · exact isQuasicoherent_pushforward_of_isAffineHom f F
  · exact affinePushforward_baseChange_isIso f f' g g' sq F


end
end AlgebraicGeometry.Scheme.Modules
