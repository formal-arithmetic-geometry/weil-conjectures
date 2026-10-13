/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import Sheaf.AlgebraicGeometry.LocalMapPullbackFamily
public import Sheaf.AlgebraicGeometry.LocalMapRecovery

/-! # Transport of local recovery equations

Source: Stacks Project, Tags 01ZR, 0095 and 0096.
(blueprint: lem-pc-fp-local-map-recovery-transport). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Recovery of a global map survives a further factorization of the limit map.
The three supplied comparisons are required to be the canonical ones.
Source: Stacks Project, Limits, Tag 01ZR, first proof, base change of local lifts;
Sheaves of Modules, Tags 0095 and 0096, composition of pullback.
(blueprint: lem-pc-fp-local-map-recovery-transport).

Proof: First substitute the equalities identifying A₀, A and B with their
tensor pullbacks. The three HEq hypotheses then become ordinary equalities of
isomorphisms; substitute these canonicality equalities. The equation p followed
by q equals b identifies the pullback of U₀ along b
with its iterated pullback along q and p, by the pullback universal property. On each
member of these identified covers, expand the displayed expression for r. Functoriality
of ordinary pullback expands its five factors. The ordinary pullback composition
isomorphisms combine the restrictions along the two paths to the same restriction.
The tensor comparison is the mate of pushforward composition under the tensor
adjunctions, and the restriction comparison uses the unique comparison between tensor
and ordinary left adjoints to pushforward. Composition of these mates is associative:
expanding their units and counits reduces both composites to the same pushforward
composition by the two triangle identities. Thus the restriction comparisons cancel
against the composition comparisons for q and p. The expression reduces to the
original recovery equation transported along the identified covers. Substitute that
equation. The same associativity identifies the remaining composite of e₀ and z with e,
using their three canonicality equations, and gives the required right side. All four
map equations have exactly the displayed source and target. No affineness, finiteness,
or descent morphism is used. Empty covers are vacuous; zero maps and identity maps obey
the same functoriality and triangle identities. -/
theorem finitePresentation_local_maps_recovery_transport
    {X₀ X₁ X₂ Z : Scheme.{u}}
    (h : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (p : Z ⟶ X₂)
    (b : Z ⟶ X₁) (a : Z ⟶ X₀) (d : X₂ ⟶ X₀)
    (wpq : p ≫ q = b) (wqh : q ≫ h = d)
    (wbh : b ≫ h = a) (wpd : p ≫ d = a)
    (A₀ : X₀.Modules ⥤ X₁.Modules) (hA₀ : A₀ = Scheme.Modules.tensorPullback h)
    (A : X₀.Modules ⥤ X₂.Modules) (hA : A = Scheme.Modules.tensorPullback d)
    (B : X₀.Modules ⥤ Z.Modules) (hB : B = Scheme.Modules.tensorPullback a)
    (F G : X₀.Modules)
    (φ : B.obj F ⟶ B.obj G)
    (e₀ : B ≅ A₀ ⋙ Scheme.Modules.tensorPullback b)
    (he₀ : HEq e₀ (Scheme.Modules.tensorPullbackCompositionIso b h a wbh))
    (e : B ≅
      A ⋙ Scheme.Modules.tensorPullback p)
    (he : HEq e (Scheme.Modules.tensorPullbackCompositionIso p d a wpd))
    (z : A ≅ A₀ ⋙ Scheme.Modules.tensorPullback q)
    (hz : HEq z (Scheme.Modules.tensorPullbackCompositionIso q h d wqh))
    (U₀ : X₁.OpenCover.{u}) :
    let Q₀ := modulesPseudofunctor.toDescentData U₀.f
    ∀ (r₀ : ∀ α, (Q₀.obj (A₀.obj F)).obj α ⟶
      (Q₀.obj (A₀.obj G)).obj α),
    localMapRecovery b U₀ (A₀.obj F) (A₀.obj G)
      (e₀.inv.app F ≫ φ ≫ e₀.hom.app G) r₀ →
    let U : X₂.OpenCover.{u} := U₀.pullback₁ q
    let V : Z.OpenCover.{u} := U.pullback₁ p
    let Q := modulesPseudofunctor.toDescentData U.f
    let r : ∀ α, (Q.obj (A.obj F)).obj α ⟶ (Q.obj (A.obj G)).obj α :=
      localMapPullbackFamily q U₀ (A₀.obj F) (A₀.obj G) (A.obj F) (A.obj G)
        (z.hom.app F) (z.inv.app G) r₀
    localMapRecovery p U (A.obj F) (A.obj G)
      (e.inv.app F ≫ φ ≫ e.hom.app G) r := by sorry

end AlgebraicGeometry
