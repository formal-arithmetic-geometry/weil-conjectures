/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair

/-!
# Sections of the invariant divisorial direct image

Source: ILO, Exposé VI, paragraph following Proposition 3.5, printed p. 74
(blueprint: def-per-invariant-divisorial-direct-image).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The given group element acts on `W ×[Y] X` over `W`, by its prescribed action
on the second projection. Source: ILO VI, paragraph after 3.5
(blueprint: def-per-invariant-divisorial-direct-image). -/
noncomputable def quotientEtaleActionMap {X Y : Scheme.{u}}
    {G : Type v} [Group G] (a : G →* Aut X) (q : X ⟶ Y)
    (hq : ∀ g : G, (a g).hom ≫ q = q) (W : Y.Etale) (g : G) :
    pullback W.hom q ⟶ pullback W.hom q :=
  pullback.lift (pullback.fst W.hom q) (pullback.snd W.hom q ≫ (a g).hom)
    (by rw [Category.assoc, hq, pullback.condition])

/-- The sections of `(q_* M_X)^G` on the étale test object `W`: the intersection
of the divisorial section monoid on `W ×[Y] X` with all equalizers of the group
pullbacks and the identity. This is an actual submonoid of the actual section ring.
Its restrictions are the restrictions of functions, so a structural-compatible family
of section isomorphisms identifies the entire invariant direct image sheaf.
Source: ILO VI, paragraph after 3.5 (blueprint: def-per-invariant-divisorial-direct-image). -/
noncomputable def invariantDivisorialDirectImageSections {X Y : Scheme.{u}} (U : X.Opens)
    {G : Type v} [Group G] (a : G →* Aut X) (q : X ⟶ Y)
    (hq : ∀ g : G, (a g).hom ≫ q = q) (W : Y.Etale) :
    Submonoid Γ(pullback W.hom q, ⊤) :=
  divisorialSections U.ι (q.Etale.obj W) ⊓
    ⨅ g : G, (quotientEtaleActionMap a q hq W g).appTop.hom.toMonoidHom.eqLocusM
      (MonoidHom.id _)

end AlgebraicGeometry
