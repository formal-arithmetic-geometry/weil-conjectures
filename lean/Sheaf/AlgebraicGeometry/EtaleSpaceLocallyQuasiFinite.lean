/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Étale algebraic spaces are locally quasi-finite on scheme charts

Source: Stacks Project, Morphisms of Spaces, Tag 03XU, using Morphisms, Tags 03WS and 02V5
(blueprint: lem-a1-etale-space-locally-quasi-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale map from an algebraic space to a scheme is locally quasi-finite, with both
properties tested on every representable étale scheme chart.
Source: Stacks Project, Tag 03XU, specialized to a scheme target, and Tag 03WS
(blueprint: lem-a1-etale-space-locally-quasi-finite).

The map to the scheme `T` is a natural transformation to its representable presheaf.
Yoneda identifies the composite from a chart `V` with a morphism of schemes over `S`.

Proof: fix any representable étale chart `v : h_V → E`. The hypothesis says that the
composite `g : V → T` is étale. By `def-weil-etale-morphism` it is unramified: it is
locally of finite type and its diagonal is an open immersion. Apply
`lem-weil-pbc-unramified-quasi-finite-at-points`, namely
`Scheme.Hom.isLocallyQuasiFinite_of_unramified`, to obtain local quasi-finiteness of `g`
in the sense of `pqf-def-quasifinite`. Since `V` and `v` were arbitrary, this is the
chartwise conclusion. Neither surjectivity nor quasi-compactness of the chart is used. -/
theorem chartwise_isLocallyQuasiFinite_of_etale
    {S : Scheme.{u}} (E : AlgebraicSpace S) (T : Over S)
    (f : E.obj.obj ⟶ yoneda.obj T)
    (hf : ∀ (V : Over S) (v : yoneda.obj V ⟶ E.obj.obj),
      IsEtale v → Etale (yonedaEquiv (v ≫ f)).left) :
    ∀ (V : Over S) (v : yoneda.obj V ⟶ E.obj.obj),
      IsEtale v → Scheme.Hom.IsLocallyQuasiFinite (yonedaEquiv (v ≫ f)).left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
