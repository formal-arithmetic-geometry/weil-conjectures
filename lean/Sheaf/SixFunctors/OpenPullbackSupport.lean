/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData

/-! # Pullback of objects extended from an open -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- Derived pullback preserves the essential image of open extension by zero.
Only support is asserted; no choice or normalization of a base-change map is assumed.

Proof: localize the given Cartesian site square at the open. The comparison of
ordinary direct images is restriction of sections on the same fibre product.
Conjugating it through the two composite module adjunctions gives an ordinary
isomorphism from pullback of extension by zero to extension by zero of pullback.
This argument allows any structural ring map: the localized ring map is its
restriction, exactly as in `cornerCoefficient`.
Resolve the module on the open by a flat-term K-flat complex P. Extension by
zero preserves flatness and K-flatness: its ordinary tensor projection formula
identifies tensoring its extension with an acyclic E with extension of the tensor
of P and the exact restriction of E. Apply the ordinary base-change isomorphism
termwise to P. The specified flat-model comparisons for the two pullbacks identify
this termwise isomorphism with an isomorphism of derived objects whose target is
extension by zero of the derived corner pullback. This exhibits membership in the
essential image. For systems, perform this construction in the vertical ringed
diagram site; its sections and ring maps already include every transition.
The result is invariant under the unique compatible changes of left adjoint and
left-derived-functor presentations, so it holds for every `Operations` record.

Source: Stacks, sites-modules.tex, Tags 04J0, 0E8I and the composite-adjunction
comparison; sites-cohomology.tex, Tags 06YY, 0G7E and 06YS.
(blueprint: lem-sf-open-pullback-support). -/
theorem derivedPullback_openSupported {m : Mode} {d : Input.{u} m} {t : SiteSquare d}
    (o : Operations d t) (M : Der (restrictRing m d.j d.R)) :
    o.opens.jShriek'.essImage (o.gPull.derived.obj (o.opens.jShriek.obj M)) := by
  sorry

end SheafOfModules.OpenTensorNormalization
