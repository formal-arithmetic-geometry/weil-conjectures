module

public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module
import Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The transitions explicitly transposed from the restricted units satisfy identity,
composition and counit compatibility, and the inside-open counit stalks give compatible
isomorphisms. Source: Stacks Project, Sheaves, Tag 00A7 (2)-(4) and Tag 00A5.

Proof: Denote extension and restriction at W by L_W and R_W, with unit eta_W and counit eps_W.
The displayed iota is defined by the inverse adjunction hom-equivalence, not by choosing an
existence witness. For W = W', the restriction transport is the identity on every section and
the transported unit is eta_W; the transpose of identity is eta_W, so injectivity of the
hom-equivalence gives the identity equation. For nested W <= W' <= W'', transpose the composite
at W. Naturality of eta_W, the defining transpose equations, and the sectionwise identity
coherences of overFunctorMap reduce this transpose to the restriction of eta_W''. Injectivity
then proves composition. Transpose iota(W,W') followed by eps_W': naturality of the
hom-equivalence and the right triangle identity reduce it to identity on R_W F, which is the
transpose of eps_W. This proves counit compatibility for every W', including top.

At x in W, use ModuleExtensionByZeroStalkInside and the usual restriction-stalk comparison.
The germ formula there identifies the stalk of eta_W with an isomorphism. The right triangle
identity identifies its composite with the restricted eps_W with identity. Thus the stalk of
eps_W is the inverse isomorphism. Define e(W,x) to be its inverse. This establishes the required
inverse formula and determines e uniquely. Apply the stalk functor to the general counit
compatibility equation. It gives iota_x followed by e(W',x).inv equal to e(W,x).inv; cancel the
two isomorphisms to obtain the final equation. All transports are O_X,x-linear, and the argument
uses the units of the chosen adjunctions themselves, so it needs no agreement between different
choices of adjunction. Empty W has no inside points; on W=W' the formula above is identity.
(blueprint: new-module-extension-by-zero-coherence) -/
theorem ModuleExtensionByZeroStalkTransitionCoherence (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) :
    let iota := fun (W W' : Opens X) (h : W ≤ W') ↦
      ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _).symm
      ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
        (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
          ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
            ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
        (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
          ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)))
    (∀ W : Opens X, iota W W le_rfl = 𝟙 _) ∧
    (∀ (W W' W'' : Opens X) (h : W ≤ W') (h' : W' ≤ W''),
      iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')) ∧
    (∀ W : Opens X,
      iota W ⊤ le_top ≫
          (Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F =
        (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app F) ∧
    ∃ e : (∀ (W : Opens X) (x : X), x ∈ W →
        ((RingedSpace.moduleStalkFunctor X x).obj F ≅
          (RingedSpace.moduleStalkFunctor X x).obj
            ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
              PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F)))),
      (∀ (W : Opens X) (x : X) (hx : x ∈ W),
        (e W x hx).inv =
          (RingedSpace.moduleStalkFunctor X x).map
            ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app
              F)) ∧
      (∀ (W W' : Opens X) (h : W ≤ W') (x : X) (hx : x ∈ W),
        (e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h) =
          (e W' x (h hx)).hom) := by
  sorry

end AlgebraicGeometry
