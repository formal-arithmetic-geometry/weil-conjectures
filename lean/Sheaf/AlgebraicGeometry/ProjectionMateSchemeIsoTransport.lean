/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Comma.Arrow
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Projection mate transport along scheme isomorphisms

Source: Stacks Project, Tag 08EU, affine-local reduction, expanded along scheme isomorphisms.
(blueprint: lem-pc-projection-mate-scheme-iso-transport).
-/

@[expose] public section

universe u w w'

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A supplied projection mate transports across a commuting square of scheme
isomorphisms, without any invertibility assumption on that mate.
Source: Stacks Project, perfect.tex, Tag 08EU, first sentence of its proof;
the scheme-isomorphism comparison part of the parent transport argument.
(blueprint: lem-pc-projection-mate-scheme-iso-transport).

Proof: Write a and b for the derived pushforwards along eY and eX, respectively.
Pushforward along an isomorphism and its inverse gives inverse exact module
functors. Localize their termwise complex functors to obtain equivalences on the
chosen localizations, even when their morphism universes differ. On K-flat
representatives the underived tensor comparisons give natural invertible
comparisons a(N tensor N') = a(N) tensor a(N') and similarly for b. Their
inverse comparisons descend as well, since exact equivalences preserve K-flat
complexes. The identity g;eY = eX;f gives a natural isomorphism
alpha : a followed by Lf* = Lg* followed by b: both are left derived functors
of the same underived composite. Computing on K-flat resolutions identifies
their counits, and uniqueness of left derived functors supplies alpha globally.
Similarly K-injective representatives and direct-image composition give
beta : Rg* followed by a = b followed by Rf*. Exact equivalences preserve
K-injectivity, so these comparisons descend on unbounded derived categories.

Conjugate p through a and b and then through alpha and beta to obtain q. Choose
beta as the right-adjoint conjugate of alpha (the K-injective comparison agrees
with it by the derived universal property). Thus q's unit and counit are precisely
p's transported unit and counit; their triangle identities follow from p's.
Conjugate t using the two tensor comparisons and alpha. Full faithfulness of b
lifts this conjugated natural isomorphism to s on the primed categories, including
its inverse. Set N = a.inverse(M) and E = b.inverse(L). Exact isomorphism
pushforward along eY.inv and eX.inv preserves quasi-coherent cohomology, so these
are objects of the two recorded quasi-coherent subcategories.

The counits of a and b identify a(N) with M and b(E) with L. The tensor and beta
comparisons therefore give invertible arrows c from a(N tensor Rg*(E)) to
M tensor Rf*(L), and d from a(Rg*(Lg*(N) tensor E)) to
Rf*(Lf*(M) tensor L). Let pi and pi' be the respective projection mates.
Expand each mate as its adjunction unit followed by the right adjoint of the
tensor comparison composed with identity tensor the adjunction counit.
Substitute the transported formulas for q's unit and counit. Naturality of the
tensor comparisons, alpha and beta then gives a(pi') followed by d = c followed
by pi. The two vertical isomorphisms c and d and this equation define the arrow
isomorphism in the conclusion. Empty schemes and zero objects use the same
functors and formulas, with no nonemptiness or boundedness hypotheses. No
projection-formula invertibility is used. -/
theorem projectionMate_schemeIso_transport
    (X Y X' Y' : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))]
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (hcomm : g ≫ eY.hom = eX.hom ≫ f)
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X) :
    ∃ (e : schemeDerivedCategory Y' ≌ schemeDerivedCategory Y)
      (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (s : tensor (schemeDerivedCategory Y') ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory X'))
      (N : schemeDerivedQCohCategory Y') (E : schemeDerivedQCohCategory X'),
      Nonempty (Arrow.mk (e.functor.map (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
        ((derivedPullback g).obj N.obj ⊗ E.obj)
        (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
          (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj)))) ≅
      Arrow.mk (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
        ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))) := by sorry

end AlgebraicGeometry
