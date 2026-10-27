/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Locally finite type monomorphisms of algebraic spaces into schemes

Source: Stacks Project, Morphisms of Spaces, Tag 0463, specialized to a scheme target
(blueprint: lem-sfb-space-lft-monomorphism-separated-lqf).

The morphism is a natural transformation on schemes over `S`. Both local finite type
and local quasi-finiteness are tested on every representable étale scheme chart.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A chartwise locally finite type monomorphism into a scheme is separated and
chartwise locally quasi-finite. Separatedness means that every scheme base change of
its relative diagonal is represented by a closed immersion. Local quasi-finiteness
uses the Stacks predicate, including its finite-type requirement.

Source: Stacks Project, Morphisms of Spaces, Tag 0463; More on Morphisms, Tag 02HE;
Morphisms of Schemes, Tag 02V5
(blueprint: lem-sfb-space-lft-monomorphism-separated-lqf).

Proof:
1. Sectionwise injectivity identifies a pair of sections with equal image in `h_T`.
   Thus the diagonal has the natural inverse given by the first projection. For any
   scheme test `h_W → X ×_(h_T) X`, its pullback is represented by `W` with identity
   projection, a closed immersion by def-weil-closed-immersion.
2. Fix a representable étale chart `e : h_V → X` and let `q : V → T` be its composite.
   For an affine first order thickening `H → H'` over `T`, two lifts `a,b : H' → V`
   have equal images under `f`; monicity gives `e a = e b`. The pullback
   `P = h_(H') ×_X h_V` is a scheme étale over `H'` by def-trf-algebraic-space.
   The sections `(id,a)` and `(id,b)` agree on `H`. Étaleness implies unramifiedness
   by def-weil-etale-morphism, and lem-weil-pbc-unramified-formally-unramified
   makes these sections equal. Projection to `V` gives `a = b`. This is precisely
   def-weil-pbc-formally-unramified-morphism for `q`.
3. The hypothesis makes `q` locally of finite type. Apply
   lem-weil-pbc-lft-formally-unramified-unramified to get its open diagonal.
4. Apply lem-weil-pbc-unramified-quasi-finite-at-points to `q`. This yields the
   affine-neighbourhood predicate of pqf-def-quasifinite at every point. Since the
   representable étale chart was arbitrary, the chartwise conclusion follows. -/
theorem separated_and_chartwise_isLocallyQuasiFinite_of_lft_monomorphism
    {S : Scheme.{u}} (T : Over S) (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hmono : ∀ H : Over S, Function.Injective (f.app (op H)))
    (hft : ∀ (V : Over S) (e : yoneda.obj V ⟶ X.obj.obj), IsEtale e →
      LocallyOfFiniteType (yoneda.preimage (e ≫ f)).left) :
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f) ∧
    ∀ (V : Over S) (e : yoneda.obj V ⟶ X.obj.obj), IsEtale e →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (e ≫ f)).left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
