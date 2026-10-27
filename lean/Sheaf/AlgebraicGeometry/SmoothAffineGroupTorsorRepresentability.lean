/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.Over

import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Representability of torsors under smooth affine group schemes

Source: Stacks Project, Groupoids, Tag 049C; Descent, Tags 0245, 02L5 and 02VL;
Morphisms, Tag 056G (blueprint: lem-sfb-smooth-affine-group-torsor-representability).

The action on the given sheaf is specified on all test schemes, with its group
laws and restriction compatibility. Restriction of the represented functor along
`Over.map f` is the functor of points of the base-changed group. `uliftYoneda`
places its values in the same universe as the sheaf without changing the points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- An fppf sheaf locally equivariantly isomorphic to a smooth affine finitely
presented group scheme is represented by an affine smooth surjective universally
open scheme, with the given action represented and the torsor map an isomorphism.

Source: Stacks Project, Groupoids, Tag 049C; Descent, Tags 0245, 02L5 and 02VL;
Morphisms, Tag 056G (blueprint: lem-sfb-smooth-affine-group-torsor-representability).

Proof:
1. The equivariant local trivializations give unique scheme overlap isomorphisms
   by lem-galois-yoneda-fully-faithful. Faithfulness gives the identity and cocycle,
   hence def-trf-scheme-cover-descent-datum applies.
2. Use lem-trf-fppf-family-coproduct-descent-encoding. The coproduct of the local
   groups is the base change of G to the coproduct of the covering schemes:
   construct the comparison on the disjoint open components and glue its inverse
   using lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-scheme-morphism-gluing.
   It is affine by lem-weil-pbc-affine-morphism-permanence. The encoding lemma
   handles arbitrary covering families without assuming their coproduct is quasi-compact.
3. Apply lem-galois-fpqc-affine-descent-effective and the same-scheme effectivity
   clause of the encoding lemma to obtain P. Local sections of F give compatible
   local maps to P, and conversely. The sheaf axiom, lem-trf-fppf-covering-is-fpqc
   and lem-weil-pbc-fpqc-representable-descent glue them to inverse natural bijections.
4. Transfer the action through these bijections. Yoneda represents it by an action
   morphism; faithfulness gives its laws. Locally the torsor map is (g,y) to (gy,y),
   with inverse (x,y) to (xy⁻¹,y). Uniqueness of this local group element and
   the representable sheaf axiom glue the inverse, giving an isomorphism globally.
5. Affineness descends by lem-weil-pbc-fpqc-descend-affine. Smoothness descends by
   lem-sfb-space-smooth-surjective-fppf-locality, using identity etale charts for
   schemes. Local identity sections show the image of P contains every covering
   image, hence P is surjective; no global section over each test is assumed.
6. By sbc-lem-smooth-criterion the projection is flat and locally finitely presented;
   lem-weil-pbc-flat-lfp-open gives universal openness. No reducedness or Noetherian
   hypothesis is used. For the trivial group, sheaf gluing identifies F with h_S.
   For empty S the empty covering and the sheaf axiom give the empty representing scheme.
-/
theorem smooth_affine_group_torsor_representability
    (k : Type u) [Field k] (S : Scheme.{u}) (_s : S ⟶ Spec (.of k))
    (G : Over S) [GrpObj G] [IsAffineHom G.hom] [Smooth G.hom]
    [LocallyOfFinitePresentation G.hom]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (act : ∀ T : Over S, (T ⟶ G) → F.obj.obj (op T) → F.obj.obj (op T))
    (one_act : ∀ (T : Over S) (x : F.obj.obj (op T)), act T 1 x = x)
    (mul_act : ∀ (T : Over S) (g h : T ⟶ G) (x : F.obj.obj (op T)),
      act T (g * h) x = act T g (act T h x))
    (map_act : ∀ (T T' : Over S) (f : T' ⟶ T) (g : T ⟶ G)
      (x : F.obj.obj (op T)),
      F.obj.map f.op (act T g x) = act T' (f ≫ g) (F.obj.map f.op x))
    (locally_trivial : ∃ (I : Type (u + 1)) (U : I → Scheme.{u})
      (f : ∀ i, U i ⟶ S), Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage S ∧
      ∀ i, ∃ e : (Over.map (f i)).op ⋙ F.obj ≅
          (Over.map (f i)).op ⋙ uliftYoneda.{u + 1}.obj G,
        ∀ (T : Over (U i)) (g : (Over.map (f i)).obj T ⟶ G)
          (x : F.obj.obj (op ((Over.map (f i)).obj T))),
          (e.hom.app (op T) (act ((Over.map (f i)).obj T) g x)).down =
            lift g (e.hom.app (op T) x).down ≫ μ[G]) :
    ∃ (P : Over S) (e : F.obj ≅ uliftYoneda.{u + 1}.obj P) (a : ModObj G P),
      IsAffineHom P.hom ∧ Smooth P.hom ∧ Surjective P.hom ∧ UniversallyOpen P.hom ∧
      (∀ (T : Over S) (g : T ⟶ G) (x : F.obj.obj (op T)),
        (e.hom.app (op T) (act T g x)).down =
          lift g (e.hom.app (op T) x).down ≫ a.smul) ∧
      IsIso (lift a.smul (snd G P)) := by
  sorry

end AlgebraicGeometry
