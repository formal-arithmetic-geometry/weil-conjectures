module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import WeilConjectures.AlgebraicGeometry.GeometricPointMorphismStalkBijection

/-!
# Proper surjections lift prescribed geometric specializations

Source: Orgogozo, Modifications et cycles proches sur une base générale, proof of Lemma 9.1.5,
printed p. 21; Stacks Project, Tags 01KE and 0GJ5
(blueprint: lem-trf-proper-geometric-specialization-lift).

A geometric specialization `c : t̄ ⇒ s̄` of the small étale topos is recorded by its
inverse-image mate, a natural transformation between the geometric stalk functors
(lem-fix-geometric-stalk-topos-point, def-trf-geometric-morphism). Two canonical comparisons
express the image `p c'` of a specialization upstairs: the stalk map of a morphism of
geometric points (Stacks Tag 04FN; bijective by
lem-weil-pbc-geometric-point-morphism-stalk-bijection) and the identification of the stalk
of an étale inverse image with the stalk at the image point (Stacks Tag 03Q1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The stalk map `a^* : F_{s'} → F_s` of a morphism of geometric points `a : s → s'`
(`a ≫ s' = s`), on set-valued étale sheaves: the class of `σ` at `(U, ū')` goes to the class
of `σ` at `(U, ū' ∘ a)`. It is the map of fibres of the morphism of points of the small étale
site given by precomposition with `a`; it is bijective by
`AlgebraicGeometry.Scheme.geometricPointMorphism_stalk_bijection`.
Source: Stacks Project, Tag 04FN (remark-map-stalks)
(blueprint: lem-trf-proper-geometric-specialization-lift). -/
noncomputable def geometricPointMorphismSheafFiber {S : Scheme.{u}} {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S) (a : Spec (.of k) ⟶ Spec (.of k'))
    (ha : a ≫ s' = s) :
    (Scheme.pointSmallEtale s').sheafFiber (A := Type (u + 1)) ⟶
      (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1)) :=
  GrothendieckTopology.Point.Hom.sheafFiber
    (show Scheme.pointSmallEtale s ⟶ Scheme.pointSmallEtale s' from
      ⟨Functor.whiskerLeft (Scheme.Etale.forget S)
        (coyoneda.map (Over.homMk a ha : Over.mk s ⟶ Over.mk s').op)⟩)

/-- The stalk of the étale inverse image of a sheaf of sets is the stalk at the image point:
`(f^{-1} F)_x ≅ F_{f ∘ x}`, naturally in `F`. It is the composite of the comparison of the
constructed and abstract sheaf pullbacks, the fibre of the pulled-back point
(`GrothendieckTopology.Point.sheafFiberComapIso`) and the identification of that point with
`x ≫ f` (`AlgebraicGeometry.Scheme.pointSmallEtaleComapIso`).
Source: Stacks Project, Tag 03Q1 (lemma-stalk-pullback)
(blueprint: lem-trf-proper-geometric-specialization-lift). -/
noncomputable def etaleSetPullbackSheafFiberIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Scheme.etaleSetPullback f ⋙ (Scheme.pointSmallEtale x).sheafFiber (A := Type (u + 1)) ≅
      (Scheme.pointSmallEtale (x ≫ f)).sheafFiber (A := Type (u + 1)) :=
  Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafPullbackIso f.Etale
        (Type (u + 1)) Y.smallEtaleTopology X.smallEtaleTopology).symm _ ≪≫
    (GrothendieckTopology.Point.sheafFiberComapIso (Scheme.pointSmallEtale x) f.Etale
      (Scheme.Hom.coverPreserving_etale f) (Type (u + 1))).symm ≪≫
    GrothendieckTopology.Point.sheafFiberIso (Scheme.pointSmallEtaleComapIso f x)

/-- A proper surjection lifts a prescribed specialization of geometric étale points.
Source: Orgogozo, proof of Lemma 9.1.5, p. 21; Stacks Tags 01KE and 0GJ5
(blueprint: lem-trf-proper-geometric-specialization-lift).

The prescribed 2-morphism `c : t̄ ⇒ s̄` is given by its inverse-image mate
`c : F_s̄ → F_t̄`, and likewise `c'`. The last clause says that the image `p c'` is `c`
under the canonical isomorphisms: with `r^*` the bijective stalk maps of the morphisms of
geometric points `rs, rt` and `(p^{-1} F)_{x} ≅ F_{p x}` the inverse-image stalk
identification, `rt^* ∘ c = (p^{-1} F)_{t'} ∘ c'_{p^{-1} F} ∘ (p^{-1} F)_{s'}^{-1} ∘ rs^*`.

Proof: (1) Reconstruct the mate of `c` on pointed affine étale neighbourhoods and obtain
a map `a` from `Spec Ωt` into the strict localization `B` of `S` at `s̄`, over `S`, which
recovers the mate on every set sheaf. (2) `B` is strictly henselian local with canonical
closed lift `s_B` of `s̄`; the base change `q : W = T ×_S B → B` is surjective and closed,
by universal closedness of `p`. (3) Choose a point of `W` over `a`; an algebraic closure
`Ωt'` of its residue field gives `rt` and a geometric point `x_W` with `q x_W = a rt`.
(4) `q(x)` specializes to the closed point; closedness of `q` gives `y` with `x ⇝ y` over
it; a point of `Spec κ(y) ×_B Spec Ωs` and an algebraic closure `Ωs'` give `rs` and `y_W`
with `q y_W = s_B rs`. (5) Strict-local lifting of `x ⇝ y` at `x_W, y_W` (Tag 0GJ5) gives
the arrow `c_W : x_W ⇒ y_W` by germs. (6) Over the strictly henselian `B`, a natural map
out of the closed stalk is unique (global germs are bijective, Tag 03QO), so `q c_W` is the
canonical restriction. (7) Put `t' = v x_W`, `s' = v y_W`, `c' = v c_W`; then
`p t' = t rt`, `p s' = s rs`, and computing on affine germs with the inverse-image stalk
identification and the stalk bijections of `rs, rt` shows `p c' = c`.
-/
theorem exists_proper_geometric_specialization_lift
    {S T : Scheme.{u}} (p : T ⟶ S) [IsProper p] [Surjective p]
    {Ωs Ωt : Type u} [Field Ωs] [IsAlgClosed Ωs] [Field Ωt] [IsAlgClosed Ωt]
    (s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
    (c : (Scheme.pointSmallEtale s).sheafFiber (A := Type (u + 1)) ⟶
      (Scheme.pointSmallEtale t).sheafFiber (A := Type (u + 1))) :
    ∃ (Ωs' Ωt' : Type u) (_ : Field Ωs') (_ : IsAlgClosed Ωs')
      (_ : Field Ωt') (_ : IsAlgClosed Ωt')
      (rs : Spec (.of Ωs') ⟶ Spec (.of Ωs))
      (rt : Spec (.of Ωt') ⟶ Spec (.of Ωt))
      (s' : Spec (.of Ωs') ⟶ T) (t' : Spec (.of Ωt') ⟶ T)
      (c' : (Scheme.pointSmallEtale s').sheafFiber (A := Type (u + 1)) ⟶
        (Scheme.pointSmallEtale t').sheafFiber (A := Type (u + 1)))
      (hs : rs ≫ s = s' ≫ p) (ht : rt ≫ t = t' ≫ p),
      c ≫ geometricPointMorphismSheafFiber (t' ≫ p) t rt ht =
        geometricPointMorphismSheafFiber (s' ≫ p) s rs hs ≫
          (etaleSetPullbackSheafFiberIso p s').inv ≫
            Functor.whiskerLeft (Scheme.etaleSetPullback p) c' ≫
              (etaleSetPullbackSheafFiberIso p t').hom
:= by
  sorry

end AlgebraicGeometry
