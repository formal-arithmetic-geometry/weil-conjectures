/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Algebra.Group.Subgroup.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # The quotient by the normalizer of a split torus

Source: Conrad, Reductive Group Schemes, Theorem 2.3.1, pp.67-71,
Proposition 2.1.2 and Remark 2.3.5
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient).

The normalizer is tested after every morphism of test schemes. The coset presheaf
is the coequalizer of the two projections of the right-coset relation. Its fppf
sheafification, and the map to it, are constructed before stating representability.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Sections of the functorial normalizer: after every map V to W, the restricted
section normalizes the image of T(V) in G(V). Intersecting the inverse images of
ordinary subgroup normalizers gives the actual subgroup, with no representability
assumption. Source: Conrad, Proposition 2.1.2 and Theorem 2.3.1
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient). -/
def torusNormalizerSections {S : Scheme.{u}} {T G : Grp (Over S)}
    (i : T ⟶ G) (W : Over S) : Subgroup (W ⟶ G.X) :=
  ⨅ V : Over S, ⨅ f : V ⟶ W,
    (Subgroup.normalizer (Set.range (fun t : V ⟶ T.X ↦ t ≫ i.hom.hom))).comap
      ((yonedaGrpObj G.X).map f.op).hom

/-- The normalizer as a subpresheaf. Take the supremum of all subfunctors whose
sections lie in the explicitly defined normalizer subgroup. The all-tests condition
in torusNormalizerSections is stable under restriction (compose the test maps),
so this supremum has precisely those sections, not a smaller subset.
This lattice construction supplies the actual restriction maps without a choice
of a representing scheme. Source: Conrad, Proposition 2.1.2
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient). -/
def torusNormalizerSubfunctor {S : Scheme.{u}} {T G : Grp (Over S)} (i : T ⟶ G) :
    Subfunctor (yoneda.obj G.X) :=
  ⨆ (F : Subfunctor (yoneda.obj G.X))
    (_ : ∀ W : (Over S)ᵒᵖ, F.obj W ⊆ torusNormalizerSections i W.unop), F

/-- The right-coset relation: a pair (g,h) is related exactly when g inverse times h
normalizes T after every further test. The product is the fibre product over S.
Source: Conrad, Theorem 2.3.1, quotient by the normalizer
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient). -/
def torusNormalizerCosetRelation {S : Scheme.{u}} {T G : Grp (Over S)} (i : T ⟶ G) :
    Subfunctor (yoneda.obj (G.X ⊗ G.X)) :=
  (torusNormalizerSubfunctor i).preimage
    (yoneda.map ((fst G.X G.X)⁻¹ * snd G.X G.X))

/-- The presheaf of right cosets G(W)/N(W), constructed as the coequalizer of the
right-coset relation's projections. Colimits of set-valued presheaves are pointwise;
since this is already an equivalence relation its coequalizer is the coset set.
Source: Conrad, Theorem 2.3.1
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient). -/
def torusNormalizerCosetPresheaf {S : Scheme.{u}} {T G : Grp (Over S)} (i : T ⟶ G) :
    (Over S)ᵒᵖ ⥤ Type u :=
  coequalizer ((torusNormalizerCosetRelation i).ι ≫ yoneda.map (fst G.X G.X))
    ((torusNormalizerCosetRelation i).ι ≫ yoneda.map (snd G.X G.X))

/-- The actual fppf sheafification of the normalizer coset presheaf. The common
universe lift permits sheafification on the big site and excludes no test schemes.
Source: Conrad, Theorem 2.3.1
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient). -/
def torusNormalizerQuotientSheaf {S : Scheme.{u}} {T G : Grp (Over S)} (i : T ⟶ G) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (torusNormalizerCosetPresheaf i ⋙ uliftFunctor.{u + 1, u})

/-- The canonical map from G to the quotient sheaf: first take the coset, then the
unit of fppf sheafification. Source: Conrad, Theorem 2.3.1 and Remark 2.3.5
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient). -/
def torusNormalizerQuotientMap {S : Scheme.{u}} {T G : Grp (Over S)} (i : T ⟶ G) :
    yoneda.obj G.X ⋙ uliftFunctor.{u + 1, u} ⟶ (torusNormalizerQuotientSheaf i).obj :=
  Functor.whiskerRight
    (coequalizer.π ((torusNormalizerCosetRelation i).ι ≫ yoneda.map (fst G.X G.X))
      ((torusNormalizerCosetRelation i).ι ≫ yoneda.map (snd G.X G.X)))
    uliftFunctor.{u + 1, u} ≫
  toSheafify (Scheme.fppfTopology.over S)
    (torusNormalizerCosetPresheaf i ⋙ uliftFunctor.{u + 1, u})

/-- The fppf quotient of a smooth affine finitely presented group scheme by the
normalizer of a closed split torus is a smooth quasi-affine scheme, and its canonical
quotient morphism is smooth and surjective.
Source: Conrad, Theorem 2.3.1, pp.67-71, Proposition 2.1.2 and Remark 2.3.5
(blueprint: lem-sfb-split-torus-normalizer-quasi-affine-quotient).

Proof:
1. Restrict to an affine open U of S. By lem-sfb-relative-torus-centralizer-normalizer,
   N is smooth, affine, finitely presented and closed. By
   lem-sfb-split-torus-finite-torsion-normalizer-detection choose n with N(T)=N(T[n]),
   including when n is not invertible. Use lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-closed-immersion-base-change and
   lem-sfb-space-smooth-surjective-fppf-locality for these restrictions.
2. Apply lem-sfb-free-flat-group-space-quotient to the free action a.g=g*a inverse.
   By lem-pc-smooth-flat, N is flat and locally finitely presented. The quotient F
   is an algebraic space, its projection is fppf, and its kernel pair is N times G.
3. By lem-sfb-finite-diagonalizable-subgroup-parameter, conjugates of T[n] define a
   map to a quasi-affine parameter scheme Y. It factors through F by
   def-weil-pbc-sheafification and def-trf-scheme-algebraic-space. It is monic:
   locally lift two quotient sections to g,h; equal conjugates imply h inverse*g
   belongs to N(T[n])=N(T), so their cosets agree and hence their sections agree.
4. Use lemma-nagata-finite-type-to-separated-target and
   lem-sfb-representable-lft-fppf-source-descent to make F to Y locally finite type.
   By lem-sfb-space-lft-monomorphism-separated-lqf it is separated locally quasi-finite;
   lem-a1-separated-locally-qf-space-representable gives its representing scheme X_U.
5. The fppf surjection from affine G makes X_U quasi-compact. Apply
   lem-a1-lft-flat-lfp-source-descent and def-weil-finite-type-morphism to get finite
   type over U. The target Y is separated by lem-trf-quasi-affine-canonical-affine-embedding
   and lem-weil-pbc-closed-immersion-base-change. Then
   lemma-nagata-finite-type-to-separated-target makes X_U to Y quasi-compact, so
   lemma-nagata-zmt-quasi-affine-source shows X_U quasi-affine.
6. Pull back G to X_U along its own fppf cover. The resulting projection N times G
   to G is smooth. Descend smoothness by lem-sfb-space-smooth-surjective-fppf-locality.
   Apply lem-sbc-smooth-flat-surjective-source-descent to get X_U smooth over U.
7. Restriction preserves the quotient sheaf's universal property, so the X_U agree
   canonically on smaller affine opens and satisfy the cocycle condition. Use
   lem-weil-pbc-open-fibre-product and lem-weil-pbc-relative-glueing-affine-opens
   to glue them to X over S, representing the original fppf quotient sheaf.
8. Quasi-affineness is its affine-open definition def-nagata-quasi-affine-morphism.
   Open covers are fppf by lem-weil-pbc-etale-composition-cancellation and
   def-weil-etale-morphism; descend smoothness and surjectivity using
   lem-sfb-space-smooth-surjective-fppf-locality. The empty base gives the empty scheme. -/
theorem exists_smooth_quasiAffine_splitTorusNormalizer_quotient
    {S : Scheme.{u}} (G T : Grp (Over S))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    (r : ℕ) (i : T ⟶ G) [IsClosedImmersion i.hom.hom.left]
    (hT : Nonempty (yonedaGrpObj T.X ≅ relativeSplitTorusFunctor S r)) :
    ∃ (X : Over S) (q : G.X ⟶ X)
      (e : yoneda.obj X ⋙ uliftFunctor.{u + 1, u} ≅ (torusNormalizerQuotientSheaf i).obj),
      Smooth X.hom ∧ IsQuasiAffineHom X.hom ∧ Smooth q.left ∧ Surjective q.left ∧
      Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u} ≫ e.hom =
        torusNormalizerQuotientMap i := by
  sorry

end AlgebraicGeometry
