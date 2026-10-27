module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry
import WeilConjectures.AlgebraicGeometry.AmplePullback
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FpqcClosedImmersionDescent
import Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.InvariantAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-! # Schematic quotients by relative subtori

Source: independently formulated supporting lemma for Raynaud, Faisceaux amples sur les
schemas en groupes, Chapter VI, sections 1-2, and Chapter IX, section 2.
The original Raynaud reference is marked WANTED by the DAG; the accepted proof is the
explicit ten-step assembly recorded there.
(blueprint: lem-sfb-relatively-ample-subtorus-quotient-schematicity).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A relatively ample smooth commutative group modulo a closed relative torus is a
scheme, and its quotient projection is affine. The presheaf coequalizer is the right-coset
presheaf. The arrow eta is its sheafification unit, expressed by its universal property;
p is exactly its composite with the coset projection. The representing isomorphism
identifies q with that same p. The homomorphism condition on q specifies the group law
induced by multiplying fppf local lifts; these lifts determine the law uniquely.

Source: independently formulated Raynaud supporting lemma, Chapter VI, sections 1-2,
and Chapter IX, section 2 (original reference WANTED).
(blueprint: lem-sfb-relatively-ample-subtorus-quotient-schematicity).

Proof, following the accepted node:
1. On each affine base open W choose the finite etale torus-splitting cover W' supplied
by lem-sfb-normal-torus-finite-etale-splitting. Quotient formation commutes with restriction
because both equality and existence of lifts are fppf local.
2. Commutativity descends multiplication, inverse and unit from local lifts. Translation
by T is free. Apply lem-sfb-free-flat-group-space-quotient to obtain local lifts and the
T-torsor identity; a lift trivializes every scheme test of p.
3. Descend affineness using lem-sfb-space-four-property-fppf-descent and smooth
surjectivity using lem-sfb-space-smooth-surjective-fppf-locality. Smooth atlas open images
are open by lem-sfb-smooth-atlas-open-image and the chartwise smooth calculus.
4. On each integral component of W', lem-sbc-smooth-connected-generic-geometry makes G'
normal integral. Pull back the ample line along the finite base change, using
lem-weil-pbc-pullback-ample-invertible. Apply
lem-sfb-relative-split-torus-invariant-affines to obtain invariant affine opens.
5. Torsor fibres show these opens are saturated. Their quotients are affine invariant
spectra by lem-sfb-affine-free-split-torus-invariants. Glue them using
lem-weil-pbc-glue-schemes and lem-pc-schemes-criterion to represent the quotient over W'.
6. Smoothness descends from G' by lem-sbc-smooth-flat-surjective-source-descent. The
preimage of the diagonal is the inverse image of the closed T' under the difference map;
lem-weil-pbc-closed-immersion-base-change and lem-pc-fpqc-descend-closed-immersion give
separatedness. Surjective images give quasi-compactness; separatedness gives
quasi-separatedness by lem-pc-separated-quasi-separated, hence finite presentation.
7. Apply lem-sfb-affine-normal-connected-group-ample to each resulting group over an
affine integral component. By lem-sc-ample-finite-set-affine every finite subset lies in
an affine open. Finite disjoint unions preserve this property.
8. The quotient sheaf supplies the canonical descent datum over W'/W. Apply
lem-pd-invariant-affine-neighbourhoods and lem-pd-invariant-affine-descent-gluing to make
this datum effective, without presuming that schematicity is etale local on the base.
9. The representing scheme and F have the same equalizer on the finite etale cover;
lem-weil-pbc-fpqc-representable-descent identifies their sheaves over W.
10. Repeat the smoothness, diagonal and finite-presentation arguments on every W and
glue by lem-pc-schemes-criterion. The smooth-locality lemmas identify the global
properties. On every affine test of F, the restrictions to W are affine; descend using
lem-sfb-space-four-property-fppf-descent. The descended group operations are the ones
from step 2. No semiabelian, maximal-torus or generic-fibre hypothesis is used. -/
theorem relatively_ample_subtorus_quotient_schematicity
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Over S) [CommGrpObj G] [Smooth G.hom] [IsSeparated G.hom]
    [LocallyOfFinitePresentation G.hom] [QuasiCompact G.hom]
    [GeometricallyConnected G.hom]
    (hample : ∃ (I : Type u) (W : I → S.Opens),
      (∀ s : S, ∃ i : I, s ∈ W i) ∧
      ∀ i : I, IsAffineOpen (W i) ∧
        ∃ (L : (G.hom ⁻¹ᵁ W i).toScheme.Modules) (hL : L.IsInvertible),
          @Scheme.Modules.IsAmple (G.hom ⁻¹ᵁ W i).toScheme L hL)
    (T : Over S) [GrpObj T] (i : T ⟶ G) [IsMonHom i] [IsClosedImmersion i.left]
    (hT : IsRelativeTorus T)
    (F : AlgebraicSpace S) (p : yoneda.obj G ⟶ F.obj.obj)
    (eta : coequalizer (yoneda.map (fst G T))
      (yoneda.map (lift (fst G T) (snd G T ≫ i) ≫ μ[G])) ⟶ F.obj.obj)
    (hp : coequalizer.π _ _ ≫ eta = p)
    (hF : ∀ Z : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun f : F.obj.obj ⟶ Z.obj ↦ eta ≫ f)) :
    ∃ (H : Over S) (_ : CommGrpObj H) (q : G ⟶ H)
      (e : yoneda.obj H ≅ F.obj.obj),
      IsMonHom q ∧ yoneda.map q ≫ e.hom = p ∧
      Smooth H.hom ∧ IsSeparated H.hom ∧ LocallyOfFinitePresentation H.hom ∧
      QuasiCompact H.hom ∧ QuasiSeparated H.hom ∧ IsAffineHom q.left := by
  sorry

end AlgebraicGeometry
