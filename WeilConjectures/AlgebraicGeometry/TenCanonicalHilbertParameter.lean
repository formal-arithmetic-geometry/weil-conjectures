/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.ProjectiveHilbertPolynomialRepresentability
public import WeilConjectures.AlgebraicGeometry.NodalDualizingDatum
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoOpen
import WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle
import WeilConjectures.AlgebraicGeometry.PicardDiagonalLocallyClosed
import WeilConjectures.AlgebraicGeometry.ProperFlatGlobalSections
import WeilConjectures.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # The ten-canonical Hilbert parameter and projective-frame torsors

Source: Morrison, arXiv:0810.2340, §3.3, Definition 9 and pp.15--17; arbitrary-field
projective-frame descent as detailed in the DAG proof.
(blueprint: lem-sfb-ten-canonical-hilbert-parameter)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry CategoryTheory.MonObj

namespace AlgebraicGeometry.TenCanonicalHilbert

/-- The ordered homogeneous coordinates, including every genus allowed by the node.
Source: Morrison §3.3 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
abbrev Coordinates (g : ℕ) := ULift.{u} (Fin ((19 * (g - 1) - 1) + 1))

/-- Standard projective space over a test scheme, with its structural projection.
Source: Morrison Definition 9 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def standard (g : ℕ) (T : Scheme.{u}) : Over T :=
  Over.mk (ℙ(Coordinates.{u} g; T) ↘ T)

/-- The exact linear Hilbert polynomial, with rational coefficients and integral values.
Source: Morrison §3.3 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def polynomial (g : ℕ) : Polynomial ℚ :=
  Polynomial.C (20 * ((g : ℚ) - 1)) * Polynomial.X + Polynomial.C (1 - (g : ℚ))

/-- Degree-zero direct image of the tenth tensor power; no module is selected from
an existence assertion. Source: Morrison §3.3; Stacks 0E6R
(blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def sections {S : Scheme.{u}} {g : ℕ} (X : StablePointedModuli S g 0)
    (omega : X.curve.Modules) : X.base.left.Modules :=
  (Scheme.Modules.pushforward X.projection).obj (omega.tensorPow 10)

/-- Evaluation is the actual normalized tensor-pullback counit.
Source: Stacks 01OA (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def evaluation {S : Scheme.{u}} {g : ℕ} (X : StablePointedModuli S g 0)
    (omega : X.curve.Modules) :
    (Scheme.Modules.tensorPullback X.projection).obj (sections X omega) ⟶
      omega.tensorPow 10 :=
  (Scheme.Modules.tensorPullbackSectionAdjunction X.projection).counit.app (omega.tensorPow 10)

/-- The canonical quotient projective bundle of a supplied quasi-coherent module.
Source: Stacks 01OA (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def bundle {T : Scheme.{u}} (V : T.Modules) (hV : V.IsQuasicoherent) : Over T :=
  Over.mk (@SymmetricAlgebraSheaf.gradedAlgebraData T V hV).relProjHom

/-- All properties of the complete relative ten-canonical series. The adjunction
line is identified by the existing Jacobian-normalized nodal dualizing datum.
The base-change arrow is the existing adjoint-defined module base-change arrow.
Source: Morrison Definition 9; Stacks 0E6R, 01OA
(blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
structure Series {S : Scheme.{u}} {g : ℕ} (X : StablePointedModuli S g 0) where
  omega : X.curve.Modules
  dualizing : NodalDualizingDatum X.projection omega
  quasicoherent : (sections X omega).IsQuasicoherent
  rank : (sections X omega).IsFiniteLocallyFreeOfRank (19 * (g - 1))
  evaluation_surjective : Epi (evaluation X omega)
  quotient : @ProjectiveBundleQuotientGeometry.TautologicalQuotient
    X.base.left (sections X omega) quasicoherent
  embedding : X.curve ⟶ (bundle (sections X omega) quasicoherent).left
  commutes : embedding ≫ (bundle (sections X omega) quasicoherent).hom = X.projection
  classifies : ProjectiveBundleQuotientGeometry.Classifies quotient X.projection
    (omega.tensorPow 10) (evaluation X omega) embedding
  closed : IsClosedImmersion embedding
  base_change : ∀ (T : Scheme.{u}) (a : T ⟶ X.base.left),
    IsIso (Scheme.Modules.moduleBaseChangeMap X.projection
      (pullback.snd X.projection a) a (pullback.fst X.projection a)
      pullback.condition (omega.tensorPow 10))

/-- A projective frame after an arbitrary base change, not a vector-space basis.
Source: Morrison pp.15--16; EGA II 4.2.3
(blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
abbrev Frame {S : Scheme.{u}} {g : ℕ} {X : StablePointedModuli S g 0}
    (D : Series X) {T : Scheme.{u}} (a : T ⟶ X.base.left) :=
  (Over.pullback a).obj (bundle (sections X D.omega) D.quasicoherent) ≅ standard g T

/-- Evaluation pulled back to the actual fibre product, before applying its frame.
Source: Stacks 01OA (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def baseEmbedding {S : Scheme.{u}} {g : ℕ} {X : StablePointedModuli S g 0}
    (D : Series X) {T : Scheme.{u}} (a : T ⟶ X.base.left) :
    pullback X.projection a ⟶
      ((Over.pullback a).obj (bundle (sections X D.omega) D.quasicoherent)).left :=
  pullback.map _ _ _ _ D.embedding (𝟙 T) (𝟙 X.base.left)
    (by simpa using D.commutes.symm) (by simp)

/-- Scheme actions use Mathlib's internal monoid actions in the slice category.
Source: Morrison §3.3 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
abbrev Action {S : Scheme.{u}} (G : Grp (Over S)) (J : Over S) := ModObj G.X J

/-- The scheme action on test-valued points, evaluated through the categorical product.
Source: Morrison §3.3 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def Action.act {S : Scheme.{u}} {G : Grp (Over S)} {J : Over S} (A : Action G J)
    (T : Over S) (a : T ⟶ G.X) (x : T ⟶ J) : T ⟶ J :=
  CartesianMonoidalCategory.lift a x ≫ A.smul

/-- An equivariant scheme torsor over a variable base, with its map to J. Local
triviality is fppf; simple transitivity is tested over every scheme. In particular
this definition includes torsors that were not given with Zariski sections.
Source: Morrison p.17 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
structure Pair {S : Scheme.{u}} {G : Grp (Over S)} {J : Over S} (A : Action G J) where
  base : Over S
  space : Over S
  projection : space ⟶ base
  action : Action G space
  commutes : ∀ (T : Over S) (a : T ⟶ G.X) (x : T ⟶ space),
    action.act T a x ≫ projection = x ≫ projection
  transitive : ∀ (T : Over S) (x y : T ⟶ space),
    x ≫ projection = y ≫ projection → ∃! a : T ⟶ G.X, action.act T a x = y
  local_sections : ∃ (U : Over S) (p : U ⟶ base),
    Surjective p.left ∧ Flat p.left ∧ LocallyOfFinitePresentation p.left ∧
      ∃ s : U ⟶ space, s ≫ projection = p
  map : space ⟶ J
  equivariant : ∀ (T : Over S) (a : T ⟶ G.X) (x : T ⟶ space),
    action.act T a x ≫ map = A.act T a (x ≫ map)

/-- Arrows of quotient pairs are actual equivariant maps over their base map.
In a fibre their invertible arrows are precisely equivariant torsor isomorphisms.
Source: Morrison p.17 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
@[ext]
structure Pair.Hom {S : Scheme.{u}} {G : Grp (Over S)} {J : Over S} {A : Action G J}
    (P Q : Pair A) where
  base : P.base ⟶ Q.base
  space : P.space ⟶ Q.space
  commutes : space ≫ Q.projection = P.projection ≫ base
  equivariant : ∀ (T : Over S) (a : T ⟶ G.X) (x : T ⟶ P.space),
    P.action.act T a x ≫ space = Q.action.act T a (x ≫ space)
  map : space ≫ Q.map = P.map

/-- Composition of equivariant maps defines the total category of quotient pairs.
Source: Morrison p.17 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
instance {S : Scheme.{u}} {G : Grp (Over S)} {J : Over S} {A : Action G J} :
    Category (Pair A) where
  Hom := Pair.Hom
  id P := ⟨𝟙 P.base, 𝟙 P.space, by simp, by intros; simp, by simp⟩
  comp f h := ⟨f.base ≫ h.base, f.space ≫ h.space, by
    rw [Category.assoc, h.commutes, ← Category.assoc, f.commutes, Category.assoc], by
    intros T a x
    rw [← Category.assoc, f.equivariant, h.equivariant, Category.assoc], by
    rw [Category.assoc, h.map, f.map]⟩
  id_comp f := Pair.Hom.ext (by simp) (by simp)
  comp_id f := Pair.Hom.ext (by simp) (by simp)
  assoc f h l := Pair.Hom.ext (by simp) (by simp)

/-- The quotient category lies over the category of base schemes.
Source: Morrison p.17 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def Pair.forget {S : Scheme.{u}} {G : Grp (Over S)} {J : Over S} (A : Action G J) :
    Pair A ⥤ Over S where
  obj P := P.base
  map f := f.base

/-- Zariski local triviality, with no nonempty-base hypothesis.
Source: Morrison pp.15--17 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def Pair.IsZariskiLocallyTrivial {S : Scheme.{u}} {G : Grp (Over S)} {J : Over S}
    {A : Action G J} (P : Pair A) : Prop :=
  ∀ t : P.base.left, ∃ (U : P.base.left.Opens) (_ : t ∈ U)
    (s : U.toScheme ⟶ P.space.left), s ≫ P.projection.left = U.ι

/-- A polynomial component of the recorded projective Hilbert representation.
The component factorization property quantifies over all test schemes, not merely
geometric points. Source: Grothendieck, Bourbaki Expose 221, §3; Morrison §3.3
(blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
structure Hilbert (k : Type u) [Field k] (g : ℕ) where
  H : Over (Spec (.of k))
  representation : (properHilbertPresheaf (standard g (Spec (.of k))).hom).RepresentableBy H
  HP : NumericalHilbertPolynomial → Over (Spec (.of k))
  inclusion : ∀ P, HP P ⟶ H
  index : NumericalHilbertPolynomial
  index_eq : index.1 = polynomial g
  coproduct : Nonempty (IsColimit (Cofan.mk H inclusion))
  projective : ∀ P, IsHProjective (HP P).hom
  finite_type : ∀ P, LocallyOfFiniteType (HP P).hom ∧ QuasiCompact (HP P).hom
  component : ∀ (P : NumericalHilbertPolynomial) (T : Over (Spec (.of k))) (b : T ⟶ H),
    HasProjectiveFibreHilbertPolynomial (standard g (Spec (.of k))).hom
      (𝟙 (standard g (Spec (.of k))).left) T (representation.homEquiv b).1 P.1 ↔
        ∃! l : T ⟶ HP P, l ≫ inclusion P = b

/-- The actual ideal of a point of the chosen locally closed Hilbert locus.
Source: Morrison Definition 9 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def Hilbert.ideal {k : Type u} [Field k] {g : ℕ} (H : Hilbert k g)
    {J T : Over (Spec (.of k))} (j : J ⟶ H.HP H.index) (b : T ⟶ J) :=
  (H.representation.homEquiv (b ≫ j ≫ H.inclusion H.index)).1

/-- A frame classifies a Hilbert point exactly when its evaluation embedding is
that closed family, with the same structural maps. Thus no arbitrary bijection
between parameter points and curves can satisfy this condition.
Source: Morrison Definition 9 (blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
def Hilbert.Classifies {k : Type u} [Field k] {g : ℕ} (H : Hilbert k g)
    {J : Over (Spec (.of k))} (j : J ⟶ H.HP H.index)
    {X : StablePointedModuli (Spec (.of k)) g 0} (D : Series X)
    {T : Over (Spec (.of k))} (a : T ⟶ X.base) (phi : Frame D a.left) (b : T ⟶ J) : Prop :=
  ∃! c : pullback X.projection a.left ≅ (H.ideal j b).subscheme,
    c.hom ≫ (H.ideal j b).subschemeι ≫
        pullback.fst (standard g (Spec (.of k))).hom T.hom =
      baseEmbedding D a.left ≫ phi.hom.left ≫ ProjectiveSpace.map (Coordinates g) T.hom ∧
    c.hom ≫ (H.ideal j b).subschemeι ≫
        pullback.snd (standard g (Spec (.of k))).hom T.hom = pullback.snd X.projection a.left

/-- The complete presentation. PGL is fixed by its automorphism functor and its
composition law, so its action is not an arbitrary abstract group action.
The equivalence is an equivalence of total categories over Sch/k, hence is natural
on every base change and preserves all automorphisms. Its objects are normalized
by the actual frame functor and its arrows by frame-induced curve maps.
Source: Morrison §3.3, Definition 9 and pp.15--17
(blueprint: lem-sfb-ten-canonical-hilbert-parameter). -/
structure Presentation (k : Type u) [Field k] (g : ℕ) where
  hilbert : Hilbert k g
  J : Over (Spec (.of k))
  inclusion : J ⟶ hilbert.HP hilbert.index
  locally_closed : IsImmersion inclusion.left
  G : Grp (Over (Spec (.of k)))
  automorphisms : ∀ T : Over (Spec (.of k)),
    (T ⟶ G.X) ≃* Aut (standard g T.left)
  automorphisms_natural : ∀ {T U : Over (Spec (.of k))} (a : U ⟶ T) (h : T ⟶ G.X),
    ProjectiveSpace.map (Coordinates g) a.left ≫ (automorphisms T h).hom.left =
      (automorphisms U (a ≫ h)).hom.left ≫ ProjectiveSpace.map (Coordinates g) a.left
  action : Action G J
  series : ∀ X : StablePointedModuli (Spec (.of k)) g 0, Series X
  equivalence : StablePointedModuli (Spec (.of k)) g 0 ≌ Pair action
  commutes : equivalence.functor ⋙ Pair.forget action =
    StablePointedModuli.forget (Spec (.of k)) g 0
  frame_base : ∀ X : StablePointedModuli (Spec (.of k)) g 0,
    (equivalence.functor.obj X).base = X.base
  frames : ∀ (X : StablePointedModuli (Spec (.of k)) g 0)
    (T : Over (Spec (.of k))) (a : T ⟶ X.base),
    {s : T ⟶ (equivalence.functor.obj X).space //
      s ≫ (equivalence.functor.obj X).projection ≫ eqToHom (frame_base X) = a} ≃
        Frame (series X) a.left
  frames_equivariant : ∀ (X : StablePointedModuli (Spec (.of k)) g 0)
    (T : Over (Spec (.of k))) (a : T ⟶ X.base) (h : T ⟶ G.X)
    (s : T ⟶ (equivalence.functor.obj X).space)
    (hs : s ≫ (equivalence.functor.obj X).projection ≫ eqToHom (frame_base X) = a)
    (ht : (equivalence.functor.obj X).action.act T h s ≫
      (equivalence.functor.obj X).projection ≫ eqToHom (frame_base X) = a),
    frames X T a ⟨(equivalence.functor.obj X).action.act T h s, ht⟩ =
      frames X T a ⟨s, hs⟩ ≪≫ automorphisms T h
  frames_classify : ∀ (X : StablePointedModuli (Spec (.of k)) g 0)
    (T : Over (Spec (.of k))) (a : T ⟶ X.base)
    (s : T ⟶ (equivalence.functor.obj X).space)
    (hs : s ≫ (equivalence.functor.obj X).projection ≫ eqToHom (frame_base X) = a),
    hilbert.Classifies inclusion (series X) a (frames X T a ⟨s, hs⟩)
      (s ≫ (equivalence.functor.obj X).map)
  represents : ∀ (X : StablePointedModuli (Spec (.of k)) g 0)
    (T : Over (Spec (.of k))) (a : T ⟶ X.base) (phi : Frame (series X) a.left),
    ∃! b : T ⟶ J, hilbert.Classifies inclusion (series X) a phi b
  all_points : ∀ (T : Over (Spec (.of k))) (b : T ⟶ J),
    ∃ (X : StablePointedModuli (Spec (.of k)) g 0) (a : T ⟶ X.base)
      (_ha : IsIso a) (phi : Frame (series X) a.left),
      hilbert.Classifies inclusion (series X) a phi b
  frames_natural : ∀ (X : StablePointedModuli (Spec (.of k)) g 0)
    (T U : Over (Spec (.of k))) (a : T ⟶ X.base) (v : U ⟶ T)
    (s : T ⟶ (equivalence.functor.obj X).space)
    (hs : s ≫ (equivalence.functor.obj X).projection ≫ eqToHom (frame_base X) = a)
    (ht : (v ≫ s) ≫ (equivalence.functor.obj X).projection ≫
      eqToHom (frame_base X) = v ≫ a),
    (frames X U (v ≫ a) ⟨v ≫ s, ht⟩).hom.left ≫
        ProjectiveSpace.map (Coordinates g) v.left =
      pullback.map _ _ _ _ (𝟙 _) v.left (𝟙 _)
        (by simp) (by simp) ≫ (frames X T a ⟨s, hs⟩).hom.left
  arrows : ∀ {X Y : StablePointedModuli (Spec (.of k)) g 0} (f : X ⟶ Y)
    (T : Over (Spec (.of k))) (a : T ⟶ X.base) (b : T ⟶ Y.base)
    (s : T ⟶ (equivalence.functor.obj X).space)
    (t : T ⟶ (equivalence.functor.obj Y).space)
    (hs : s ≫ (equivalence.functor.obj X).projection ≫ eqToHom (frame_base X) = a)
    (ht : t ≫ (equivalence.functor.obj Y).projection ≫ eqToHom (frame_base Y) = b)
    (_hst : s ≫ (equivalence.functor.map f).space = t)
    (c : pullback X.projection a.left ⟶ pullback Y.projection b.left)
    (_hc : c ≫ pullback.fst Y.projection b.left =
      pullback.fst X.projection a.left ≫ f.map)
    (_hb : c ≫ pullback.snd Y.projection b.left = pullback.snd X.projection a.left),
    c ≫ baseEmbedding (series Y) b.left ≫ (frames Y T b ⟨t, ht⟩).hom.left =
      baseEmbedding (series X) a.left ≫ (frames X T a ⟨s, hs⟩).hom.left
  hyperplane_twist : ∀ (X : StablePointedModuli (Spec (.of k)) g 0)
    (T : Over (Spec (.of k))) (a : T ⟶ X.base) (phi : Frame (series X) a.left),
    ∃ (N : T.left.Modules) (_hN : N.IsInvertible),
      Nonempty ((Scheme.Modules.tensorPullback
        (baseEmbedding (series X) a.left ≫ phi.hom.left)).obj
          (ProjectiveSpace.twist (Coordinates g) T.left 1) ≅
        (Scheme.Modules.tensorPullback (pullback.fst X.projection a.left)).obj
          ((series X).omega.tensorPow 10) ⊗
        (Scheme.Modules.tensorPullback (pullback.snd X.projection a.left)).obj N)
  euler_polynomial : ∀ (T : Over (Spec (.of k))) (b : T ⟶ J) (t : T.left) (m : ℤ),
    ((Scheme.Modules.tensorPullback
      ((hilbert.ideal inclusion b).subschemeι ≫
        pullback.fst (standard g (Spec (.of k))).hom T.hom)).obj
      (ProjectiveSpace.twist (Coordinates g) (Spec (.of k)) m)).eulerCharFiber
        ((hilbert.ideal inclusion b).subschemeι ≫
          pullback.snd (standard g (Spec (.of k))).hom T.hom) t =
      20 * ((g : ℤ) - 1) * m + 1 - (g : ℤ)
  zariski : ∀ X : StablePointedModuli (Spec (.of k)) g 0,
    (equivalence.functor.obj X).IsZariskiLocallyTrivial

end AlgebraicGeometry.TenCanonicalHilbert

namespace AlgebraicGeometry

/-- The stable ten-canonical Hilbert locus, its complete evaluation series and
projective-frame torsors present the stable-curve groupoid over every k-scheme.
Source: Morrison §3.3, Definition 9, pp.15--16, and the paragraph after Corollary 11,
p.17; Stacks 0E6R and 0BDP for the arbitrary-base construction.

Proof plan (the thirteen steps of the node):
1. Apply [lem-sfb-projective-hilbert-polynomial-representability] over $\operatorname{Spec}k$ to
obtain $Z=H_P$, projective and finite type, with its universal flat finitely presented closed
family $p:\mathcal C\to Z$. The polynomial in this representability statement agrees with
$\chi(\mathcal C_z,\mathcal O(m))$ by [lem-sfb-flat-projective-hilbert-polynomial-locality]. Since
$d=20(g-1)>0$, [lem-sfb-projective-hilbert-polynomial-dimension] shows that every geometric fibre
has dimension one. Thus the universal family is a family to which the curve-stack open-locus
statement applies.

2. Let $U\subset Z$ be the open subscheme where the universal family is stable of genus $g$, using
[lem-sfb-stable-and-smooth-family-open-loci]. This has the required universal property on every
test scheme, rather than only on geometric points. Over $U$ the line $\omega=\omega_{\mathcal
C/U}$ exists and commutes with all base changes by [lem-sfb-gorenstein-curve-relative-dualizing].
Also $p_*\mathcal O_{\mathcal C}=\mathcal O_U$ universally by
[lem-sc-proper-flat-global-sections], since stable fibres are geometrically reduced and nonempty
connected.

3. For any stable family $f:C\to T$, set $L=\omega_{C/T}^{\otimes10}$. The preceding dualizing
construction and [lem-sfb-stable-curve-pluricanonical-linear-series] show on every geometric fibre
that $H^q(C_t,L_t)=0$ for $q>0$ and $h^0(C_t,L_t)=19(g-1)=r$. Apply the general form of
[sk-thm-picard-perfect] with $i=0$ and this $r$. It gives $V=f_*L$ locally free of rank $r$ and
commuting with every base change, on all of $T$. Its hypotheses hold: $f$ is proper and finitely
presented, and $L$ is finitely presented and flat over $T$ because $f$ is flat and $L$ invertible.
No reducedness or Noetherian hypothesis on $T$ enters.

4. The evaluation $f^*V\to L$ is surjective. Indeed its finite-type cokernel has zero reduction at
each point of $C$, since base change identifies the fibre map with evaluation of the very ample
complete series in [lem-sfb-stable-curve-pluricanonical-linear-series];
[lem-weil-pbc-nakayama-local-generators] then annihilates that cokernel stalk. The quotient
property [lem-trf-projective-bundle-quotient-geometry] gives $i:C\to\mathbf P_T(V)$ pulling back
$\mathcal O(1)$ to $L$. Its geometric fibre maps are closed immersions by the same field lemma.

5. The map $i$ is proper by [lem-weil-pbc-proper-to-separated], since its target is separated by
[lem-trf-projective-bundle-quotient-geometry]. Each fibre of $i$ over a target point is either
empty or a single closed point: this follows by taking the geometric fibre over its image in $T$,
where $i$ is a closed immersion. Thus $i$ is locally quasi-finite, by [pqf-def-quasifinite], and
[pqf-lem-proper-lqf-finite] makes it finite. On an affine target open its algebra map $A\to B$ has
finite cokernel $Q$. By [lem-weil-pbc-affine-pushforward-base-change] its reduction over each
residue field of $T$ is surjective, since the fibre map is closed. At a target point $y$ over $t$,
$Q_y/\mathfrak m_tQ_y=0$; reducing further modulo $\mathfrak m_y$ and applying
[lem-weil-pbc-nakayama-local-generators] gives $Q_y=0$. Hence $A\to B$ is surjective and $i$ is a
closed immersion. This proves the relative embedding assertion by an explicit affine cokernel
argument.

6. On the universal stable curve over $U$, put $M=\mathcal O_{\mathcal C}(1)\otimes\omega^{-10}$.
Apply [lem-sc-picard-diagonal-locally-closed] to this invertible module. Its universal
$p_*\mathcal O=\mathcal O$ hypothesis was checked in step 2. It gives an immersion $K\to U$ of
finite presentation such that a test map $T\to U$ factors through $K$ exactly when $M_T\simeq
f_T^*N$ for a finite locally free $N$ on $T$. Here $N$ has rank one: every fibre of $f_T$ is
nonempty and the pullback has rank one. Thus $N$ is invertible. Conversely, Zariski local
isomorphisms $M_T\simeq\mathcal O$ give a global such $N$: on overlaps their ratios are units on
$C$, and these are exactly base units because $f_*\mathcal O_C=\mathcal O_T$ universally. The
ratios satisfy the cocycle condition, so glue $N$. This is precisely the base-line-twist
condition, including nilpotent test schemes.

7. Over $K$, the module $W=p_*\mathcal O_{\mathcal C}(1)$ is locally free of rank $r$ and commutes
with arbitrary base change: locally trivialize the base line $N$ of step 6 and use step 3. The
coordinate restrictions form a map $\alpha:\mathcal O_K^r\to W$. Let $J\subset K$ be its
isomorphism open, given by [lem-sc-finite-locally-free-map-iso-open]; locally it is the open where
$\det\alpha$ is a unit. Therefore $J\to Z$ is an immersion (a locally closed subscheme). This open
is essential: equality of the hyperplane line with $\omega^{10}$ up to a base twist alone does not
force an embedding into $\mathbf P^{r-1}$ to be a complete linear series. The construction of $K$
and this open both commute with arbitrary base change.

8. Given a stable family and a projective frame $\phi:\mathbf P_T(V)\simeq\mathbf P^{r-1}_T$,
compose its embedding from step 5 with $\phi$. By [lem-sfb-projective-frames-pgl], Zariski locally
$\phi$ is induced by a matrix, and its hyperplane line differs from $L$ by a line from $T$. On
such opens the coordinate restrictions are a basis of $V$, so the resulting Hilbert map factors
through $J$. Its fibre polynomial is $20(g-1)m+1-g$ by
[lem-sfb-stable-curve-pluricanonical-linear-series], which is its coordinate-ring Hilbert
polynomial by [lem-sfb-flat-projective-hilbert-polynomial-locality]; so
[lem-sfb-projective-hilbert-polynomial-representability] puts it in the specified $Z$, not a
different Hilbert component.

9. Conversely a $T$-point of $J$ gives a stable family with $\mathcal O_C(1)\simeq L\otimes f^*N$
and the coordinate isomorphism $\mathcal O_T^r\simeq f_*\mathcal O_C(1)$. Locally trivialize $N$.
The latter isomorphism gives a frame of $V=f_*L$, hence a projective frame. Changing the
trivialization multiplies that frame by a unit from $T$, so its projectivization is unchanged by
[lem-sfb-projective-frames-pgl]; the projective frames glue. Evaluation recovers the original
embedding, so this construction and step 8 are inverse. A different chosen line comparison also
differs by a base unit, by universal $f_*\mathcal O_C=\mathcal O_T$, and gives the same result.
This proves the representing property independently of all auxiliary choices.

10. The two constructions preserve arrows and every base change. An isomorphism of framed families
gives the same embedded closed subscheme; conversely equality of subschemes supplies the unique
compatible curve isomorphism. There are no residual automorphisms of a framed curve: a compatible
automorphism commutes with its closed immersion, hence is the identity, and the completeness
isomorphism in step 7 determines the projective frame uniquely. Change of coordinates in $G$
preserves stability, the base-line-twist condition and invertibility of $\alpha$; hence the
$G$-action on $Z$ preserves $J$ scheme-theoretically by its universal property. Thus the
representing property and $G$-invariance hold over all test schemes, not only over fields.

11. For a stable $C/T$, apply [lem-sfb-projective-frames-pgl] to $V=f_*\omega^{10}$. Its
projective-frame scheme $E$ is a Zariski locally trivial $G$-torsor. The universal frame on $E$
gives $E\to J$ by steps 8--10; changing frame is exactly changing coordinates, so this map is
equivariant. A curve isomorphism induces the canonical map on its dualizing line and on $V$, hence
an equivariant isomorphism of these pairs.

12. For the inverse, let $E\to T$ be a $G$-torsor with an equivariant map to $J$. For an fppf
torsor, [lem-sfb-projective-frames-pgl] supplies an etale trivializing cover; for a Zariski torsor
use its given cover. Pull back the universal stable curves on $J$ to this cover. They are flat
proper finitely presented curves with one-dimensional geometric fibres, hence objects of
$\mathfrak C$ in [lem-sfb-nodal-curve-stack-smooth]. Torsor transitions give coordinate changes
and curve isomorphisms; equivariance gives their cocycle identities. That node explicitly asserts
effective etale descent and the etale sheaf property for isomorphisms. Thus the datum descends to
an algebraic-space curve over $T$, with uniquely descending compatible arrows. The universal
stable-genus-$g$ open of [lem-sfb-stable-and-smooth-family-open-loci] is all of $T$: its pullback
to the surjective cover is the whole cover. That statement ensures the descended curve is a scheme
with the required projective-bundle projectivity. No descent of $\mathcal O(1)$ as a
$G$-linearized line is needed.

13. On the trivializing cover, steps 8--9 identify the given torsor with the projective-frame
torsor of the descended curve. These identifications agree on overlaps: their transitions are
exactly the given projective coordinate changes. They glue to an equivariant isomorphism
preserving the map to $J$. In particular an initially fppf torsor admitting such a map is Zariski
locally trivial. Starting with a stable curve, reconstruction from its local framed embeddings
descends its own identity cocycle and recovers that curve. By the explicit etale sheaf property
for isomorphisms in [lem-sfb-nodal-curve-stack-smooth], compatible curve isomorphisms glue
uniquely; the frame-scheme assertion in [lem-sfb-projective-frames-pgl] does the same for
compatible torsor maps. The two constructions are therefore inverse and fully faithful on arrows.
After any $T^{\prime}\to T$, the pulled-back cover and all evaluation and transition maps are the
same construction for the pullback family; uniqueness of descended isomorphisms gives the natural
comparison. This proves the natural equivalence with $[J/G]$.
(blueprint: lem-sfb-ten-canonical-hilbert-parameter) -/
theorem ten_canonical_hilbert_parameter (k : Type u) [Field k] (g : ℕ) (_hg : 2 ≤ g) :
    Nonempty (TenCanonicalHilbert.Presentation k g) := by
  sorry

end AlgebraicGeometry
