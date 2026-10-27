module

public import Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import WeilConjectures.AlgebraicGeometry.FormallySmooth
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Character pushouts of split-torus extensions

Source: Stacks Project, groupoids.tex, Tag 049C, and descent.tex, Tag 023T;
the contracted-product and associated-frame calculation in the DAG proof
(blueprint: lem-sfb-split-torus-character-pushout).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SplitTorusCharacterPushout

open Scheme.Modules SplitTorusFrames

/-- The right action (g,z)t = (g i(t), chi(t) inverse z), on actual scheme products.
Source: Stacks, Tag 049C, contracted-product calculation in the node
(blueprint: lem-sfb-split-torus-character-pushout). -/
def action {k : Type u} [Field k] (r : ℕ) (G : Grp (Over (Spec (.of k))))
    (i : MultiplicativeType.splitTorus k r ⟶ G)
    (chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k) :
    (G.X ⊗ StandardGroupSchemes.multiplicative k) ⊗
      (MultiplicativeType.splitTorus k r).X ⟶
        G.X ⊗ StandardGroupSchemes.multiplicative k :=
  lift
    ((fst (G.X ⊗ StandardGroupSchemes.multiplicative k)
      (MultiplicativeType.splitTorus k r).X ≫ fst G.X
        (StandardGroupSchemes.multiplicative k)) *
      (snd (G.X ⊗ StandardGroupSchemes.multiplicative k)
        (MultiplicativeType.splitTorus k r).X ≫ i.hom.hom))
    (((snd (G.X ⊗ StandardGroupSchemes.multiplicative k)
      (MultiplicativeType.splitTorus k r).X ≫ chi)⁻¹) *
      (fst (G.X ⊗ StandardGroupSchemes.multiplicative k)
        (MultiplicativeType.splitTorus k r).X ≫
          snd G.X (StandardGroupSchemes.multiplicative k)))

/-- The orbit presheaf: the pointwise coequalizer of action and projection.
We lift sets one universe so that sheafification on the bounded big site exists.
Source: Stacks, Tag 049C, explicit quotient in the node
(blueprint: lem-sfb-split-torus-character-pushout). -/
def orbitPresheaf {k : Type u} [Field k] (r : ℕ) (G : Grp (Over (Spec (.of k))))
    (i : MultiplicativeType.splitTorus k r ⟶ G)
    (chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1) :=
  coequalizer (uliftYoneda.{u + 1}.map (action r G i chi))
    (uliftYoneda.{u + 1}.map (fst (G.X ⊗ StandardGroupSchemes.multiplicative k)
      (MultiplicativeType.splitTorus k r).X))

/-- E_chi is the fppf sheafification of the actual orbit presheaf.
Source: Stacks, Tags 049C and 00W1, explicit quotient in the node
(blueprint: lem-sfb-split-torus-character-pushout). -/
def pushoutSheaf {k : Type u} [Field k] (r : ℕ) (G : Grp (Over (Spec (.of k))))
    (i : MultiplicativeType.splitTorus k r ⟶ G)
    (chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k) :
    (Over (Spec (.of k)))ᵒᵖ ⥤ Type (u + 1) :=
  sheafify (Scheme.fppfTopology.over (Spec (.of k))) (orbitPresheaf r G i chi)

/-- The canonical quotient arrow (g,z) to [g,z], including sheafification.
Source: Stacks, Tags 049C and 00W1
(blueprint: lem-sfb-split-torus-character-pushout). -/
def classMap {k : Type u} [Field k] (r : ℕ) (G : Grp (Over (Spec (.of k))))
    (i : MultiplicativeType.splitTorus k r ⟶ G)
    (chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k) :
    uliftYoneda.{u + 1}.obj (G.X ⊗ StandardGroupSchemes.multiplicative k) ⟶
      pushoutSheaf r G i chi :=
  coequalizer.π (uliftYoneda.{u + 1}.map (action r G i chi))
    (uliftYoneda.{u + 1}.map (fst (G.X ⊗ StandardGroupSchemes.multiplicative k)
      (MultiplicativeType.splitTorus k r).X)) ≫
    toSheafify (Scheme.fppfTopology.over (Spec (.of k))) (orbitPresheaf r G i chi)

end AlgebraicGeometry.SplitTorusCharacterPushout

namespace AlgebraicGeometry.SplitTorusCharacterPushout

open Scheme.Modules SplitTorusFrames

/-- The point [g,z] of a fixed representing scheme, transported from the canonical
quotient arrow, rather than an arbitrary point map.
Source: Stacks, Tag 049C, explicit quotient in the node
(blueprint: lem-sfb-split-torus-character-pushout). -/
def bracket {k : Type u} [Field k] {r : ℕ} {G : Grp (Over (Spec (.of k)))}
    {i : MultiplicativeType.splitTorus k r ⟶ G}
    {chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k}
    {E : Over (Spec (.of k))}
    (rep : uliftYoneda.{u + 1}.obj E ≅ pushoutSheaf r G i chi)
    {U : Over (Spec (.of k))} (g : U ⟶ G.X)
    (z : U ⟶ StandardGroupSchemes.multiplicative k) : U ⟶ E :=
  (rep.inv.app (op U) ((classMap r G i chi).app (op U) ⟨lift g z⟩)).down

/-- Regard a point over B as a point over k, using the structural equality of p.
Source: Stacks, Tag 001D, composition of morphisms over a base
(blueprint: lem-sfb-split-torus-character-pushout). -/
def pointOverBase {k : Type u} [Field k] {X B : Over (Spec (.of k))}
    (p : X ⟶ B) {U : Over B.left} (x : U ⟶ Over.mk p.left) :
    (Over.map B.hom).obj U ⟶ X :=
  Over.homMk x.left
    ((congrArg (fun f ↦ x.left ≫ f) p.w).symm.trans
      ((Category.assoc x.left p.left B.hom).symm.trans
        (congrArg (fun f ↦ f ≫ B.hom) x.w)))

attribute [irreducible] action orbitPresheaf pushoutSheaf classMap bracket pointOverBase

/-- Regard a commuting triangle over S as a morphism over B.
Source: Stacks, Tag 001D, composition of morphisms over a base
(blueprint: lem-sfb-split-torus-character-pushout). -/
def sectionOver {S : Scheme.{u}} {X E B : Over S} (q : X ⟶ B) (p : E ⟶ B)
    (a : X ⟶ E) (h : a.left ≫ p.left = q.left) :
    Over.mk q.left ⟶ Over.mk p.left :=
  Over.homMk (U := Over.mk q.left) (V := Over.mk p.left) a.left h

/-- The complete conclusion for the fixed quotient construction. Representability,
group law, exact sequence, equivariant line and canonical frame are all retained.
Source: Stacks, Tags 049C and 023T, associated-frame calculation in the node
(blueprint: lem-sfb-split-torus-character-pushout). -/
def Geometry {k : Type u} [Field k] (r : ℕ)
    (G B : Grp (Over (Spec (.of k))))
    (i : MultiplicativeType.splitTorus k r ⟶ G) (q : G ⟶ B)
    (chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k) :
    Prop :=
  ∃ (E : Grp (Over (Spec (.of k))))
    (rep : uliftYoneda.{u + 1}.obj E.X ≅ pushoutSheaf r G i chi)
    (j : StandardGroupSchemes.multiplicative k ⟶ E.X) (p : E.X ⟶ B.X)
    (M : B.X.left.Modules) (F : FrameModel M)
    (e : F.space ≅ Over.mk p.left)
    (a : G.X ⟶ E.X) (ha : a.left ≫ p.left = q.hom.hom.left),
    IsCommMonObj E.X ∧ Good E.X.left E.X.hom ∧
    (∀ (U : Over (Spec (.of k))) (g h : U ⟶ G.X)
      (z w : U ⟶ StandardGroupSchemes.multiplicative k),
      bracket rep (g * h) (z * w) = bracket rep g z * bracket rep h w) ∧
    IsMonHom j ∧ IsMonHom p ∧
    (∀ (U : Over (Spec (.of k))) (z : U ⟶ StandardGroupSchemes.multiplicative k),
      z ≫ j = bracket rep 1 z) ∧
    (∀ (U : Over (Spec (.of k))) (g : U ⟶ G.X)
      (z : U ⟶ StandardGroupSchemes.multiplicative k),
      bracket rep g z ≫ p = g ≫ q.hom.hom) ∧
    IsPullback j (toUnit (StandardGroupSchemes.multiplicative k)) p η[B.X] ∧
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k)))
      (yoneda.map p) ∧
    M.IsInvertible ∧
    (∀ (U : Over B.X.left) (x y : U ⟶ Over.mk p.left)
      (z : (Over.map B.X.hom).obj U ⟶ StandardGroupSchemes.multiplicative k),
      pointOverBase p y = pointOverBase p x * (z ≫ j) →
      (F.at (y ≫ e.inv)).hom = (F.at (x ≫ e.inv)).hom ≫
        ((tensorPullback U.hom).obj M).smulHom
          (z.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
            (LaurentPolynomial.T 1)))) ∧
    (∀ (U : Over (Spec (.of k))) (g : U ⟶ G.X), g ≫ a = bracket rep g 1) ∧
    (∃ sigma : unit G.X.left ≅ (tensorPullback q.hom.hom.left).obj M,
      sigma = F.at (sectionOver q.hom.hom p a ha ≫ e.inv)) ∧
    (∀ (U : Over B.X.left) (g h : U ⟶ Over.mk q.hom.hom.left)
      (t : (Over.map B.X.hom).obj U ⟶ (MultiplicativeType.splitTorus k r).X),
      pointOverBase q.hom.hom h = pointOverBase q.hom.hom g * (t ≫ i.hom.hom) →
      (F.at (h ≫ sectionOver q.hom.hom p a ha ≫ e.inv)).hom =
        (F.at (g ≫ sectionOver q.hom.hom p a ha ≫ e.inv)).hom ≫
          ((tensorPullback U.hom).obj M).smulHom
            ((t ≫ chi).left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
              (LaurentPolynomial.T 1))))

/-- Character pushout of a smooth separated commutative finite-type group extension.

Source: Stacks, groupoids.tex, Tag 049C, and descent.tex, Tag 023T;
the contracted-product refinement and positive character sign are the explicit
calculation recorded in the node
(blueprint: lem-sfb-split-torus-character-pushout).

Proof:
1. G_m is affine and finitely presented, with coordinate ring A[x,y]/(xy-1).
   It is smooth because a unit modulo a square-zero ideal lifts to a unit:
   if uv=1+a then v(1-a) is an inverse. Affine permanence gives qc and qs.
2. Choose fppf-local lifts s of B-sections to G. The kernel condition gives
   g=s i(t) uniquely. The coordinate [s i(t),z] to chi(t)z is invariant under
   the stated action, and has inverse z to [s,z]. Local representatives of
   sheafification and descent of representable morphisms give torsor charts.
3. Apply smooth affine group torsor representability over B to obtain a smooth
   affine surjective representing scheme. Smoothness and affineness give finite
   presentation, and the action identifies E times G_m with E times_B E.
4. Apply split-torus frame geometry in rank one to get the invertible module
   and equivariant B-isomorphism with its frame model. Since B is smooth,
   separated and finite type, the representing scheme has these properties.
5. The quotient group law [g,z][h,w]=[gh,zw] is well-defined by commutativity.
   Finite-product preservation by sheafification transports the group identities;
   Yoneda represents them. The maps z to [1,z] and [g,z] to q(g) are homomorphisms.
   The identity fibre chart identifies the kernel with G_m, and local lifts
   of B-sections prove local surjectivity. Multiplication by [1,z] is scalar action.
6. The class [g,1] is a frame of q^*M. The orbit relation gives
   [g i(t),1]=[g,chi(t)]. Equivariance gives sigma(g i(t))=chi(t)sigma(g),
   on every test scheme, hence on G times T with normalized pullback comparisons. -/
theorem character_pushout
    {k : Type u} [Field k] (r : ℕ) (G B : Grp (Over (Spec (.of k))))
    [IsCommMonObj G.X] [IsCommMonObj B.X]
    [Smooth G.X.hom] [Smooth B.X.hom]
    [IsClosedImmersion (pullback.diagonal G.X.hom)]
    [IsClosedImmersion (pullback.diagonal B.X.hom)]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType B.X.hom] [QuasiCompact B.X.hom]
    (i : MultiplicativeType.splitTorus k r ⟶ G) (q : G ⟶ B)
    (_hkernel : IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus k r).X)
      q.hom.hom η[B.X])
    (_hlocallySurjective : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (Spec (.of k))) (yoneda.map q.hom.hom))
    (chi : (MultiplicativeType.splitTorus k r).X ⟶ StandardGroupSchemes.multiplicative k)
    [IsMonHom chi] : Geometry r G B i q chi := by
  sorry

end AlgebraicGeometry.SplitTorusCharacterPushout
