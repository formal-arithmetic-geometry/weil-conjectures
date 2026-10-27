/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Coordinate frames and projective-line compactifications of split torus torsors

Source: Stacks Project, Tags 023T, 05B2, 0499, 049A, 01OB and 01OE
(blueprint: lem-sfb-split-torus-torsor-frame-geometry).
The records describe the conclusion for actual schemes and tensor inverse images.
They neither choose schemes from existence axioms nor assume the desired geometry.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SplitTorusFrames

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- The canonical tensor inverse image of the structure sheaf.
Source: Stacks, Tags 0096 and 01CA
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def unitComparison {X Z : Scheme.{u}} (h : X ⟶ Z) :
    (tensorPullback h).obj (unit Z) ≅ unit X :=
  (boundaryPullbackComparison h).app (unit Z) ≪≫ pullbackObjUnitIso h

/-- Pull a frame back using the normalized composition comparison.
Source: Stacks, Tags 0096 and 01OB
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def pullFrame {S X U : Scheme.{u}} (A : S.Modules) (f : X ⟶ S)
    (e : unit X ≅ (tensorPullback f).obj A) (h : U ⟶ X) :
    unit U ≅ (tensorPullback (h ≫ f)).obj A :=
  (unitComparison h).symm ≪≫ (tensorPullback h).mapIso e ≪≫
    ((tensorPullbackSectionComp h f).app A).symm

/-- A representing frame scheme, specified by its universal frame and the induced
bijection on every S-scheme. Pullback, rather than an arbitrary bijection, defines
this classification, hence it is natural.
Source: Stacks, Tag 01OB, invertible-quotient interpretation
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
structure FrameModel {S : Scheme.{u}} (A : S.Modules) where
  space : Over S
  frame : unit space.left ≅ (tensorPullback space.hom).obj A
  represents (U : Over S) : Function.Bijective fun a : U ⟶ space ↦
    pullFrame A space.hom frame a.left ≪≫
      eqToIso (congrArg (fun f ↦ (tensorPullback f).obj A) a.w)

/-- The first j coordinate frame factors, including the empty product.
Source: Stacks, Tag 01OB and the fibre-product universal property
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def framesProduct {S : Scheme.{u}} {r : ℕ} (F : Fin r → Over S) (j : Fin (r + 1)) : Over S :=
  ∏ᶜ fun i : Fin j.val ↦ F ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt)⟩

/-- Forget the last coordinate frame in the chosen finite products.
Source: Stacks, Tag 01OB and the fibre-product universal property
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def forget {S : Scheme.{u}} {r : ℕ} (F : Fin r → Over S) (j : Fin r) :
    framesProduct F j.succ ⟶ framesProduct F j.castSucc :=
  Pi.lift fun i : Fin j.val ↦
    Pi.π (fun l : Fin (j.val + 1) ↦ F ⟨l.val, Nat.lt_of_lt_of_le l.isLt
      (Nat.succ_le_of_lt j.isLt)⟩) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- Ordered coordinate characters of the recorded split torus.
Source: Stacks, Tag 049A, coordinate-character construction
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def coordinate (k : Type u) [Field k] :
    (r : ℕ) → Fin r → ((MultiplicativeType.splitTorus k r).X ⟶
      StandardGroupSchemes.multiplicative k)
  | 0, j => Fin.elim0 j
  | n + 1, j => Fin.cases
      (fst (StandardGroupSchemes.multiplicative k) (MultiplicativeType.splitTorus k n).X)
      (fun i ↦ snd (StandardGroupSchemes.multiplicative k)
        (MultiplicativeType.splitTorus k n).X ≫ coordinate k n i) j

/-- Pull the Laurent coordinate back along a point of the split torus.
Source: Stacks, Tags 049A and 022U
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def scalar {k : Type u} [Field k] {r : ℕ} {U : Over (Spec (.of k))}
    (t : U ⟶ (MultiplicativeType.splitTorus k r).X) (j : Fin r) : Γ(U.left, ⊤) :=
  (t ≫ coordinate k r j).left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))

/-- The rank-two module in the quotient convention, with the pulled-back dual.
Source: Stacks, Tag 01OB
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def rankTwo {S : Scheme.{u}} (A : S.Modules) (f : Over S) : f.left.Modules :=
  biprod (unit f.left) ((tensorPullback f.hom).obj (dual A))

/-- Projective-line compactification of one frame step, with its canonical
symmetric algebra, normalized tautological quotient, exact two-isomorphism open,
and the first-summand trivialization.
Source: Stacks, Tags 01OB and 01OE
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
structure Compactification {S : Scheme.{u}} (A : S.Modules)
    (V W : Over S) (q : W ⟶ V) where
  quasiCoherent : (rankTwo A V).IsQuasicoherent
  quotient : @TautologicalQuotient V.left (rankTwo A V) quasiCoherent
  inclusion : W.left ⟶
    (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V) quasiCoherent).relProj
  openImmersion : IsOpenImmersion inclusion
  overBase : inclusion ≫
    (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V)
      quasiCoherent).relProjHom = q.left
  first : unit W.left ≅ (tensorPullback inclusion).obj quotient.line
  first_eq : first.hom =
    (unitComparison inclusion).inv ≫ (tensorPullback inclusion).map
      ((unitComparison
        (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V)
          quasiCoherent).relProjHom).inv ≫
        (tensorPullback
          (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V)
            quasiCoherent).relProjHom).map biprod.inl ≫ quotient.quotient)
  image (U : Scheme.{u})
      (a : U ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V)
        quasiCoherent).relProj) :
    (∃ b : U ⟶ W.left, b ≫ inclusion = a) ↔
      IsIso ((tensorPullback a).map
        ((tensorPullback
          (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V)
            quasiCoherent).relProjHom).map biprod.inl ≫ quotient.quotient)) ∧
      IsIso ((tensorPullback a).map
        ((tensorPullback
          (@SymmetricAlgebraSheaf.gradedAlgebraData V.left (rankTwo A V)
            quasiCoherent).relProjHom).map biprod.inr ≫ quotient.quotient))

/-- Evaluate the universal frame on a morphism over S.
Source: Stacks, Tag 01OB
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def FrameModel.at {S : Scheme.{u}} {A : S.Modules} (F : FrameModel A)
    {U : Over S} (a : U ⟶ F.space) : unit U.left ≅ (tensorPullback U.hom).obj A :=
  pullFrame A F.space.hom F.frame a.left ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj A) a.w)

/-- Smooth, separated and finite type over the field, with separatedness expressed
by the closed diagonal and finite type by its two defining properties.
Source: Stacks, Tags 01V4, 01KU and 01T0
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def Good {k : Type u} [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) : Prop :=
  Smooth f ∧ IsClosedImmersion (pullback.diagonal f) ∧
    LocallyOfFiniteType f ∧ QuasiCompact f

/-- Scalar equivariance for one coordinate frame, on every test scheme.
Source: Stacks, Tags 0499 and 049A
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
def FrameEquivariant {k : Type u} [Field k] (S : Over (Spec (.of k)))
    (Y : Over S.left) (r : ℕ) (j : Fin r) (A : S.left.Modules) (F : FrameModel A)
    (a : Y ⟶ F.space)
    (act : Over.mk (Y.hom ≫ S.hom) ⊗ (MultiplicativeType.splitTorus k r).X ⟶
      Over.mk (Y.hom ≫ S.hom)) : Prop :=
  ∀ (U : Over S.left) (y z : U ⟶ Y)
    (t : (Over.map S.hom).obj U ⟶ (MultiplicativeType.splitTorus k r).X),
    (Over.map S.hom).map z = lift ((Over.map S.hom).map y) t ≫ act →
    (F.at (z ≫ a)).hom = (F.at (y ≫ a)).hom ≫
      ((tensorPullback U.hom).obj A).smulHom (scalar (k := k) (r := r) t j)

/-- All the geometric conclusions, for the fixed input action. The product cones
and forgetful arrows are the actual categorical products over S. Equivariance is
an equality of module maps on Y times T, so holds on all test schemes, including
nonreduced tests. No geometric assertion is hidden in a chosen object.
Source: Stacks, Tags 023T, 05B2, 0499, 049A, 01OB and 01OE
(blueprint: lem-sfb-split-torus-torsor-frame-geometry). -/
structure Geometry {k : Type u} [Field k] (S : Over (Spec (.of k))) (Y : Over S.left)
    (r : ℕ)
    (act : Over.mk (Y.hom ≫ S.hom) ⊗ (MultiplicativeType.splitTorus k r).X ⟶
      Over.mk (Y.hom ≫ S.hom))
 where
  line : Fin r → S.left.Modules
  invertible (j : Fin r) : (line j).IsInvertible
  frames (j : Fin r) : FrameModel (line j)
  comparison : Y ≅ framesProduct (fun j ↦ (frames j).space) (Fin.last r)
  compactification (j : Fin r) : Compactification (line j)
    (framesProduct (fun i ↦ (frames i).space) j.castSucc)
    (framesProduct (fun i ↦ (frames i).space) j.succ)
    (forget (fun i ↦ (frames i).space) j)
  equivariant (j : Fin r) : FrameEquivariant S Y r j (line j) (frames j)
    (comparison.hom ≫ Pi.π (fun i : Fin r ↦ (frames ⟨i.val, i.isLt⟩).space) j) act
  good : Good S.left S.hom →
    (∀ j : Fin (r + 1), Good (framesProduct (fun i ↦ (frames i).space) j).left
      ((framesProduct (fun i ↦ (frames i).space) j).hom ≫ S.hom)) ∧
    (∀ j : Fin r, Good
      (@SymmetricAlgebraSheaf.gradedAlgebraData _
        (rankTwo (line j) (framesProduct (fun i ↦ (frames i).space) j.castSucc))
        (compactification j).quasiCoherent).relProj
      ((@SymmetricAlgebraSheaf.gradedAlgebraData _
        (rankTwo (line j) (framesProduct (fun i ↦ (frames i).space) j.castSucc))
        (compactification j).quasiCoherent).relProjHom ≫
        (framesProduct (fun i ↦ (frames i).space) j.castSucc).hom ≫ S.hom))
  rank_zero : r = 0 → IsIso Y.hom

/-- A faithfully flat finitely presented right split-torus torsor is the product
of its character-frame schemes and has the stated projective-line tower.

Source: Stacks, Tags 023T, 05B2, 0499, 049A, 01OB and 01OE
(blueprint: lem-sfb-split-torus-torsor-frame-geometry).

Proof:
1. By def-pc-fppf-site and lem-trf-fppf-covering-is-fpqc, the flat surjective
   finitely presented singleton is fppf, hence fpqc. The
   torsor isomorphism gives g(y,z) with z=y*g(y,z). Uniqueness and the action
   laws give g(y,w)=g(y,z)g(z,w), as identities of scheme morphisms.
2. By lem-pc-fpqc-descent, descend the trivial line with transition g_i inverse.
   Rank-one local freeness descends. Its frame satisfies e_i(z)=g_i(y,z)e_i(y),
   so the right action becomes positive scalar multiplication on frames.
3. Use lem-trf-projective-bundle-quotient-geometry for P(O plus A dual).
   The locus where both summand quotients are invertible
   is open. Normalize by the first summand; the second then evaluates on a
   unique frame of A. This represents frames, naturally in arbitrary tests.
   The first summand itself gives the asserted trivialization of O(1).
4. The descended frames give Y to their product. After pullback along Y to S
   its inverse is (t,y) to (y*t,y). This inverse descends by fpqc full
   faithfulness in lem-galois-fpqc-morphisms-descend. The character equation
   proves equivariance.
   For rank zero the same descent identifies q with the identity of S.
5. Use def-pc-fibre-product for the successive products over S and
   def-pc-module-pullback for inverse images. Their forgetful arrows compose to the
   structure arrow. Pullback commutes with duals for invertible modules, as
   checked in rank-one bases. Step 3 gives each prescribed compactification.
6. When S is finite type over k, take a finite affine cover trivializing the
   finitely many lines. The frame-product charts have Laurent coordinates;
   projective-line charts add one polynomial variable. They are finite type.
   This argument also covers the empty base and empty product.
7. These charts are opens in affine spaces over smooth opens of S. Apply
   sbc-lem-affine-space-smooth, lem-trf-smooth-composition,
   lem-weil-pbc-smooth-restrict-open-subschemes and
   lem-weil-pbc-smooth-local-on-source to prove smoothness.
8. The projective projections are separated. Each open restriction has diagonal
   a base change of the closed projective diagonal. The diagonal of a composite
   factors through a base change of the base diagonal. Closed immersions are
   preserved by lem-weil-pbc-closed-immersion-base-change and
   lem-weil-pbc-closed-immersion-comp, proving all separatedness claims. -/
theorem split_torus_torsor_frame_geometry
    {k : Type u} [Field k] (S : Over (Spec (.of k))) (Y : Over S.left)
    [Flat Y.hom] [Surjective Y.hom] [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (r : ℕ)
    (act : Over.mk (Y.hom ≫ S.hom) ⊗ (MultiplicativeType.splitTorus k r).X ⟶
      Over.mk (Y.hom ≫ S.hom))
    (hone : ∀ (U : Over (Spec (.of k))) (y : U ⟶ Over.mk (Y.hom ≫ S.hom)),
      lift y (1 : U ⟶ (MultiplicativeType.splitTorus k r).X) ≫ act = y)
    (hmul : ∀ (U : Over (Spec (.of k))) (y : U ⟶ Over.mk (Y.hom ≫ S.hom))
      (t t' : U ⟶ (MultiplicativeType.splitTorus k r).X),
      lift (lift y t ≫ act) t' ≫ act = lift y (t * t') ≫ act)
    (_hinvariant : act.left ≫ Y.hom =
      (fst (Over.mk (Y.hom ≫ S.hom)) (MultiplicativeType.splitTorus k r).X).left ≫
        Y.hom)
    (torsor : ∃ e :
      (Over.mk (Y.hom ≫ S.hom) ⊗ (MultiplicativeType.splitTorus k r).X).left ≅
        pullback Y.hom Y.hom,
      e.hom ≫ pullback.fst _ _ =
        (fst (Over.mk (Y.hom ≫ S.hom)) (MultiplicativeType.splitTorus k r).X).left ∧
      e.hom ≫ pullback.snd _ _ = act.left) :
    Nonempty (Geometry S Y r act) := by
  sorry

end AlgebraicGeometry.SplitTorusFrames
