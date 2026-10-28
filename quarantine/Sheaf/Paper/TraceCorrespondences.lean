/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.GeometricOperations
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.Paper.IntegralFinitePullbackComposition

/-! # Correspondences and supported classes

Source: current Weil blueprint, sec-trace-formula/sk-d-corr (blueprint: sk-d-corr),
with the reviewed DAG's explicit functor-domain conditions.

Correspondences retain their support, both maps over the base, a compactification,
and the supplied exceptional adjunction on full coefficient subcategories. The
coefficient map is an ambient morphism; the support class is constructed from it,
not a further field. No geometric condition is imposed on a general support.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The supplied right adjoint to the actual compactification functor on full
subcategories. The preservation proof just types its restriction; it asserts no
unbounded right adjoint. Source: sk-d-corr, correspondence data (blueprint: sk-d-corr). -/
structure TraceCorrespondenceAdjunction {T Z : Scheme.{u}} {i : T ⟶ Z}
    (cs : Compactification i)
    (PT : ObjectProperty (proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1))))
    (PZ : ObjectProperty (proEtaleDerivedCategory Z (Padic.coefficientExtensionRing l E (n + 1))))
    where
  preserves : ∀ K : PT.FullSubcategory,
    PZ ((sfIntrinsicCompactSupport cs (Padic.coefficientExtensionRing l E (n + 1))).obj K.obj)
  right : PZ.FullSubcategory ⥤ PT.FullSubcategory
  adjunction : PZ.lift
    (PT.ι ⋙ sfIntrinsicCompactSupport cs (Padic.coefficientExtensionRing l E (n + 1)))
      preserves ⊣ right

/-- A correspondence from `(X,K)` to `(Y,L)`, with ordinary leg 2.
The full subcategories contain the displayed objects. Compactifiability is realized
by an actual compactification, and the exceptional functor is its supplied right
adjoint. Source: sk-d-corr, first paragraph (blueprint: sk-d-corr). -/
structure TraceCorrespondence (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    (X Y : Over (Spec (.of F.k)))
    (K : proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E (n + 1))) where
  C : Over (Spec (.of F.k))
  c₁ : C ⟶ Y
  c₂ : C ⟶ X
  compactification : Compactification c₁.left
  sourceDomain : ObjectProperty
    (proEtaleDerivedCategory C.left (Padic.coefficientExtensionRing l E (n + 1)))
  targetDomain : ObjectProperty
    (proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E (n + 1)))
  exceptional : TraceCorrespondenceAdjunction l E n compactification sourceDomain targetDomain
  target_mem : targetDomain L
  pull_mem : sourceDomain ((finiteDerivedPullback l E n c₂.left).obj K)
  u : (finiteDerivedPullback l E n c₂.left).obj K ⟶
    (exceptional.right.obj ⟨L, target_mem⟩).obj

namespace TraceCorrespondence

variable {l E n} {F : FiniteFieldDatum.{u}} {hl : l ≠ F.p} {X Y : Over (Spec (.of F.k))}
  {K : proEtaleDerivedCategory X.left (Padic.coefficientExtensionRing l E (n + 1))}
  {L : proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E (n + 1))}

/-- The product Z is the fibre product over the fixed base.
Source: sk-d-corr, Z (blueprint: sk-d-corr). -/
abbrev product (X Y : Over (Spec (.of F.k))) : Scheme.{u} := pullback Y.hom X.hom

/-- The ordered support map `(c₁,c₂)`; its two projections are the given legs.
Source: sk-d-corr, c (blueprint: sk-d-corr). -/
def support (c : TraceCorrespondence l E n F hl X Y K L) : c.C.left ⟶ product X Y :=
  pullback.lift c.c₁.left c.c₂.left (c.c₁.w.trans c.c₂.w.symm)

/-- Factor exchange over the base, with its inverse retained.
Source: sk-d-corr, tau (blueprint: sk-d-corr). -/
def exchange (X Y : Over (Spec (.of F.k))) : product Y X ≅ product X Y :=
  pullbackSymmetry X.hom Y.hom

/-- The opposite support is tau after the support of the opposite correspondence.
Source: sk-d-corr, bar d (blueprint: sk-d-corr). -/
def oppositeSupport (d : TraceCorrespondence l E n F hl Y X L K) :
    d.C.left ⟶ product X Y := d.support ≫ (exchange X Y).hom

/-- The specified support intersection. Its maps to C, D and the base are the
pullback projections and their composites, retained below.
Source: sk-d-corr, E(C,D) (blueprint: sk-d-corr). -/
def intersection (c : TraceCorrespondence l E n F hl X Y K L)
    (d : TraceCorrespondence l E n F hl Y X L K) : Scheme.{u} :=
  pullback c.support d.oppositeSupport

/-- Projection of the support intersection to C.
Source: sk-d-corr, E(C,D) (blueprint: sk-d-corr). -/
def intersectionFst (c : TraceCorrespondence l E n F hl X Y K L)
    (d : TraceCorrespondence l E n F hl Y X L K) : c.intersection d ⟶ c.C.left :=
  pullback.fst c.support d.oppositeSupport

/-- Projection of the support intersection to D.
Source: sk-d-corr, E(C,D) (blueprint: sk-d-corr). -/
def intersectionSnd (c : TraceCorrespondence l E n F hl X Y K L)
    (d : TraceCorrespondence l E n F hl Y X L K) : c.intersection d ⟶ d.C.left :=
  pullback.snd c.support d.oppositeSupport

/-- The intersection's structure map, without replacing its support by an image.
Source: sk-d-corr, specified structure maps (blueprint: sk-d-corr). -/
def intersectionBase (c : TraceCorrespondence l E n F hl X Y K L)
    (d : TraceCorrespondence l E n F hl Y X L K) : c.intersection d ⟶ Spec (.of F.k) :=
  c.intersectionFst d ≫ c.C.hom

/-- The fixed scheme is the pullback of the diagonal, without separatedness.
Source: sk-d-corr, Fix(c) (blueprint: sk-d-corr). -/
def fixed (c : TraceCorrespondence l E n F hl X X K K) : Scheme.{u} :=
  pullback c.support (pullback.diagonal X.hom)

/-- The fixed inclusion to C, also the equalizer inclusion of the two legs.
Source: sk-d-corr, fixed scheme (blueprint: sk-d-corr). -/
def fixedInclusion (c : TraceCorrespondence l E n F hl X X K K) : c.fixed ⟶ c.C.left :=
  pullback.fst c.support (pullback.diagonal X.hom)

/-- The other fixed-square projection to X.
Source: sk-d-corr, fixed scheme (blueprint: sk-d-corr). -/
def fixedProjection (c : TraceCorrespondence l E n F hl X X K K) : c.fixed ⟶ X.left :=
  pullback.snd c.support (pullback.diagonal X.hom)

/-- The fixed scheme's specified structure map.
Source: sk-d-corr, specified structure maps (blueprint: sk-d-corr). -/
def fixedBase (c : TraceCorrespondence l E n F hl X X K K) : c.fixed ⟶ Spec (.of F.k) :=
  c.fixedInclusion ≫ c.C.hom

end TraceCorrespondence

/-- A class supported on the specified compactifiable map is the ambient Hom
from the support image of its constant unit. No immersion or exceptional adjoint
is required. Source: sk-d-corr, H^0_T(Z,P) (blueprint: sk-d-corr). -/
def TraceSupportedClass {T Z : Scheme.{u}} {i : T ⟶ Z} (cs : Compactification i)
    (P : proEtaleDerivedCategory Z (Padic.coefficientExtensionRing l E (n + 1))) : Type _ :=
  (sfIntrinsicCompactSupport cs (Padic.coefficientExtensionRing l E (n + 1))).obj
    (finiteIntrinsicClosed l E T n).monoidal.tensorUnit ⟶ P

namespace TraceClassOperations

variable {l E n}

/-- The final identification uses the full finite-Tor subcategories even for a
non-geometric support. This is the recorded coefficient predicate on every scheme.
Source: sk-d-corr, extra hypotheses for the Hom identification (blueprint: sk-d-corr). -/
abbrev domain (T : Scheme.{u}) :=
  finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) T

/-- The actual full coefficient category, retaining ambient objects and morphisms.
Source: sk-d-corr, ordinary ambient Hom sets (blueprint: sk-d-corr). -/
abbrev Category (T : Scheme.{u}) := (domain (l := l) (E := E) (n := n) T).FullSubcategory

/-- The given exceptional operations and displayed projection/composition data needed
for the final identification, on arbitrary schemes. The fields `ordinary_mem` and
`pull_mem` express that the displayed ordinary operations are supplied on the full
coefficient subcategories; they are the domain conditions in the node, not a
replacement of any canonical functor by a freely chosen map. `projection` is the
supplied projection formula at the constant unit, composed with its left unitor.
All three support functors are the actual chosen compactification composites.
Source: sk-d-corr, final identification's functor-domain assumptions (blueprint: sk-d-corr). -/
structure Data {X Y Z C : Scheme.{u}} (p₁ : Z ⟶ Y) (p₂ : Z ⟶ X) (c : C ⟶ Z)
    (K : Category (l := l) (E := E) (n := n) X)
    (L : Category (l := l) (E := E) (n := n) Y) where
  cs : Compactification c
  ps : Compactification p₁
  cps : Compactification (c ≫ p₁)
  exceptional : TraceCorrespondenceAdjunction l E n cs (domain C) (domain Z)
  projectionExceptional : TraceCorrespondenceAdjunction l E n ps (domain Z) (domain Y)
  compositeExceptional : TraceCorrespondenceAdjunction l E n cps (domain C) (domain Y)
  ordinary_mem : domain Z ((finiteDerivedPullback l E n p₂).obj K.obj)
  pull_mem : domain C ((finiteDerivedPullback l E n c).obj
    ((finiteDerivedPullback l E n p₂).obj K.obj))
  composition :
    (domain Y).lift ((domain C).ι ⋙
      sfIntrinsicCompactSupport cps (Padic.coefficientExtensionRing l E (n + 1)))
      compositeExceptional.preserves ≅
    (domain Z).lift ((domain C).ι ⋙
      sfIntrinsicCompactSupport cs (Padic.coefficientExtensionRing l E (n + 1)))
      exceptional.preserves ⋙
    (domain Y).lift ((domain Z).ι ⋙
      sfIntrinsicCompactSupport ps (Padic.coefficientExtensionRing l E (n + 1)))
      projectionExceptional.preserves
  projection :
    (finiteIntrinsicClosed l E Z n).tensor.obj
      ((sfIntrinsicCompactSupport cs (Padic.coefficientExtensionRing l E (n + 1))).obj
        (finiteIntrinsicClosed l E C n).monoidal.tensorUnit,
        (finiteDerivedPullback l E n p₂).obj K.obj) ≅
    (sfIntrinsicCompactSupport cs (Padic.coefficientExtensionRing l E (n + 1))).obj
      ((finiteDerivedPullback l E n c).obj ((finiteDerivedPullback l E n p₂).obj K.obj))

/-- The canonical Hom equivalence for the supplied per-map operations, with no
separatedness or finite-type condition on the schemes. For the node take Z to be
Y times_s X, c the ordered support, and p1,p2 its projections. The two exceptional
adjunctions are pasted and compared with the third using the supplied compositor;
no exceptional composition isomorphism is chosen independently.

Source: sk-d-corr, final display (blueprint: sk-d-corr).
The definition uncurries tensor--Hom, uses projection and the unit, passes through
full inclusions and the given exceptional adjunction, then uses ordinary pullback
composition and uniqueness of the composite right adjoint. This is proof steps 5--7
of the node, implemented with existing equivalences and actual comparison maps. -/
def homEquivalence {X Y Z C : Scheme.{u}} (p₁ : Z ⟶ Y) (p₂ : Z ⟶ X) (c : C ⟶ Z)
    (K : Category (l := l) (E := E) (n := n) X)
    (L : Category (l := l) (E := E) (n := n) Y) (D : Data p₁ p₂ c K L) :
    TraceSupportedClass l E n D.cs
      ((finiteIntrinsicDerivedInternalHom l E Z n).obj
        (op ((finiteDerivedPullback l E n p₂).obj K.obj),
          (D.projectionExceptional.right.obj L).obj)) ≃
    ((finiteDerivedPullback l E n (c ≫ p₂)).obj K.obj ⟶
      (D.compositeExceptional.right.obj L).obj) :=
  ((finiteIntrinsicClosed l E Z n).transpose _ _ _).symm |>.trans
    ((Iso.homCongr D.projection (Iso.refl _)).trans
      (((domain Z).fullyFaithfulι.homEquiv
        (X := ⟨_, D.exceptional.preserves ⟨_, D.pull_mem⟩⟩)
        (Y := D.projectionExceptional.right.obj L)).symm.trans
        ((D.exceptional.adjunction.homEquiv ⟨_, D.pull_mem⟩
          (D.projectionExceptional.right.obj L)).trans
          (((domain C).fullyFaithfulι.homEquiv
            (X := ⟨_, D.pull_mem⟩)
            (Y := D.exceptional.right.obj (D.projectionExceptional.right.obj L))).trans
            (Iso.homCongr
              ((Functor.mapDerivedCategoryNatIso
                (sfIntrinsicPullbackComp (Padic.coefficientExtensionRing l E (n + 1))
                  c p₂) ≪≫ Functor.mapDerivedCategoryCompIso _ _).app K.obj).symm
              ((domain C).ι.mapIso
                ((((D.exceptional.adjunction.comp D.projectionExceptional.adjunction
                  ).ofNatIsoLeft D.composition.symm).rightAdjointUniq
                    D.compositeExceptional.adjunction).app L)))))))

/-- The class is the inverse image of u under the exact Hom equivalence. Agreement
at L with the originally supplied exceptional object is retained explicitly.
Source: sk-d-corr, inverse-image class [u] (blueprint: sk-d-corr). -/
def supportedClass {X Y Z C : Scheme.{u}} (p₁ : Z ⟶ Y) (p₂ : Z ⟶ X) (c : C ⟶ Z)
    (K : Category (l := l) (E := E) (n := n) X)
    (L : Category (l := l) (E := E) (n := n) Y) (D : Data p₁ p₂ c K L)
    (V : proEtaleDerivedCategory C (Padic.coefficientExtensionRing l E (n + 1)))
    (agreement : (D.compositeExceptional.right.obj L).obj ≅ V)
    (u : (finiteDerivedPullback l E n (c ≫ p₂)).obj K.obj ⟶ V) :
    TraceSupportedClass l E n D.cs
      ((finiteIntrinsicDerivedInternalHom l E Z n).obj
        (op ((finiteDerivedPullback l E n p₂).obj K.obj),
          (D.projectionExceptional.right.obj L).obj)) :=
  (homEquivalence p₁ p₂ c K L D).symm (u ≫ agreement.inv)

end TraceClassOperations

namespace TraceCorrespondenceClass

open GeometricOperationPackage

variable {F : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime] {hl : l ≠ F.p}
  {E : Type u} [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {n : ℕ}
  {G : TraceFormulaCoefficientSetup F l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))}
  {A : ExceptionalAdjunctions F l hl E n G}
  (O : GeometricOperations F l hl E n G A)

/-- The constant unit on any geometric support is in the full finite-Tor category.
This is constructed from the base unit in the operation package: pull it back and
transport along the package's monoidal unit isomorphism using repleteness.
Source: sk-d-corr, final identification, unit domain (blueprint: sk-d-corr). -/
def unitCtf (X : TraceFormulaGeometricSpace F) : Ctf F l E n X :=
  letI : (domain F l E n X).IsClosedUnderIsomorphisms :=
    (G.property.1 X.obj.obj).2
  ⟨unitObj F l E n X,
    (domain F l E n X).prop_of_iso
      (pullUnitIso F l E n (TraceFormulaGeometricSpace.structureMap X)
        (O.comparisons.monoidal (TraceFormulaGeometricSpace.structureMap X))).symm
      ((pullCtf F l hl E n G (TraceFormulaGeometricSpace.structureMap X)).obj
        ⟨unitObj F l E n (TraceFormulaGeometricSpace.point F),
          O.comparisons.unitDomain⟩).property⟩

/-- Projection formula at the support unit followed by the left unitor.
Both inputs are objects of the stated full subcategories; no internal Hom is
asserted to be constructible. Source: sk-d-corr, final Hom identification
(blueprint: sk-d-corr). -/
def projectionUnit {C Z : TraceFormulaGeometricSpace F} (c : C ⟶ Z)
    (M : Ctf F l E n Z) :
    tensorObj F l E n Z ((support F l hl E n G c).obj (unitObj F l E n C)) M.obj ≅
      (support F l hl E n G c).obj ((pull F l E n c).obj M.obj) :=
  O.comparisons.projection c (unitCtf O C) M ≪≫
    (support F l hl E n G c).mapIso
      ((closed F l E n C).monoidal.leftUnitor ((pull F l E n c).obj M.obj))

/-- Ambient Hom equivalence for c and the projections p1 and p2. It is valid for
any composable maps, hence in particular for Z = Y times_s X. The exceptional
composition is the unique adjunction mate of the given support composition.
The ordinary composition is the canonical pullback comparison on the same
intrinsic coefficient categories. The Hom sets on both sides are ambient.

Source: sk-d-corr, displayed Hom identification (blueprint: sk-d-corr).
The construction successively uncurries, uses projection and the unit, passes
through the fully faithful coefficient inclusions, applies the exceptional
adjunction, and conjugates by the ordinary and exceptional composition maps. -/
def homEquivalence {X Y Z C : TraceFormulaGeometricSpace F}
    (p₁ : Z ⟶ Y) (p₂ : Z ⟶ X) (c : C ⟶ Z)
    (K : Ctf F l E n X) (L : Ctf F l E n Y) :
    ((support F l hl E n G c).obj (unitObj F l E n C) ⟶
      (finiteIntrinsicDerivedInternalHom l E Z.obj.obj.left n).obj
        (op ((pull F l E n p₂).obj K.obj),
          ((exceptionalCtf F l hl E n G p₁).obj L).obj)) ≃
    ((pull F l E n (c ≫ p₂)).obj K.obj ⟶
      ((exceptionalCtf F l hl E n G (c ≫ p₁)).obj L).obj) :=
  ((closed F l E n Z).transpose _ _ _).symm |>.trans
    ((Iso.homCongr (projectionUnit O c ((pullCtf F l hl E n G p₂).obj K))
      (Iso.refl _)).trans
      (((domain F l E n Z).fullyFaithfulι.homEquiv
        (X := (supportCtf F l hl E n G c).obj
          ((pullCtf F l hl E n G c).obj ((pullCtf F l hl E n G p₂).obj K)))
        (Y := (exceptionalCtf F l hl E n G p₁).obj L)).symm.trans
        (((A c).homEquiv _ _).trans
          (((domain F l E n C).fullyFaithfulι.homEquiv
            (X := (pullCtf F l hl E n G c).obj ((pullCtf F l hl E n G p₂).obj K))
            (Y := (exceptionalCtf F l hl E n G c).obj
              ((exceptionalCtf F l hl E n G p₁).obj L))).trans
            (Iso.homCongr
              ((pullComp F l E n c p₂).app K.obj).symm
              (((domain F l E n C).ι.mapIso
                ((O.comparisons.exceptionalComp c p₁).app L)).symm))))))

/-- The class [u] is the inverse image under the specified Hom equivalence,
so its support and coefficient map determine it without additional data.
An objectwise agreement of the given exceptional adjoint at L is expressed by
`agreement`; its role is exactly the last-adjoint agreement in the node.
Source: sk-d-corr, last sentence (blueprint: sk-d-corr). -/
def supportedClass {X Y Z C : TraceFormulaGeometricSpace F}
    (p₁ : Z ⟶ Y) (p₂ : Z ⟶ X) (c : C ⟶ Z)
    (K : Ctf F l E n X) (L : Ctf F l E n Y)
    (V : Ambient F l E n C)
    (agreement : ((exceptionalCtf F l hl E n G (c ≫ p₁)).obj L).obj ≅ V)
    (u : (pull F l E n (c ≫ p₂)).obj K.obj ⟶ V) :
    (support F l hl E n G c).obj (unitObj F l E n C) ⟶
      (finiteIntrinsicDerivedInternalHom l E Z.obj.obj.left n).obj
        (op ((pull F l E n p₂).obj K.obj),
          ((exceptionalCtf F l hl E n G p₁).obj L).obj) :=
  (homEquivalence O p₁ p₂ c K L).symm (u ≫ agreement.inv)

end TraceCorrespondenceClass

end WeilConjectures
