/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Cubical rigidified lines

Source: Moret-Bailly, Pinceaux de varietes abeliennes, I §2, especially I 2.4.5;
Lan, revised thesis, Definition 3.2.2.6 and (3.2.2.3)--(3.2.2.4).
(blueprint: def-sfb-cubical-rigidified-line)

The identities are tested in simultaneous local frames of the finitely many line factors.
A frame is allowed to be zero away from those factors. Thus the tests require only finitely
many local trivializations, including over nonreduced test schemes. The scalar identities
are exactly the canonical tensor cancellation identities, without chosen cancellation maps.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace AlgebraicGeometry
namespace CubicalLine

/-- The existing canonical comparison for pullback of the structure module (the degree-zero
case of the upstream tensor-power comparison). Source: Moret-Bailly I §2
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable abbrev pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  Scheme.Modules.boundaryPullbackPowIso f (𝟙_ Y.Modules) 0

/-- Syntax recording the eight signed factors and their parenthesization, rather than a
new tensor product. Source: Moret-Bailly I §2
(blueprint: def-sfb-cubical-rigidified-line). -/
inductive Word (X Y : Scheme.{u}) where
  | factor (a : X ⟶ Y) (negative : Bool)
  | tensor (A B : Word X Y)

/-- Interpret a signed tensor word using the recorded tensor pullback, sheaf tensor, and
internal-Hom dual. Source: Moret-Bailly I §2
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def Word.module {X Y : Scheme.{u}} (L : Y.Modules) : Word X Y → X.Modules
  | .factor a false => (Scheme.Modules.tensorPullback a).obj L
  | .factor a true => Scheme.Modules.dual ((Scheme.Modules.tensorPullback a).obj L)
  | .tensor A B => A.module L ⊗ B.module L

/-- Partial frames: forward and backward maps, required to be mutually inverse only on
the finitely many factors being tested. Source: Moret-Bailly I §2
(blueprint: def-sfb-cubical-rigidified-line). -/
abbrev Frame {Y : Scheme.{u}} (T : Scheme.{u}) (L : Y.Modules) :=
  ∀ a : T ⟶ Y, ((Scheme.Modules.tensorPullback a).obj L ⟶ 𝟙_ T.Modules) ×
    (𝟙_ T.Modules ⟶ (Scheme.Modules.tensorPullback a).obj L)

/-- Validity at one factor; no global simultaneous trivialization is assumed.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
def Frame.valid {T Y : Scheme.{u}} {L : Y.Modules} (b : Frame T L) (a : T ⟶ Y) : Prop :=
  (b a).1 ≫ (b a).2 = 𝟙 _ ∧ (b a).2 ≫ (b a).1 = 𝟙 _

/-- Which finitely many factors of a word must have valid frames after pullback.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
def Word.framed {X Y T : Scheme.{u}} (q : T ⟶ X) {L : Y.Modules} (b : Frame T L) :
    Word X Y → Prop
  | .factor a _ => b.valid (q ≫ a)
  | .tensor A B => A.framed q b ∧ B.framed q b

/-- Evaluate a pulled-back signed word in a partial frame. A negative factor is evaluated
by the actual dual evaluation, inserting the inverse frame of its positive factor.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def Word.frameMap {X Y T : Scheme.{u}} (q : T ⟶ X) (L : Y.Modules)
    (b : Frame T L) : (A : Word X Y) →
      (Scheme.Modules.tensorPullback q).obj (A.module L) ⟶ 𝟙_ T.Modules
  | .factor a false =>
      ((Scheme.Modules.tensorPullbackSectionComp q a).app L).inv ≫ (b (q ≫ a)).1
  | .factor a true =>
      (λ_ _).inv ≫
        ((b (q ≫ a)).2 ≫ ((Scheme.Modules.tensorPullbackSectionComp q a).app L).hom) ▷
          (Scheme.Modules.tensorPullback q).obj
            (Scheme.Modules.dual ((Scheme.Modules.tensorPullback a).obj L)) ≫
        (Scheme.Modules.boundaryPullbackTensorIso q ((Scheme.Modules.tensorPullback a).obj L)
          (Scheme.Modules.dual ((Scheme.Modules.tensorPullback a).obj L))).inv ≫
        (Scheme.Modules.tensorPullback q).map
          (Scheme.Modules.dualEvaluation ((Scheme.Modules.tensorPullback a).obj L)) ≫
        (pullbackUnit q).hom
  | .tensor A B =>
      (Scheme.Modules.boundaryPullbackTensorIso q (A.module L) (B.module L)).hom ≫
        (A.frameMap q L b ⊗ₘ B.frameMap q L b) ≫ (λ_ _).hom

/-- The triple fibre product of a group scheme over its base.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable abbrev cube {S : Scheme.{u}} (G : Over S) : Over S :=
  ∏ᶜ (fun _ : Fin 3 ↦ G)

/-- The coordinate-sum map, including the empty sum (identity followed by the structure
map). Multiplicative notation here denotes the additive group law of the source.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def sumMap {S : Scheme.{u}} (G : Over S) [CommGrpObj G]
    (I : Finset (Fin 3)) : cube G ⟶ G :=
  ∏ i ∈ I, Pi.π (fun _ : Fin 3 ↦ G) i

/-- The precise eight factors of Theta_3, with positive singletons and triple and negative
pairs and empty set. Source: Moret-Bailly I §2
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def thetaWord {S : Scheme.{u}} (G : Over S) [CommGrpObj G] :
    Word (cube G).left G.left :=
  .tensor (.tensor (.tensor (.tensor (.tensor (.tensor (.tensor
    (.factor (sumMap G {0, 1, 2}).left false)
    (.factor (sumMap G {0}).left false))
    (.factor (sumMap G {1}).left false))
    (.factor (sumMap G {2}).left false))
    (.factor (sumMap G {0, 1}).left true))
    (.factor (sumMap G {0, 2}).left true))
    (.factor (sumMap G {1, 2}).left true))
    (.factor (sumMap G ∅).left true)

/-- The alternating cube tensor, using the sheaf-Hom dual for every inverse.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def theta {S : Scheme.{u}} (G : Over S) [CommGrpObj G] (L : G.left.Modules) :
    (cube G).left.Modules :=
  (thetaWord G).module L

/-- Frame coordinates of the pulled-back cube section at a triple of generalized points.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def value {S : Scheme.{u}} {G : Over S} [CommGrpObj G]
    {L : G.left.Modules} (τ : 𝟙_ (cube G).left.Modules ≅ theta G L)
    (T : Over S) (x : Fin 3 → (T ⟶ G)) (b : Frame T.left L) :
    𝟙_ T.left.Modules ⟶ 𝟙_ T.left.Modules :=
  (pullbackUnit (Pi.lift x).left).inv ≫
    (Scheme.Modules.tensorPullback (Pi.lift x).left).map τ.hom ≫
    (thetaWord G).frameMap (Pi.lift x).left L b

/-- A frame usable for a triple; it is invertible at exactly the eight maps needed there.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
def Framed {S : Scheme.{u}} {G : Over S} [CommGrpObj G] {L : G.left.Modules}
    (T : Over S) (x : Fin 3 → (T ⟶ G)) (b : Frame T.left L) : Prop :=
  (thetaWord G).framed (Pi.lift x).left b

/-- Symmetry, normalization on each identity slice, and the four-point cocycle. All tests
are over arbitrary schemes, so include nilpotents and all base changes. Valid partial
frames always exist locally for these finitely many invertible factors. Under a frame,
canonical cancellation is multiplication of scalars; hence these equalities are precisely
the tensor identities of the source. The slice cancellation does not depend on the scale
of the supplied rigidification: its four occurrences cancel in pairs.
Source: Moret-Bailly I §2; Lan Definition 3.2.2.6
(blueprint: def-sfb-cubical-rigidified-line). -/
def Compatible {S : Scheme.{u}} {G : Over S} [CommGrpObj G] {L : G.left.Modules}
    (τ : 𝟙_ (cube G).left.Modules ≅ theta G L) : Prop :=
  (∀ (T : Over S) (x : Fin 3 → (T ⟶ G)) (σ : Equiv.Perm (Fin 3)) (b : Frame T.left L),
    Framed T x b → Framed T (x ∘ σ) b → value τ T x b = value τ T (x ∘ σ) b) ∧
  (∀ (T : Over S) (x : Fin 3 → (T ⟶ G)) (i : Fin 3) (b : Frame T.left L),
    x i = 1 → Framed T x b → value τ T x b = 𝟙 _) ∧
  (∀ (T : Over S) (x y w z : T ⟶ G) (b : Frame T.left L),
    Framed T ![x, y, z] b → Framed T ![x * y, w, z] b →
    Framed T ![y, w, z] b → Framed T ![x, y * w, z] b →
    value τ T ![x, y, z] b ≫ value τ T ![x * y, w, z] b =
      value τ T ![y, w, z] b ≫ value τ T ![x, y * w, z] b)

end CubicalLine

/-- A cubical rigidified invertible module: the actual line module, an identity
rigidification, and a symmetric normalized nowhere-vanishing cube section satisfying
the cocycle. Source: Moret-Bailly I §2; Lan Definition 3.2.2.6
(blueprint: def-sfb-cubical-rigidified-line). -/
structure CubicalRigidifiedLine {S : Scheme.{u}} (G : Over S) [CommGrpObj G] where
  /-- The invertible module on G. -/
  line : G.left.Modules
  /-- Zariski local freeness of rank one. -/
  invertible : line.IsInvertible
  /-- Rigidification along the group identity. -/
  rigidification : (Scheme.Modules.tensorPullback (η[G]).left).obj line ≅
    𝟙_ S.Modules
  /-- Nowhere-vanishing cube section. -/
  sectionIso : 𝟙_ (CubicalLine.cube G).left.Modules ≅ CubicalLine.theta G line
  /-- Symmetry, identity-slice normalization and the cocycle. -/
  compatible : CubicalLine.Compatible sectionIso


namespace CubicalLine

/-- Apply a line isomorphism to the positive factors and its inverse transpose to the
negative factors. Source: Moret-Bailly I §2; Lan Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def Word.mapIso {X Y : Scheme.{u}} {L M : Y.Modules} (f : L ≅ M) :
    (A : Word X Y) → A.module L ≅ A.module M
  | .factor a false => (Scheme.Modules.tensorPullback a).mapIso f
  | .factor a true =>
      ((Scheme.Modules.dualFunctor X).mapIso
        ((Scheme.Modules.tensorPullback a).mapIso f).op).symm
  | .tensor A B => A.mapIso f ⊗ᵢ B.mapIso f

/-- Transport partial frames to the tensor pullback of a line, with the normalized
composition comparison. Source: Moret-Bailly I §2
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def Frame.change {T Y Y' : Scheme.{u}} {L : Y.Modules}
    (h : Y' ⟶ Y) (b : Frame T L) : Frame T ((Scheme.Modules.tensorPullback h).obj L) :=
  fun a ↦
    ⟨((Scheme.Modules.tensorPullbackSectionComp a h).app L).inv ≫ (b (a ≫ h)).1,
      (b (a ≫ h)).2 ≫ ((Scheme.Modules.tensorPullbackSectionComp a h).app L).hom⟩

/-- The cube map induced by a morphism over a map of base schemes, built from the three
projections. Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def baseCubeMap {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} (h : (Over.map g).obj G' ⟶ G) :
    (Over.map g).obj (cube G') ⟶ cube G :=
  Pi.lift (fun i ↦ (Over.map g).map (Pi.π (fun _ : Fin 3 ↦ G') i) ≫ h)

/-- A morphism across bases preserves the coordinate sums precisely when it is a group
homomorphism: singleton sums impose no restriction, the empty sum is the identity and
the pair sum is multiplication. This form also covers the base-change projection.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
def PreservesSums {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) : Prop :=
  (η[G']).left ≫ h.left = g ≫ (η[G]).left ∧
    ∀ I : Finset (Fin 3),
      (sumMap G' I).left ≫ h.left = (baseCubeMap g h).left ≫ (sumMap G I).left

/-- Frame characterization of the canonical cube/pullback comparison. It specifies the
map on local tensor generators, so rules out rescaling by any unit.
Source: Moret-Bailly I §2, functoriality (blueprint: def-sfb-cubical-rigidified-line). -/
def ComparisonNormalized {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (L : G.left.Modules)
    (c : theta G' ((Scheme.Modules.tensorPullback h.left).obj L) ≅
      (Scheme.Modules.tensorPullback (baseCubeMap g h).left).obj (theta G L)) : Prop :=
  ∀ (T : Scheme.{u}) (q : T ⟶ (cube G').left) (b : Frame T L),
    (thetaWord G).framed (q ≫ (baseCubeMap g h).left) b →
    (thetaWord G').framed q (b.change h.left) →
    (Scheme.Modules.tensorPullback q).map c.hom ≫
        ((Scheme.Modules.tensorPullbackSectionComp q (baseCubeMap g h).left).app
          (theta G L)).inv ≫
        (thetaWord G).frameMap (q ≫ (baseCubeMap g h).left) L b =
      (thetaWord G').frameMap q ((Scheme.Modules.tensorPullback h.left).obj L)
        (b.change h.left)

/-- The cube comparison is uniquely determined by its local tensor-frame formula.
Source: Moret-Bailly I §2, pullback of cubical lines; Lan following Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line).
Proof: on an open where the finitely many positive line factors are free of rank one,
pullback sends a generator to its tensor inverse image and the dual generator to its
dual. The tensor and composition comparisons give exactly ComparisonNormalized.
These local maps are independent of the chosen frames, since changing one frame scales
the two sides by the same exponent. They glue uniquely, and their local inverses glue.
The equality of coordinate-sum maps supplied by PreservesSums identifies the factors.
No choice of an arbitrary isomorphism or scalar is made. -/
theorem comparison_existsUnique {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (hh : PreservesSums g h)
    (L : G.left.Modules) (hL : L.IsInvertible) :
    ∃! c : theta G' ((Scheme.Modules.tensorPullback h.left).obj L) ≅
        (Scheme.Modules.tensorPullback (baseCubeMap g h).left).obj (theta G L),
      ComparisonNormalized g h L c := by
  sorry

/-- The uniquely frame-normalized cube/pullback comparison.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def comparison {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (hh : PreservesSums g h)
    (L : G.left.Modules) (hL : L.IsInvertible) :
    theta G' ((Scheme.Modules.tensorPullback h.left).obj L) ≅
      (Scheme.Modules.tensorPullback (baseCubeMap g h).left).obj (theta G L) :=
  Classical.choose (comparison_existsUnique g h hh L hL)

/-- The termwise pulled-back rigidification, using the identity equality of the group map.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def pullbackRigidification {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (hh : PreservesSums g h)
    (L : G.left.Modules) (r : (Scheme.Modules.tensorPullback (η[G]).left).obj L ≅
      𝟙_ S.Modules) :
    (Scheme.Modules.tensorPullback (η[G']).left).obj
      ((Scheme.Modules.tensorPullback h.left).obj L) ≅ 𝟙_ S'.Modules :=
  ((Scheme.Modules.tensorPullbackSectionComp (η[G']).left h.left).app L).symm ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj L) hh.1) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp g (η[G]).left).app L ≪≫
    (Scheme.Modules.tensorPullback g).mapIso r ≪≫ pullbackUnit g

/-- The cube section is the pullback of the old section through the canonical comparison.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def pullbackSection {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (hh : PreservesSums g h)
    (L : G.left.Modules) (hL : L.IsInvertible)
    (τ : 𝟙_ (cube G).left.Modules ≅ theta G L) :
    𝟙_ (cube G').left.Modules ≅ theta G' ((Scheme.Modules.tensorPullback h.left).obj L) :=
  (pullbackUnit (baseCubeMap g h).left).symm ≪≫
    (Scheme.Modules.tensorPullback (baseCubeMap g h).left).mapIso τ ≪≫
    (comparison g h hh L hL).symm

/-- Tensor pullback preserves invertibility and the three cubical identities.
Source: Moret-Bailly I §2, termwise pullback; Lan following Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line).
Proof: local rank-one trivializations pull back to rank-one trivializations.
Use the frame characterization of comparison to identify each pulled-back cube value
with the original value. PreservesSums takes the identity and products of generalized
points to the identity and products. Apply successively the symmetry, normalization,
and cocycle fields of Compatible. These equalities hold after every base change and
on every member of the local frame cover, hence glue as sheaf morphism equalities. -/
theorem pullback_properties {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (hh : PreservesSums g h)
    (L : G.left.Modules) (hL : L.IsInvertible)
    (τ : 𝟙_ (cube G).left.Modules ≅ theta G L) (hτ : Compatible τ) :
    ((Scheme.Modules.tensorPullback h.left).obj L).IsInvertible ∧
      Compatible (pullbackSection g h hh L hL τ) := by
  sorry

/-- A homomorphism over one base preserves identity and all coordinate sums.
Source: Moret-Bailly I §2, pullback (blueprint: def-sfb-cubical-rigidified-line).
Proof: preservation of identity is the unit axiom of IsMonHom. For every finite subset,
postcomposition with h preserves its product by the multiplication axiom. The product
projections of baseCubeMap give the same coordinates; product extensionality finishes. -/
theorem hom_preservesSums {S : Scheme.{u}} {G G' : Over S}
    [CommGrpObj G] [CommGrpObj G'] (h : G' ⟶ G) [IsMonHom h] :
    PreservesSums (G := G) (G' := G') (𝟙 S) ((Over.mapId S).hom.app G' ≫ h) := by
  sorry

/-- Base change of the underlying group scheme, with its actual fibre-product scheme.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable abbrev baseChangedGroup {S S' : Scheme.{u}} (g : S' ⟶ S) (G : Over S) :
    Over S' :=
  (Over.pullback g).obj G

/-- Base change transports the group operations by the Cartesian pullback functor.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable instance baseChangedGroup_grpObj {S S' : Scheme.{u}} (g : S' ⟶ S)
    (G : Over S) [GrpObj G] : GrpObj (baseChangedGroup g G) :=
  ((Over.pullback g).mapGrp.obj (Grp.mk G)).grp

/-- The pulled-back group law is commutative.
Source: Moret-Bailly I §2 (blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable instance baseChangedGroup_isCommMonObj {S S' : Scheme.{u}} (g : S' ⟶ S)
    (G : Over S) [CommGrpObj G] : IsCommMonObj (baseChangedGroup g G) :=
  ((Over.pullback g).mapCommMon.obj (CommMon.mk G)).comm

/-- The canonical projection of the base-changed group preserves all coordinate sums.
Source: Moret-Bailly I §2, restriction to a base subscheme
(blueprint: def-sfb-cubical-rigidified-line).
Proof: the group operations on baseChangedGroup are their Cartesian pullbacks.
Composing the identity or multiplication with the first pullback projection is therefore
the original identity or multiplication after base change. Iterating multiplication gives
the equality for each finite subset, and the empty subset gives the identity case. -/
theorem baseChange_preservesSums {S S' : Scheme.{u}} (g : S' ⟶ S)
    (G : Over S) [CommGrpObj G] :
    PreservesSums (G := G) (G' := baseChangedGroup g G) g
      ((Over.mapPullbackAdj g).counit.app G) := by
  sorry

end CubicalLine

namespace CubicalRigidifiedLine

/-- An isomorphism of cubical rigidified lines preserves both the identity rigidification
and the cube section under the actual eight-factor operation.
Source: Moret-Bailly I §2; Lan Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line). -/
structure Iso {S : Scheme.{u}} {G : Over S} [CommGrpObj G]
    (L M : CubicalRigidifiedLine G) where
  /-- The isomorphism of invertible modules. -/
  lineIso : L.line ≅ M.line
  /-- Preservation of the rigidification. -/
  rigidification : ((Scheme.Modules.tensorPullback (η[G]).left).mapIso lineIso) ≪≫
    M.rigidification = L.rigidification
  /-- Preservation of the cube section. -/
  cube : L.sectionIso ≪≫ (CubicalLine.thetaWord G).mapIso lineIso = M.sectionIso

/-- Termwise pullback, including base changes: the line is h*L, the rigidification is the
canonical composition through g*e*L, and the section is (h^3)*tau under the normalized
cube comparison. Source: Moret-Bailly I §2; Lan following Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def pullbackOver {S S' : Scheme.{u}} (g : S' ⟶ S)
    {G : Over S} {G' : Over S'} [CommGrpObj G] [CommGrpObj G']
    (h : (Over.map g).obj G' ⟶ G) (hh : CubicalLine.PreservesSums g h)
    (L : CubicalRigidifiedLine G) : CubicalRigidifiedLine G' where
  line := (Scheme.Modules.tensorPullback h.left).obj L.line
  invertible := (CubicalLine.pullback_properties g h hh L.line L.invertible
    L.sectionIso L.compatible).1
  rigidification := CubicalLine.pullbackRigidification g h hh L.line L.rigidification
  sectionIso := CubicalLine.pullbackSection g h hh L.line L.invertible L.sectionIso
  compatible := (CubicalLine.pullback_properties g h hh L.line L.invertible
    L.sectionIso L.compatible).2

/-- Pullback by a homomorphism over the same base, with its induced rigidification
and cube section. Source: Moret-Bailly I §2; Lan following Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def pullback {S : Scheme.{u}} {G G' : Over S}
    [CommGrpObj G] [CommGrpObj G'] (h : G' ⟶ G) [IsMonHom h]
    (L : CubicalRigidifiedLine G) : CubicalRigidifiedLine G' :=
  pullbackOver (G := G) (G' := G') (𝟙 S) ((Over.mapId S).hom.app G' ≫ h)
    (CubicalLine.hom_preservesSums h) L

/-- Termwise base change to the actual fibre product. In particular, for a subscheme
inclusion S' → S this is the restriction requested in the source.
Source: Moret-Bailly I §2; Lan following Definition 3.2.2.7
(blueprint: def-sfb-cubical-rigidified-line). -/
noncomputable def baseChange {S S' : Scheme.{u}} (g : S' ⟶ S) {G : Over S}
    [CommGrpObj G] (L : CubicalRigidifiedLine G) :
    CubicalRigidifiedLine (CubicalLine.baseChangedGroup g G) :=
  pullbackOver (G := G) (G' := CubicalLine.baseChangedGroup g G) g
    ((Over.mapPullbackAdj g).counit.app G)
    (CubicalLine.baseChange_preservesSums g G) L

end CubicalRigidifiedLine
end AlgebraicGeometry
