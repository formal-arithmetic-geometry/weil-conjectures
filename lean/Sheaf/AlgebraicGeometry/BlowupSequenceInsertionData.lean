/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.KrullDimension.Basic

/-! # Data for insertion into an ordinary blowup sequence

Source: Temkin, Non-embedded Desingularization, §§2.2.3, 4.1.3, 4.2.1--4.2.4,
Definition 4.2.2 and Lemmas 4.2.1, 4.2.3, 4.2.5, printed pp.28--29
(blueprint: def-per-blowup-sequence-insertion-data).

An insertion is represented by its three consecutive segments: the original prefix,
the given inserted tower, and a replacement suffix. Only the suffix is new data.
All comparisons retain every stage, including empty centers, and compare ideal sheaves.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.OrdinaryBlowupInsertion

/-- Shift a suffix level back to its old index.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
def shiftLevel (n m l : ℕ) (h : m + l = n) (i : Fin (l + 1)) : Fin (n + 1) :=
  ⟨m + i.val, by omega⟩

/-- Shift a suffix center back to its old index.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
def shiftCenter (n m l : ℕ) (h : m + l = n) (i : Fin l) : Fin n :=
  ⟨m + i.val, by omega⟩

/-- The original tower, the insertion position, the preserved open and the supported
inserted tower, with exactly the Noetherian, coherence and schematic-closure conditions.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
structure Input (X : Scheme.{u}) where
  old : OrdinaryBlowupTower X
  position : Fin (old.length + 1)
  inserted : OrdinaryBlowupTower (old.level position)
  preserved : X.Opens
  noetherian : ∀ i, IsNoetherian (old.level i)
  coherent : ∀ i : Fin old.length, RingedSpace.IsCoherent (old.level i.castSucc).toRingedSpace
    (old.center i).toModules
  inserted_noetherian : ∀ i, IsNoetherian (inserted.level i)
  inserted_coherent : ∀ i : Fin inserted.length,
    RingedSpace.IsCoherent (inserted.level i.castSucc).toRingedSpace
      (inserted.center i).toModules
  closure : ∀ i : Fin old.length, position.val ≤ i.val →
    old.center i =
      (((old.center i).subschemeι ⁻¹ᵁ (old.toBase i.castSucc ⁻¹ᵁ preserved)).ι ≫
        (old.center i).subschemeι).ker
  supported : ∀ (i : Fin inserted.length) (z : (inserted.center i).subscheme),
    old.toBase position
      (inserted.toBase i.castSucc ((inserted.center i).subschemeι z)) ∉ preserved

/-- The terminal scheme of the inserted segment.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
def Input.terminal {X : Scheme.{u}} (P : Input X) : Scheme.{u} :=
  P.inserted.level (Fin.last P.inserted.length)

/-- The structure map to the original base of a replacement suffix level.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
def suffixBase {X : Scheme.{u}} (P : Input X) (T : OrdinaryBlowupTower P.terminal)
    (i : Fin (T.length + 1)) : T.level i ⟶ X :=
  T.toBase i ≫ P.inserted.toBase (Fin.last P.inserted.length) ≫ P.old.toBase P.position

/-- The old level over the preserved open, at a replacement index.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
def oldOpen {X : Scheme.{u}} (P : Input X) (l : ℕ) (h : P.position.val + l = P.old.length)
    (i : Fin (l + 1)) :=
  P.old.toBase (shiftLevel P.old.length P.position.val l h i) ⁻¹ᵁ P.preserved

/-- A replacement suffix. Concatenating the unchanged prefix, the inserted tower and
this suffix is the whole insertion. Its levels are compared with the old levels only
over the preserved open. A new ideal is the kernel of the old restricted center's map
into its new ambient scheme. All maps to the original base agree on this common open.
Source: Temkin Definition 4.2.2 (blueprint: def-per-blowup-sequence-insertion-data). -/
structure Diagram {X : Scheme.{u}} (P : Input X) where
  suffix : OrdinaryBlowupTower P.terminal
  length_eq : P.position.val + suffix.length = P.old.length
  openIso : ∀ i : Fin (suffix.length + 1),
    (oldOpen P suffix.length length_eq i).toScheme ≅
      (suffixBase P suffix i ⁻¹ᵁ P.preserved).toScheme
  over : ∀ i, (openIso i).hom ≫ (suffixBase P suffix i ⁻¹ᵁ P.preserved).ι ≫
    suffixBase P suffix i = (oldOpen P suffix.length length_eq i).ι ≫
      P.old.toBase (shiftLevel P.old.length P.position.val suffix.length length_eq i)
  oldOpenMap : ∀ (i j : Fin (suffix.length + 1)) (_hij : i ≤ j),
    (oldOpen P suffix.length length_eq j).toScheme ⟶
      (oldOpen P suffix.length length_eq i).toScheme
  oldOpenMap_fac : ∀ i j (hij : i ≤ j),
    oldOpenMap i j hij ≫ (oldOpen P suffix.length length_eq i).ι =
      (oldOpen P suffix.length length_eq j).ι ≫ P.old.transition
        (shiftLevel P.old.length P.position.val suffix.length length_eq i)
        (shiftLevel P.old.length P.position.val suffix.length length_eq j)
        (by change P.position.val + i.val ≤ P.position.val + j.val; omega)
  naturality : ∀ i j (hij : i ≤ j),
    (openIso j).hom ≫ (suffixBase P suffix j ⁻¹ᵁ P.preserved).ι ≫
      suffix.transition i j hij = oldOpenMap i j hij ≫ (openIso i).hom ≫
        (suffixBase P suffix i ⁻¹ᵁ P.preserved).ι
  center_eq : ∀ i : Fin suffix.length,
    suffix.center i =
      (((P.old.center
          (shiftCenter P.old.length P.position.val suffix.length length_eq i)).subschemeι ∣_
            oldOpen P suffix.length length_eq i.castSucc) ≫
        (openIso i.castSucc).hom ≫
          (suffixBase P suffix i.castSucc ⁻¹ᵁ P.preserved).ι).ker
  noetherian : ∀ i, IsNoetherian (suffix.level i)
  coherent : ∀ i : Fin suffix.length,
    RingedSpace.IsCoherent (suffix.level i.castSucc).toRingedSpace (suffix.center i).toModules

/-- The old center in the first position, when it exists.
Source: Temkin Lemma 4.2.3 (blueprint: def-per-blowup-sequence-insertion-data). -/
def Input.firstOld {X : Scheme.{u}} (P : Input X) (h : P.position.val < P.old.length) :
    (P.old.level P.position).IdealSheafData :=
  (P.old.center ⟨P.position.val, h⟩).comap
    (eqToHom (congrArg P.old.level (by rfl)))

/-- The first replacement center, transported to the terminal inserted scheme.
Source: Temkin Lemma 4.2.3 (blueprint: def-per-blowup-sequence-insertion-data). -/
def Diagram.firstNew {X : Scheme.{u}} {P : Input X} (D : Diagram P)
    (h : P.position.val < P.old.length) : P.terminal.IdealSheafData :=
  (D.suffix.center ⟨0, by have := D.length_eq; omega⟩).comap D.suffix.initial.inv

/-- The transform of the first old center at an arbitrary inserted level, computed as
the schematic closure of the common preserved open. The insertion theorem identifies
these with the successive ordinary strict transforms.
Source: Temkin §§2.2.8, 4.2.1--4.2.2
(blueprint: def-per-blowup-sequence-insertion-data). -/
def Input.transform {X : Scheme.{u}} (P : Input X)
    (h : P.position.val < P.old.length) (i : Fin (P.inserted.length + 1)) :
    (P.inserted.level i).IdealSheafData :=
  (strictTransformMap (P.firstOld h).subschemeι (P.inserted.toBase i)
    (P.old.toBase P.position ⁻¹ᵁ P.preserved)).ker

/-- A stagewise isomorphism of suffixes over their fixed initial scheme, preserving
all transitions and every ordered center ideal. No empty stage is deleted.
Source: Temkin §2.2.3 (blueprint: def-per-blowup-sequence-insertion-data). -/
structure SuffixIso {X : Scheme.{u}} {P : Input X} (D E : Diagram P) where
  length_eq : D.suffix.length = E.suffix.length
  iso : ∀ i : Fin (D.suffix.length + 1),
    D.suffix.level i ≅ E.suffix.level (Fin.cast (congrArg Nat.succ length_eq) i)
  over : ∀ i, (iso i).hom ≫
    E.suffix.toBase (Fin.cast (congrArg Nat.succ length_eq) i) = D.suffix.toBase i
  naturality : ∀ i j (hij : i ≤ j),
    D.suffix.transition i j hij ≫ (iso i).hom = (iso j).hom ≫
      E.suffix.transition (Fin.cast (congrArg Nat.succ length_eq) i)
        (Fin.cast (congrArg Nat.succ length_eq) j) (by simpa using hij)
  ideal : ∀ i : Fin D.suffix.length,
    D.suffix.center i = (E.suffix.center (Fin.cast length_eq i)).comap (iso i.castSucc).hom

/-- A pullback of towers retaining all stages, with cartesian level squares and equality
of extended center ideals. This differs from a contracted resolution comparison, which
must delete empty stages.
Source: Temkin §§2.2.5, 4.2.4 (blueprint: def-per-blowup-sequence-insertion-data). -/
structure TowerPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : OrdinaryBlowupTower X) (B : OrdinaryBlowupTower Y) where
  length_eq : B.length = A.length
  map : ∀ i : Fin (B.length + 1),
    B.level i ⟶ A.level (Fin.cast (congrArg Nat.succ length_eq) i)
  cartesian : ∀ i, IsPullback (map i) (B.toBase i)
    (A.toBase (Fin.cast (congrArg Nat.succ length_eq) i)) f
  naturality : ∀ i j (hij : i ≤ j), B.transition i j hij ≫ map i = map j ≫
    A.transition (Fin.cast (congrArg Nat.succ length_eq) i)
      (Fin.cast (congrArg Nat.succ length_eq) j) (by simpa using hij)
  ideal : ∀ i : Fin B.length,
    B.center i = (A.center (Fin.cast length_eq i)).comap (map i.castSucc)

/-- Pullback data for the two input segments and the preserved open; the insertion
position is retained even if some centers become empty.
Source: Temkin Lemma 4.2.5 (blueprint: def-per-blowup-sequence-insertion-data). -/
structure InputPullback {X Y : Scheme.{u}} (f : Y ⟶ X) (P : Input X) (Q : Input Y) where
  old : TowerPullback f P.old Q.old
  position : Fin.cast (congrArg Nat.succ old.length_eq) Q.position = P.position
  preserved : Q.preserved = f ⁻¹ᵁ P.preserved
  inserted : TowerPullback
    (old.map Q.position ≫ eqToHom (congrArg P.old.level position)) P.inserted Q.inserted

/-- The actual map between the terminal inserted schemes in a pullback comparison.
Source: Temkin Lemma 4.2.5 (blueprint: def-per-blowup-sequence-insertion-data). -/
def InputPullback.terminalMap {X Y : Scheme.{u}} {f : Y ⟶ X}
    {P : Input X} {Q : Input Y} (b : InputPullback f P Q) : Q.terminal ⟶ P.terminal :=
  b.inserted.map (Fin.last Q.inserted.length) ≫
    eqToHom (congrArg P.inserted.level (by ext; simp))

/-- The generic points of the irreducible components of the image. Images of centers
in the insertion theorem are closed because the structural morphisms are proper.
Source: Temkin §4.1.3 (blueprint: def-per-blowup-sequence-insertion-data). -/
def genericImagePoints {C X : Scheme.{u}} (f : C ⟶ X) : Set X :=
  Subtype.val '' genericPoints (Set.range f)

/-- Pure codimension of the image, measured in the local rings of the original base.
Source: Temkin §4.1.3 (blueprint: def-per-blowup-sequence-insertion-data). -/
def PureImageCodimension {C X : Scheme.{u}} (f : C ⟶ X) (e : ℕ) : Prop :=
  ∀ x ∈ genericImagePoints f, ringKrullDim (X.presheaf.stalk x) = (e : WithBot ℕ∞)

/-- Schematic density of the inverse image of the generic image points: a section
vanishing on their induced local schemes vanishes. Germs express exactly restriction
to those local schemes, including nilpotents, rather than topological density.
Source: Temkin §4.1.3 (blueprint: def-per-blowup-sequence-insertion-data). -/
def DenseAboveGenericImage {C X : Scheme.{u}} (f : C ⟶ X) : Prop :=
  ∀ (V : C.Opens) (s : Γ(C, V)),
    (∀ (x : C) (hx : x ∈ V), f x ∈ genericImagePoints f → C.presheaf.germ V x hx s = 0) →
      s = 0

/-- A tower on the first old center induced by the inserted ambient tower: its levels
are the transforms, each transition blows up the pulled-back ambient center, and the
closed embeddings commute with all tower transitions and the initial embeddings.
Source: Temkin Lemma 4.2.1 (blueprint: def-per-blowup-sequence-insertion-data). -/
structure CenterTower {X : Scheme.{u}} (P : Input X)
    (h : P.position.val < P.old.length) where
  tower : OrdinaryBlowupTower (P.firstOld h).subscheme
  length_eq : tower.length = P.inserted.length
  map : ∀ i : Fin (tower.length + 1),
    tower.level i ⟶ P.inserted.level (Fin.cast (congrArg Nat.succ length_eq) i)
  closed : ∀ i, IsClosedImmersion (map i)
  initial : map 0 ≫ P.inserted.initial.hom = tower.initial.hom ≫ (P.firstOld h).subschemeι
  naturality : ∀ i j (hij : i ≤ j), tower.transition i j hij ≫ map i = map j ≫
    P.inserted.transition (Fin.cast (congrArg Nat.succ length_eq) i)
      (Fin.cast (congrArg Nat.succ length_eq) j) (by simpa using hij)
  ideal : ∀ i : Fin tower.length,
    tower.center i = (P.inserted.center (Fin.cast length_eq i)).comap (map i.castSucc)
  transform : ∀ i, (map i).ker =
    P.transform h (Fin.cast (congrArg Nat.succ length_eq) i)

/-- The terminal closed embedding of the induced tower in the inserted terminal scheme.
Source: Temkin Lemma 4.2.1 (blueprint: def-per-blowup-sequence-insertion-data). -/
def CenterTower.terminalMap {X : Scheme.{u}} {P : Input X}
    {h : P.position.val < P.old.length} (H : CenterTower P h) :
    H.tower.level (Fin.last H.tower.length) ⟶ P.terminal :=
  H.map (Fin.last H.tower.length) ≫
    eqToHom (congrArg P.inserted.level (by ext; simp))

end AlgebraicGeometry.OrdinaryBlowupInsertion
