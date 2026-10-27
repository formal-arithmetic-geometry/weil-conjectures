# CategoryTheory.CondensedBar.InternalCochainCoordinates

## Reason

The construction lemmas need the existing coordinate specifications without importing the
existence theorem that will use those lemmas. Move the data to a definitions-only module
and publicly reexport it from the original module. All existing declaration names,
signatures, attributes and definition bodies are retained. The theorem statement stays
identical. This is a relocation to permit acyclic proof dependencies, with no change to
the meaning of any target or consumer.

## Old

The following header and declarations occurred in
`lean/Sheaf/CategoryTheory/InternalHomogeneousCochainCoordinates.lean`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-! # Internal homogeneous and inhomogeneous cochain coordinates

Source: Stacks Project, Tag 0DVG, section-continuous-group-cohomology, displayed bar
boundary; internal sheaf adaptation in the DAG, not a verbatim assertion of that tag
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates).

The specifications below retain internal module objects, their actual section evaluations,
and cochain maps. Existence is the final theorem; no module is chosen from an existence axiom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar

/-- Prefix products of a tuple of continuous group-valued sections, starting with the unit.
Source: the homogeneous coordinate calculation following Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def coordinatePrefixes {J : ProfiniteGrp.{u}} {T : Profinite.{u}} {n : ℕ}
    (g : Fin n → C(T, J)) : Fin (n + 1) → C(T, J) :=
  fun i ↦ ((List.ofFn g).take i.val).prod

/-- Successive left quotients, preserving the order for noncommutative groups.
Source: the homogeneous coordinate calculation following Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def coordinateQuotients {J : ProfiniteGrp.{u}} {T : Profinite.{u}} {n : ℕ}
    (x : Fin (n + 1) → C(T, J)) : Fin n → C(T, J) :=
  fun i ↦ (x i.castSucc)⁻¹ * x i.succ

/-- Homogeneous equivariance is tested after every further profinite base change.
Source: the internal homogeneous-coordinate adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def IsHomogeneousSection {A : Ring.{u}} (F : InternalFunctions A) (J : ProfiniteGrp.{u})
    (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power J (n + 1))).obj M.module) S) : Prop :=
  ∀ (T : Profinite.{u}) (f : T ⟶ S) (a : C(T, J))
    (g : Fin (n + 1) → C(T, J)),
    (F.evaluate (power J (n + 1)) S M.module x).val T f
        (tupleMap (fun i ↦ a * g i)) =
      M.act T a ((F.evaluate (power J (n + 1)) S M.module x).val T f (tupleMap g))

/-- A presentation of the homogeneous submodule complex: the inclusion is injective on
sections, with exactly the homogeneous sections as its image, and the differential is
alternating deletion. The coefficient functor and inclusion use the original internal maps.
This specifies the subobject up to its unique inclusion-preserving isomorphism.
Source: internal sheaf adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
structure InternalHomogeneousCochains {A : Ring.{u}} (F : InternalFunctions A)
    (J : ProfiniteGrp.{u}) where
  complex : Equivariant A J ⥤ CochainComplex (Modules A) ℕ
  inclusion : ∀ (M : Equivariant A J) (n : ℕ),
    (complex.obj M).X n ⟶ (F.functor (power J (n + 1))).obj M.module
  injective : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u}),
    Function.Injective ((inclusion M n).hom.hom.app (op S))
  image : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power J (n + 1))).obj M.module) S),
    (∃ y : sections A ((complex.obj M).X n) S,
      (inclusion M n).hom.hom.app (op S) y = x) ↔ IsHomogeneousSection F J M n S x
  maps : ∀ {M N : Equivariant A J} (h : M ⟶ N) (n : ℕ),
    (complex.map h).f n ≫ inclusion N n =
      inclusion M n ≫ (F.functor (power J (n + 1))).map h.val
  differential : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((complex.obj M).X n) S) (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin (n + 2) → C(T, J)),
    (F.evaluate (power J (n + 2)) S M.module
      (((complex.obj M).d n (n + 1) ≫ inclusion M (n + 1)).hom.hom.app (op S) x)).val
        T f (tupleMap g) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (F.evaluate (power J (n + 1)) S M.module
          ((inclusion M n).hom.hom.app (op S) x)).val T f
            (tupleMap (fun j ↦ g (i.succAbove j)))

/-- Evaluation of a homogeneous cochain via its actual submodule inclusion.
Source: internal sheaf adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def homogeneousCoordinateValue {A : Ring.{u}} {F : InternalFunctions A}
    {J : ProfiniteGrp.{u}} (H : InternalHomogeneousCochains F J) (M : Equivariant A J)
    (n : ℕ) (S : Profinite.{u}) (x : sections A ((H.complex.obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, J)) : sections A M.module T :=
  (F.evaluate (power J (n + 1)) S M.module
    ((H.inclusion M n).hom.hom.app (op S) x)).val T f (tupleMap g)

/-- Evaluation of an inhomogeneous cochain through the recorded bar-term isomorphism.
Source: Stacks 0DVG and the landed internal bar data
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def inhomogeneousCoordinateValue {A : Ring.{u}} {F : InternalFunctions A}
    {J : ProfiniteGrp.{u}} (B : BarDiagram (G := J) F) (M : Equivariant A J)
    (n : ℕ) (S : Profinite.{u}) (x : sections A (((cochains B).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, J)) : sections A M.module T :=
  (F.evaluate (power J n) S M.module ((B.term M n).hom.hom.hom.app (op S) x)).val
    T f (tupleMap g)

/-- The ordinary localization of integer-indexed internal-module complexes, using the
standard large localization in the stated size convention. This defines a functor, not a
new derived category or a choice of a comparison map.
Source: Mathlib derived-category localization
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def coordinateLocalization (A : Ring.{u}) :
    CochainComplex (Modules A) ℤ ⥤
      @DerivedCategory (Modules A) inferInstance inferInstance
        (HasDerivedCategory.standard (Modules A)) :=
  @DerivedCategory.Q (Modules A) inferInstance inferInstance
    (HasDerivedCategory.standard (Modules A))

/-- Compatible coordinate isomorphisms and restriction maps for every profinite group.
The two directions of `coordinates` are actual internal linear cochain maps, inverse in
all degrees; naturality is in every equivariant coefficient map. Generalized evaluations
quantify over the entire profinite slice. Restrictions are fixed by precomposition, and
both coordinate squares are retained. The derived isomorphism is represented by these
same maps, after extension by zero in negative degrees.
Source: internal sheaf adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
structure InternalCochainCoordinates (A : Ring.{u}) (F : InternalFunctions A)
    (bar : ∀ J : ProfiniteGrp.{u}, BarDiagram (G := J) F) where
  homogeneous : ∀ J : ProfiniteGrp.{u}, InternalHomogeneousCochains F J
  coordinates : ∀ J : ProfiniteGrp.{u}, (homogeneous J).complex ≅ cochains (bar J)
  phi : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((homogeneous J).complex.obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, J)),
    inhomogeneousCoordinateValue (bar J) M n S
        ((((coordinates J).hom.app M).f n).hom.hom.app (op S) x) T f g =
      homogeneousCoordinateValue (homogeneous J) M n S x T f (coordinatePrefixes g)
  psi : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (c : sections A (((cochains (bar J)).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (n + 1) → C(T, J)),
    homogeneousCoordinateValue (homogeneous J) M n S
        ((((coordinates J).inv.app M).f n).hom.hom.app (op S) c) T f x =
      M.act T (x 0)
        (inhomogeneousCoordinateValue (bar J) M n S c T f (coordinateQuotients x))
  zero : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J),
    ((cochains (bar J)).obj M).X 0 ≅ M.module
  zero_eval : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (S : Profinite.{u})
    (c : sections A (((cochains (bar J)).obj M).X 0) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin 0 → C(T, J)),
    inhomogeneousCoordinateValue (bar J) M 0 S c T f g =
      M.module.X.obj.map f.op ((zero J M).hom.hom.hom.app (op S) c)
  phi_zero : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (S : Profinite.{u})
    (x : sections A (((homogeneous J).complex.obj M).X 0) S),
    ((((coordinates J).hom.app M).f 0 ≫ (zero J M).hom).hom.hom.app (op S) x) =
      homogeneousCoordinateValue (homogeneous J) M 0 S x S (𝟙 S) (fun _ ↦ 1)
  psi_zero : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (S : Profinite.{u})
    (m : sections A M.module S) (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, J)),
    homogeneousCoordinateValue (homogeneous J) M 0 S
        (((zero J M).inv ≫ ((coordinates J).inv.app M).f 0).hom.hom.app (op S) m)
        T f (fun _ ↦ g) = M.act T g (M.module.X.obj.map f.op m)
  homogeneousRestriction : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J),
    (homogeneous J).complex ⟶
      Profinite.CondensedAction.inflate v ⋙ (homogeneous K).complex
  inhomogeneousRestriction : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J),
    cochains (bar J) ⟶ Profinite.CondensedAction.inflate v ⋙ cochains (bar K)
  homogeneousRestriction_eval : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J)
    (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((homogeneous J).complex.obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, K)),
    homogeneousCoordinateValue (homogeneous K) ((Profinite.CondensedAction.inflate v).obj M)
        n S ((((homogeneousRestriction K J v).app M).f n).hom.hom.app (op S) x)
        T f g =
      homogeneousCoordinateValue (homogeneous J) M n S x T f
        (fun i ↦ v.toContinuousMap.comp (g i))
  inhomogeneousRestriction_eval : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J)
    (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains (bar J)).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, K)),
    inhomogeneousCoordinateValue (bar K) ((Profinite.CondensedAction.inflate v).obj M)
        n S ((((inhomogeneousRestriction K J v).app M).f n).hom.hom.app (op S) x)
        T f g =
      inhomogeneousCoordinateValue (bar J) M n S x T f
        (fun i ↦ v.toContinuousMap.comp (g i))
  restriction_phi : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J) (M : Equivariant A J),
    (homogeneousRestriction K J v).app M ≫
        (coordinates K).hom.app ((Profinite.CondensedAction.inflate v).obj M) =
      (coordinates J).hom.app M ≫ (inhomogeneousRestriction K J v).app M
  restriction_psi : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J) (M : Equivariant A J),
    (inhomogeneousRestriction K J v).app M ≫
        (coordinates K).inv.app ((Profinite.CondensedAction.inflate v).obj M) =
      (coordinates J).inv.app M ≫ (homogeneousRestriction K J v).app M
  derived : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J),
    ∃ e : (coordinateLocalization A).obj (extend ((homogeneous J).complex.obj M)) ≅
        (coordinateLocalization A).obj (extend ((cochains (bar J)).obj M)),
      e.hom = (coordinateLocalization A).map
          (HomologicalComplex.extendMap ((coordinates J).hom.app M)
            ComplexShape.embeddingUpNat) ∧
      e.inv = (coordinateLocalization A).map
          (HomologicalComplex.extendMap ((coordinates J).inv.app M)
            ComplexShape.embeddingUpNat)

```

## New

The same declarations are in the new module
`Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinateData`; the original module begins
with `public import Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinateData` and its
construction lemmas are proof-only imports. The original public imports are retained
through this public reexport. Only the new module-docstring paragraph differs below.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-! # Internal homogeneous and inhomogeneous cochain coordinates

Source: Stacks Project, Tag 0DVG, section-continuous-group-cohomology, displayed bar
boundary; internal sheaf adaptation in the DAG, not a verbatim assertion of that tag
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates).

The existing definitions are factored out for construction lemmas
(blueprint: def-sfb-internal-cochain-coordinate-data).

The specifications below retain internal module objects, their actual section evaluations,
and cochain maps. Existence is the final theorem; no module is chosen from an existence axiom.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar

/-- Prefix products of a tuple of continuous group-valued sections, starting with the unit.
Source: the homogeneous coordinate calculation following Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def coordinatePrefixes {J : ProfiniteGrp.{u}} {T : Profinite.{u}} {n : ℕ}
    (g : Fin n → C(T, J)) : Fin (n + 1) → C(T, J) :=
  fun i ↦ ((List.ofFn g).take i.val).prod

/-- Successive left quotients, preserving the order for noncommutative groups.
Source: the homogeneous coordinate calculation following Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def coordinateQuotients {J : ProfiniteGrp.{u}} {T : Profinite.{u}} {n : ℕ}
    (x : Fin (n + 1) → C(T, J)) : Fin n → C(T, J) :=
  fun i ↦ (x i.castSucc)⁻¹ * x i.succ

/-- Homogeneous equivariance is tested after every further profinite base change.
Source: the internal homogeneous-coordinate adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def IsHomogeneousSection {A : Ring.{u}} (F : InternalFunctions A) (J : ProfiniteGrp.{u})
    (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power J (n + 1))).obj M.module) S) : Prop :=
  ∀ (T : Profinite.{u}) (f : T ⟶ S) (a : C(T, J))
    (g : Fin (n + 1) → C(T, J)),
    (F.evaluate (power J (n + 1)) S M.module x).val T f
        (tupleMap (fun i ↦ a * g i)) =
      M.act T a ((F.evaluate (power J (n + 1)) S M.module x).val T f (tupleMap g))

/-- A presentation of the homogeneous submodule complex: the inclusion is injective on
sections, with exactly the homogeneous sections as its image, and the differential is
alternating deletion. The coefficient functor and inclusion use the original internal maps.
This specifies the subobject up to its unique inclusion-preserving isomorphism.
Source: internal sheaf adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
structure InternalHomogeneousCochains {A : Ring.{u}} (F : InternalFunctions A)
    (J : ProfiniteGrp.{u}) where
  complex : Equivariant A J ⥤ CochainComplex (Modules A) ℕ
  inclusion : ∀ (M : Equivariant A J) (n : ℕ),
    (complex.obj M).X n ⟶ (F.functor (power J (n + 1))).obj M.module
  injective : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u}),
    Function.Injective ((inclusion M n).hom.hom.app (op S))
  image : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((F.functor (power J (n + 1))).obj M.module) S),
    (∃ y : sections A ((complex.obj M).X n) S,
      (inclusion M n).hom.hom.app (op S) y = x) ↔ IsHomogeneousSection F J M n S x
  maps : ∀ {M N : Equivariant A J} (h : M ⟶ N) (n : ℕ),
    (complex.map h).f n ≫ inclusion N n =
      inclusion M n ≫ (F.functor (power J (n + 1))).map h.val
  differential : ∀ (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((complex.obj M).X n) S) (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin (n + 2) → C(T, J)),
    (F.evaluate (power J (n + 2)) S M.module
      (((complex.obj M).d n (n + 1) ≫ inclusion M (n + 1)).hom.hom.app (op S) x)).val
        T f (tupleMap g) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (F.evaluate (power J (n + 1)) S M.module
          ((inclusion M n).hom.hom.app (op S) x)).val T f
            (tupleMap (fun j ↦ g (i.succAbove j)))

/-- Evaluation of a homogeneous cochain via its actual submodule inclusion.
Source: internal sheaf adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def homogeneousCoordinateValue {A : Ring.{u}} {F : InternalFunctions A}
    {J : ProfiniteGrp.{u}} (H : InternalHomogeneousCochains F J) (M : Equivariant A J)
    (n : ℕ) (S : Profinite.{u}) (x : sections A ((H.complex.obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, J)) : sections A M.module T :=
  (F.evaluate (power J (n + 1)) S M.module
    ((H.inclusion M n).hom.hom.app (op S) x)).val T f (tupleMap g)

/-- Evaluation of an inhomogeneous cochain through the recorded bar-term isomorphism.
Source: Stacks 0DVG and the landed internal bar data
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def inhomogeneousCoordinateValue {A : Ring.{u}} {F : InternalFunctions A}
    {J : ProfiniteGrp.{u}} (B : BarDiagram (G := J) F) (M : Equivariant A J)
    (n : ℕ) (S : Profinite.{u}) (x : sections A (((cochains B).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, J)) : sections A M.module T :=
  (F.evaluate (power J n) S M.module ((B.term M n).hom.hom.hom.app (op S) x)).val
    T f (tupleMap g)

/-- The ordinary localization of integer-indexed internal-module complexes, using the
standard large localization in the stated size convention. This defines a functor, not a
new derived category or a choice of a comparison map.
Source: Mathlib derived-category localization
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
def coordinateLocalization (A : Ring.{u}) :
    CochainComplex (Modules A) ℤ ⥤
      @DerivedCategory (Modules A) inferInstance inferInstance
        (HasDerivedCategory.standard (Modules A)) :=
  @DerivedCategory.Q (Modules A) inferInstance inferInstance
    (HasDerivedCategory.standard (Modules A))

/-- Compatible coordinate isomorphisms and restriction maps for every profinite group.
The two directions of `coordinates` are actual internal linear cochain maps, inverse in
all degrees; naturality is in every equivariant coefficient map. Generalized evaluations
quantify over the entire profinite slice. Restrictions are fixed by precomposition, and
both coordinate squares are retained. The derived isomorphism is represented by these
same maps, after extension by zero in negative degrees.
Source: internal sheaf adaptation of Stacks 0DVG
(blueprint: lem-sfb-internal-homogeneous-cochain-coordinates). -/
structure InternalCochainCoordinates (A : Ring.{u}) (F : InternalFunctions A)
    (bar : ∀ J : ProfiniteGrp.{u}, BarDiagram (G := J) F) where
  homogeneous : ∀ J : ProfiniteGrp.{u}, InternalHomogeneousCochains F J
  coordinates : ∀ J : ProfiniteGrp.{u}, (homogeneous J).complex ≅ cochains (bar J)
  phi : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((homogeneous J).complex.obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, J)),
    inhomogeneousCoordinateValue (bar J) M n S
        ((((coordinates J).hom.app M).f n).hom.hom.app (op S) x) T f g =
      homogeneousCoordinateValue (homogeneous J) M n S x T f (coordinatePrefixes g)
  psi : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (c : sections A (((cochains (bar J)).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (x : Fin (n + 1) → C(T, J)),
    homogeneousCoordinateValue (homogeneous J) M n S
        ((((coordinates J).inv.app M).f n).hom.hom.app (op S) c) T f x =
      M.act T (x 0)
        (inhomogeneousCoordinateValue (bar J) M n S c T f (coordinateQuotients x))
  zero : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J),
    ((cochains (bar J)).obj M).X 0 ≅ M.module
  zero_eval : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (S : Profinite.{u})
    (c : sections A (((cochains (bar J)).obj M).X 0) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin 0 → C(T, J)),
    inhomogeneousCoordinateValue (bar J) M 0 S c T f g =
      M.module.X.obj.map f.op ((zero J M).hom.hom.hom.app (op S) c)
  phi_zero : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (S : Profinite.{u})
    (x : sections A (((homogeneous J).complex.obj M).X 0) S),
    ((((coordinates J).hom.app M).f 0 ≫ (zero J M).hom).hom.hom.app (op S) x) =
      homogeneousCoordinateValue (homogeneous J) M 0 S x S (𝟙 S) (fun _ ↦ 1)
  psi_zero : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J) (S : Profinite.{u})
    (m : sections A M.module S) (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, J)),
    homogeneousCoordinateValue (homogeneous J) M 0 S
        (((zero J M).inv ≫ ((coordinates J).inv.app M).f 0).hom.hom.app (op S) m)
        T f (fun _ ↦ g) = M.act T g (M.module.X.obj.map f.op m)
  homogeneousRestriction : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J),
    (homogeneous J).complex ⟶
      Profinite.CondensedAction.inflate v ⋙ (homogeneous K).complex
  inhomogeneousRestriction : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J),
    cochains (bar J) ⟶ Profinite.CondensedAction.inflate v ⋙ cochains (bar K)
  homogeneousRestriction_eval : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J)
    (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((homogeneous J).complex.obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin (n + 1) → C(T, K)),
    homogeneousCoordinateValue (homogeneous K) ((Profinite.CondensedAction.inflate v).obj M)
        n S ((((homogeneousRestriction K J v).app M).f n).hom.hom.app (op S) x)
        T f g =
      homogeneousCoordinateValue (homogeneous J) M n S x T f
        (fun i ↦ v.toContinuousMap.comp (g i))
  inhomogeneousRestriction_eval : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J)
    (M : Equivariant A J) (n : ℕ) (S : Profinite.{u})
    (x : sections A (((cochains (bar J)).obj M).X n) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, K)),
    inhomogeneousCoordinateValue (bar K) ((Profinite.CondensedAction.inflate v).obj M)
        n S ((((inhomogeneousRestriction K J v).app M).f n).hom.hom.app (op S) x)
        T f g =
      inhomogeneousCoordinateValue (bar J) M n S x T f
        (fun i ↦ v.toContinuousMap.comp (g i))
  restriction_phi : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J) (M : Equivariant A J),
    (homogeneousRestriction K J v).app M ≫
        (coordinates K).hom.app ((Profinite.CondensedAction.inflate v).obj M) =
      (coordinates J).hom.app M ≫ (inhomogeneousRestriction K J v).app M
  restriction_psi : ∀ (K J : ProfiniteGrp.{u}) (v : K →ₜ* J) (M : Equivariant A J),
    (inhomogeneousRestriction K J v).app M ≫
        (coordinates K).inv.app ((Profinite.CondensedAction.inflate v).obj M) =
      (coordinates J).inv.app M ≫ (homogeneousRestriction K J v).app M
  derived : ∀ (J : ProfiniteGrp.{u}) (M : Equivariant A J),
    ∃ e : (coordinateLocalization A).obj (extend ((homogeneous J).complex.obj M)) ≅
        (coordinateLocalization A).obj (extend ((cochains (bar J)).obj M)),
      e.hom = (coordinateLocalization A).map
          (HomologicalComplex.extendMap ((coordinates J).hom.app M)
            ComplexShape.embeddingUpNat) ∧
      e.inv = (coordinateLocalization A).map
          (HomologicalComplex.extendMap ((coordinates J).inv.app M)
            ComplexShape.embeddingUpNat)

```

The new proof-local `BarHomogeneousInclusion` structure specializes the existing
homogeneous-presentation conditions to the given bar complex and adds its uniquely
specified evaluation formula. It does not replace or alter an existing definition.

## Users

`tools/downstream.py Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinates` reports
zero downstream Lean modules, and a direct import search agrees. The assigned theorem
and all its definitions remain available under their original names. DAG parents still
use the original theorem and its unchanged statement. No other existing Lean module or
DAG node is edited; no direct importer needs adaptation or compilation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinates | T3 | Publicly reexports the unchanged definitions; proves the original existence theorem from construction lemmas. |

## Status

landed 20261026T083030-L-2253958 2026-10-26 (merge of deliver/T3/Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinates)
