# Algebra.ActiveRootNormalization structural constructors

## Reason

The three independent proof steps need the same actual pushout and integral-closure
constructions. Keeping their definitions in the theorem module would create an import
cycle. Relocate the 22 existing constructors, unchanged in name, universe, signature,
visibility and body, to `Sheaf.RingTheory.ActiveRootNormalizationData`. The item publicly
imports that module, preserving access to every constructor. Only their docstring node
tags change to the new definition node. No object is chosen from an unproved existence
statement, and no definition gains a proof hole.

The unused public import `Sheaf.RingTheory.StrictHenselizationPresentationIn` is removed.
The theorem uses the geometric strict-henselization colimit, not that separate presentation
structure. Other retained public dependencies are re-exported through the data module or
remain explicit in the item. Its theorem signature is unchanged.

## Old

In `Sheaf.RingTheory.ActiveRootTowerNormalizationSplitting`:

```lean
/-- A commutative algebra as an under-object. Source: Stacks, Tag 01ZM.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
abbrev asAlgebra {R : CommRingCat.{u}} (X : Under R) : CommAlgCat.{u} R :=
  (commAlgCatEquivUnder R).inverse.obj X

/-- The integral closure with its structural map. Source: Stacks, Tag 0CBF.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def closure {R : CommRingCat.{u}} (X : Under R) : Under R :=
  CommRingCat.mkUnder R (integralClosure R (asAlgebra X))

/-- Inclusion of the actual integral closure in its ambient ring. Source: Tag 0CBF.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def closureInclusion {R : CommRingCat.{u}} (X : Under R) : closure X ⟶ X :=
  (integralClosure R (asAlgebra X)).val.toUnder

/-- The diagonal finite product, including the empty product. Source: ILO IX 2.1.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def diagonal (R : CommRingCat.{u}) (d : ℕ) : Under R :=
  CommRingCat.mkUnder R (Fin d → R)

/-- The simultaneous-root diagram as algebras over its coefficient ring.
Source: the canonical power transitions in the node, Stacks Tag 01ZM.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def rootDiagram {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (p : ℕ) :
    RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p} ⥤ Under (CommRingCat.of R) :=
  (simultaneousRootDiagram t {n : ℕ+ | Nat.Coprime (n : ℕ) p}).toUnder
    (.of R) (fun n ↦ CommRingCat.ofHom (algebraMap R (pthRootAlgebra n.1 r R t)))
    (fun h ↦ CommRingCat.hom_ext (RingHom.ext (AlgHom.commutes
      (simultaneousRootTransition t (leOfHom h)))))

/-- The boundary localization map, with empty product one. Source: ILO IX 2.1.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def puncture {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :
    CommRingCat.of R ⟶ CommRingCat.of (Localization.Away (∏ i, t i)) :=
  CommRingCat.ofHom (algebraMap R _)

/-- Restrict the root system to any enumerated active set and puncture by the full product.
Source: Stacks Tag 01ZM and ILO IX 2.1, active-root system.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def activeDiagram {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ) :
    RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p} ⥤
      Under (CommRingCat.of (Localization.Away (∏ i, t i))) :=
  rootDiagram (fun i ↦ algebraMap B A (t (active i))) p ⋙
    Under.map (CommRingCat.ofHom (algebraMap B A)) ⋙ Under.pushout (puncture t)

/-- The localized full root stage as an algebra over B[1/f]. Source: ILO IX 2.1.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def fullPuncturedStage {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (m : ℕ+) :
    Under (CommRingCat.of (Localization.Away (∏ i, t i))) :=
  (Under.pushout (puncture t)).obj
    (CommRingCat.mkUnder (.of B) (pthRootAlgebra m r B t))

/-- The full root stage after the specified strict-local scalar extension.
Source: ILO IX 2.1, S_m = A tensor_B C_m; pushout equals tensor product.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def strictStage {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) : Under (CommRingCat.of A) :=
  (Under.pushout (CommRingCat.ofHom (algebraMap B A))).obj
    (CommRingCat.mkUnder (.of B) (pthRootAlgebra m r B t))

/-- Structural map C_m -> S_m, the first coprojection of the tensor pushout.
Source: ILO IX 2.1 (blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def strictStageMap {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) :
    CommRingCat.of (pthRootAlgebra m r B t) ⟶ (strictStage (A := A) t m).right :=
  pushout.inl (CommRingCat.ofHom (algebraMap B (pthRootAlgebra m r B t)))
    (CommRingCat.ofHom (algebraMap B A))

/-- Puncture of the strict-local full stage, as an S_m-algebra. Source: ILO IX 2.1.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def strictPuncture {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) : Under (strictStage (A := A) t m).right :=
  (Under.pushout (CommRingCat.ofHom (algebraMap B A) ≫
    (strictStage (A := A) t m).hom)).obj (Under.mk (puncture t))

/-- D_m as a C_m-algebra, using the actual localization and tensor pushouts.
Source: Stacks Tag 0CBF, ambient algebra in the second application.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def ambient {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :
    Under (CommRingCat.of (pthRootAlgebra m r B t)) :=
  (Under.map (pushout.inl
    (CommRingCat.ofHom (algebraMap B (pthRootAlgebra m r B t))) (puncture t))).obj
    ((Under.pushout (fullPuncturedStage t m).hom).obj D)

/-- The base change of D_m to the actual strict-local full stage.
Source: Stacks Tag 0CBF (blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
abbrev strictAmbient {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :=
  (Under.pushout (strictStageMap (A := A) t m)).obj (ambient t m D)

/-- The base change of E_m itself; associativity identifies it with E_m tensor_B A.
Source: Stacks Tag 0CBF (blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
abbrev strictClosure {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :=
  (Under.pushout (strictStageMap (A := A) t m)).obj (closure (ambient t m D))

/-- The canonical D -> D_m tensor coprojection. Source: the displayed D_m formula.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def ambientInclusion {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :
    D.right ⟶ (ambient t m D).right :=
  pushout.inl D.hom (fullPuncturedStage t m).hom

/-- The canonical D -> D_m tensor_C_m S_m coprojections. Source: Tag 0CBF.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def strictAmbientInclusion {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :
    D.right ⟶ (strictAmbient (A := A) t m D).right :=
  ambientInclusion t m D ≫ pushout.inl (ambient t m D).hom (strictStageMap (A := A) t m)

/-- S_m[1/f] with its canonical B[1/f]-structure. Source: ILO IX 2.1.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def strictPunctureOverBase {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) :
    Under (CommRingCat.of (Localization.Away (∏ i, t i))) :=
  Under.mk (pushout.inl (puncture t)
    (CommRingCat.ofHom (algebraMap B A) ≫ (strictStage (A := A) t m).hom))

/-- The localization map on each coordinate. Source: Stacks Tag 0CBF.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def diagonalLocalization {R : CommRingCat.{u}} (U : Under R) (d : ℕ) :
    (diagonal R d).right ⟶ (diagonal U.right d).right :=
  CommRingCat.ofHom (RingHom.pi (fun j : Fin d ↦
    U.hom.hom.comp (Pi.evalRingHom (fun _ : Fin d ↦ R) j)))

/-- Coprojection of the unpunctured active algebra into Q_m.
Source: Stacks Tag 01ZM (blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
def activeInclusion {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ)
    (m : RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p}) :
    CommRingCat.of (pthRootAlgebra m.1 s A (fun i ↦ algebraMap B A (t (active i)))) ⟶
      ((activeDiagram (A := A) t active p).obj m).right :=
  pushout.inl
    (CommRingCat.ofHom ((algebraMap A
      (pthRootAlgebra m.1 s A (fun i ↦ algebraMap B A (t (active i))))).comp
      (algebraMap B A))) (puncture t)

/-- The punctured active-root colimit in commutative algebras over B[1/f].
Source: Stacks Tag 01ZM (blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
abbrev activeColimit {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ) :=
  colimit (activeDiagram (A := A) t active p)

/-- Scalar extension of D to a specified B[1/f]-algebra. Source: Stacks Tag 01ZM.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
abbrev extend {R : CommRingCat.{u}} (D Q : Under R) :=
  (Under.pushout Q.hom).obj D

/-- The structural D-coprojection in a scalar extension. Source: Stacks Tag 01ZM.
(blueprint: lem-sfb-active-root-tower-normalization-splitting). -/
abbrev extendInclusion {R : CommRingCat.{u}} (D Q : Under R) :=
  pushout.inl D.hom Q.hom
```

## New

In `Sheaf.RingTheory.ActiveRootNormalizationData`, publicly imported by the original module:

```lean
/-- A commutative algebra as an under-object. Source: Stacks, Tag 01ZM.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
abbrev asAlgebra {R : CommRingCat.{u}} (X : Under R) : CommAlgCat.{u} R :=
  (commAlgCatEquivUnder R).inverse.obj X

/-- The integral closure with its structural map. Source: Stacks, Tag 0CBF.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def closure {R : CommRingCat.{u}} (X : Under R) : Under R :=
  CommRingCat.mkUnder R (integralClosure R (asAlgebra X))

/-- Inclusion of the actual integral closure in its ambient ring. Source: Tag 0CBF.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def closureInclusion {R : CommRingCat.{u}} (X : Under R) : closure X ⟶ X :=
  (integralClosure R (asAlgebra X)).val.toUnder

/-- The diagonal finite product, including the empty product. Source: ILO IX 2.1.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def diagonal (R : CommRingCat.{u}) (d : ℕ) : Under R :=
  CommRingCat.mkUnder R (Fin d → R)

/-- The simultaneous-root diagram as algebras over its coefficient ring.
Source: the canonical power transitions in the node, Stacks Tag 01ZM.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def rootDiagram {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (p : ℕ) :
    RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p} ⥤ Under (CommRingCat.of R) :=
  (simultaneousRootDiagram t {n : ℕ+ | Nat.Coprime (n : ℕ) p}).toUnder
    (.of R) (fun n ↦ CommRingCat.ofHom (algebraMap R (pthRootAlgebra n.1 r R t)))
    (fun h ↦ CommRingCat.hom_ext (RingHom.ext (AlgHom.commutes
      (simultaneousRootTransition t (leOfHom h)))))

/-- The boundary localization map, with empty product one. Source: ILO IX 2.1.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def puncture {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) :
    CommRingCat.of R ⟶ CommRingCat.of (Localization.Away (∏ i, t i)) :=
  CommRingCat.ofHom (algebraMap R _)

/-- Restrict the root system to any enumerated active set and puncture by the full product.
Source: Stacks Tag 01ZM and ILO IX 2.1, active-root system.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def activeDiagram {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ) :
    RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p} ⥤
      Under (CommRingCat.of (Localization.Away (∏ i, t i))) :=
  rootDiagram (fun i ↦ algebraMap B A (t (active i))) p ⋙
    Under.map (CommRingCat.ofHom (algebraMap B A)) ⋙ Under.pushout (puncture t)

/-- The localized full root stage as an algebra over B[1/f]. Source: ILO IX 2.1.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def fullPuncturedStage {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (m : ℕ+) :
    Under (CommRingCat.of (Localization.Away (∏ i, t i))) :=
  (Under.pushout (puncture t)).obj
    (CommRingCat.mkUnder (.of B) (pthRootAlgebra m r B t))

/-- The full root stage after the specified strict-local scalar extension.
Source: ILO IX 2.1, S_m = A tensor_B C_m; pushout equals tensor product.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def strictStage {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) : Under (CommRingCat.of A) :=
  (Under.pushout (CommRingCat.ofHom (algebraMap B A))).obj
    (CommRingCat.mkUnder (.of B) (pthRootAlgebra m r B t))

/-- Structural map C_m -> S_m, the first coprojection of the tensor pushout.
Source: ILO IX 2.1 (blueprint: def-sfb-active-root-normalization-pushout-data). -/
def strictStageMap {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) :
    CommRingCat.of (pthRootAlgebra m r B t) ⟶ (strictStage (A := A) t m).right :=
  pushout.inl (CommRingCat.ofHom (algebraMap B (pthRootAlgebra m r B t)))
    (CommRingCat.ofHom (algebraMap B A))

/-- Puncture of the strict-local full stage, as an S_m-algebra. Source: ILO IX 2.1.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def strictPuncture {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) : Under (strictStage (A := A) t m).right :=
  (Under.pushout (CommRingCat.ofHom (algebraMap B A) ≫
    (strictStage (A := A) t m).hom)).obj (Under.mk (puncture t))

/-- D_m as a C_m-algebra, using the actual localization and tensor pushouts.
Source: Stacks Tag 0CBF, ambient algebra in the second application.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def ambient {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :
    Under (CommRingCat.of (pthRootAlgebra m r B t)) :=
  (Under.map (pushout.inl
    (CommRingCat.ofHom (algebraMap B (pthRootAlgebra m r B t))) (puncture t))).obj
    ((Under.pushout (fullPuncturedStage t m).hom).obj D)

/-- The base change of D_m to the actual strict-local full stage.
Source: Stacks Tag 0CBF (blueprint: def-sfb-active-root-normalization-pushout-data). -/
abbrev strictAmbient {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :=
  (Under.pushout (strictStageMap (A := A) t m)).obj (ambient t m D)

/-- The base change of E_m itself; associativity identifies it with E_m tensor_B A.
Source: Stacks Tag 0CBF (blueprint: def-sfb-active-root-normalization-pushout-data). -/
abbrev strictClosure {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :=
  (Under.pushout (strictStageMap (A := A) t m)).obj (closure (ambient t m D))

/-- The canonical D -> D_m tensor coprojection. Source: the displayed D_m formula.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def ambientInclusion {B : Type u} [CommRing B] {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :
    D.right ⟶ (ambient t m D).right :=
  pushout.inl D.hom (fullPuncturedStage t m).hom

/-- The canonical D -> D_m tensor_C_m S_m coprojections. Source: Tag 0CBF.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def strictAmbientInclusion {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+)
    (D : Under (CommRingCat.of (Localization.Away (∏ i, t i)))) :
    D.right ⟶ (strictAmbient (A := A) t m D).right :=
  ambientInclusion t m D ≫ pushout.inl (ambient t m D).hom (strictStageMap (A := A) t m)

/-- S_m[1/f] with its canonical B[1/f]-structure. Source: ILO IX 2.1.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def strictPunctureOverBase {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r : ℕ} (t : Fin r → B) (m : ℕ+) :
    Under (CommRingCat.of (Localization.Away (∏ i, t i))) :=
  Under.mk (pushout.inl (puncture t)
    (CommRingCat.ofHom (algebraMap B A) ≫ (strictStage (A := A) t m).hom))

/-- The localization map on each coordinate. Source: Stacks Tag 0CBF.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
def diagonalLocalization {R : CommRingCat.{u}} (U : Under R) (d : ℕ) :
    (diagonal R d).right ⟶ (diagonal U.right d).right :=
  CommRingCat.ofHom (RingHom.pi (fun j : Fin d ↦
    U.hom.hom.comp (Pi.evalRingHom (fun _ : Fin d ↦ R) j)))

/-- Coprojection of the unpunctured active algebra into Q_m.
Source: Stacks Tag 01ZM (blueprint: def-sfb-active-root-normalization-pushout-data). -/
def activeInclusion {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ)
    (m : RootTowerIndex {n : ℕ+ | Nat.Coprime (n : ℕ) p}) :
    CommRingCat.of (pthRootAlgebra m.1 s A (fun i ↦ algebraMap B A (t (active i)))) ⟶
      ((activeDiagram (A := A) t active p).obj m).right :=
  pushout.inl
    (CommRingCat.ofHom ((algebraMap A
      (pthRootAlgebra m.1 s A (fun i ↦ algebraMap B A (t (active i))))).comp
      (algebraMap B A))) (puncture t)

/-- The punctured active-root colimit in commutative algebras over B[1/f].
Source: Stacks Tag 01ZM (blueprint: def-sfb-active-root-normalization-pushout-data). -/
abbrev activeColimit {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    {r s : ℕ} (t : Fin r → B) (active : Fin s → Fin r) (p : ℕ) :=
  colimit (activeDiagram (A := A) t active p)

/-- Scalar extension of D to a specified B[1/f]-algebra. Source: Stacks Tag 01ZM.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
abbrev extend {R : CommRingCat.{u}} (D Q : Under R) :=
  (Under.pushout Q.hom).obj D

/-- The structural D-coprojection in a scalar extension. Source: Stacks Tag 01ZM.
(blueprint: def-sfb-active-root-normalization-pushout-data). -/
abbrev extendInclusion {R : CommRingCat.{u}} (D Q : Under R) :=
  pushout.inl D.hom Q.hom
```

## Users

`tools/downstream.py Sheaf.RingTheory.ActiveRootTowerNormalizationSplitting` reports zero
Lean downstream modules, and the exact direct-import search also returns none. Therefore
there are no importer adaptations or importer compiles to perform. The DAG parent below
still cites the original theorem; its attachment and dependency remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ActiveRootTowerNormalizationSplitting | C1 | Publicly re-exports the relocated constructors and proves the original theorem from three smaller steps. |
| Sheaf.AlgebraicGeometry.SNCTameRootEtaleExtension | DAG parent; no current Lean import | Its dependency on the unchanged original theorem remains valid; no file edit. |

## Status

landed 20261026T081159-L-1853738 2026-10-26 (merge of deliver/C1/Sheaf.RingTheory.ActiveRootTowerNormalizationSplitting)
