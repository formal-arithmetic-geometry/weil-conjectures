/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec
public import Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually
public import Sheaf.AlgebraicGeometry.NagataMorphismEqEventually
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# A selected finite-stage model of a morphism

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 353
(blueprint: def-nagata-morphism-descent).

The record retains the choices of affine charts, open descent, coefficient lifts and
relations, and overlap witnesses. The resulting morphism is the gluing at the prescribed
finite upper bound. Only the proofs needed for that gluing are postponed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
variable (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
variable (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
variable {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
variable (p : X₀ ⟶ D.obj (op i₀)) (q : Y₀ ⟶ D.obj (op i₀))
variable [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
variable [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
variable (phi : (baseChangeCone D c p).pt ⟶ (baseChangeCone D c q).pt)
variable (d : I → I → I) (hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j) (r : LinearOrder I)

/-- All displayed choices in finite-stage morphism descent. Empty finite chart families
are permitted. Source: blueprint node order 353
(blueprint: def-nagata-morphism-descent).

`openSelected` identifies the chosen open with `nagataQCOpenDescent` using its full
cover, basic-open presentation and lift data. `U` covers the intersection with the
inverse image of the base chart. `localMap` is the chosen generator-and-relation map
at its coefficient stage. `localGenerators` and `localRelations` say exactly how its
ring map is induced by the lifted generators. The rebased maps are its transports.
The cover and overlap stages are the recorded dependency constructions, rather than
arbitrary stages at which the desired global conclusion is assumed. -/
structure NagataMorphismDescentData
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    (p : X₀ ⟶ D.obj (op i₀)) (q : Y₀ ⟶ D.obj (op i₀))
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (phi : (baseChangeCone D c p).pt ⟶ (baseChangeCone D c q).pt)
    (d : I → I → I) (hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j) (r : LinearOrder I) where
  limitOver : phi ≫ pullback.snd q (c.π.app (op i₀)) =
    pullback.snd p (c.π.app (op i₀))
  J : ℕ
  T : Fin J → (D.obj (op i₀)).Opens
  affineT : ∀ j, IsAffineOpen (T j)
  coverT : ⨆ j, T j = ⊤
  K : Fin J → ℕ
  V : ∀ j, Fin (K j) → Y₀.Opens
  affineV : ∀ j k, IsAffineOpen (V j k)
  coverV : ⨆ j, ⨆ k, V j k = ⊤
  targetToBase : ∀ j k, (V j k).toScheme ⟶ (T j).toScheme
  targetOver : ∀ j k, targetToBase j k ≫ (T j).ι = (V j k).ι ≫ q
  finitePresentation : ∀ j k, (targetToBase j k).appTop.hom.FinitePresentation
  n : ∀ j, Fin (K j) → ℕ
  m : ∀ j, Fin (K j) → ℕ
  presentation : ∀ j k,
    @Algebra.Presentation Γ((T j).toScheme, ⊤) Γ((V j k).toScheme, ⊤)
      (Fin (n j k)) (Fin (m j k)) _ _ (targetToBase j k).appTop.hom.toAlgebra
  generators : ∀ j k, Fin (n j k) → Γ((V j k).toScheme, ⊤)
  generators_eq : ∀ j k, generators j k =
    @Algebra.Generators.val _ _ _ _ _ (targetToBase j k).appTop.hom.toAlgebra
      (@Algebra.Presentation.toGenerators _ _ _ _ _ _
        (targetToBase j k).appTop.hom.toAlgebra (presentation j k))
  relations : ∀ j k, Fin (m j k) → MvPolynomial (Fin (n j k)) Γ((T j).toScheme, ⊤)
  relations_eq : ∀ j k, relations j k =
    @Algebra.Presentation.relation _ _ _ _ _ _
      (targetToBase j k).appTop.hom.toAlgebra (presentation j k)
  W : ∀ j, Fin (K j) → (baseChangeCone D c p).pt.Opens
  W_eq : ∀ j k, W j k =
    phi ⁻¹ᵁ (pullback.fst q (c.π.app (op i₀)) ⁻¹ᵁ V j k)
  compactW : ∀ j k, IsCompact (W j k : Set (baseChangeCone D c p).pt)
  a : ∀ j, Fin (K j) → ℕ
  A : ∀ j k, Fin (a j k) → X₀.Opens
  affineA : ∀ j k b, IsAffineOpen (A j k b)
  coverA : ∀ j k, ⨆ b, A j k b = ⊤
  b : ∀ j k, Fin (a j k) → ℕ
  basicSection : ∀ j k t, Fin (b j k t) → Γ((baseChangeCone D c p).pt,
    pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ A j k t)
  basicPresentation : ∀ j k t,
    W j k ⊓ (pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ A j k t) =
      ⨆ z, (baseChangeCone D c p).pt.basicOpen (basicSection j k t z)
  openLiftStage : ∀ j k, Fin (a j k) → I
  openLiftGE : ∀ j k t, i₀ ≤ openLiftStage j k t
  openLift : ∀ j k t, Fin (b j k t) →
    Γ((baseChangeDiagram D p).obj (Over.mk (homOfLE (openLiftGE j k t)).op),
      pullback.fst p (D.map (homOfLE (openLiftGE j k t)).op) ⁻¹ᵁ A j k t)
  openLift_eq : ∀ j k t z,
    ((baseChangeCone D c p).π.app (Over.mk (homOfLE (openLiftGE j k t)).op)).appLE
      (pullback.fst p (D.map (homOfLE (openLiftGE j k t)).op) ⁻¹ᵁ A j k t)
      (pullback.fst p (c.π.app (op i₀)) ⁻¹ᵁ A j k t)
      (nagataQCOpenDescent_limit_chart_le D c p
        (Over.mk (homOfLE (openLiftGE j k t)).op) (A j k t)) (openLift j k t z) =
        basicSection j k t z
  openStage : ∀ j, Fin (K j) → I
  openGE : ∀ j k, i₀ ≤ openStage j k
  descended : ∀ j k,
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE (openGE j k)).op)).Opens
  openSelected : ∀ j k,
    (⟨openStage j k, openGE j k, descended j k⟩ :
      Σ' w : I, Σ' hw : i₀ ≤ w,
        ((baseChangeDiagram D p).obj (Over.mk (homOfLE hw).op)).Opens) =
      nagataQCOpenDescent D c hc i₀ p (W j k) (compactW j k)
        (a j k) (A j k) (affineA j k) (coverA j k) (b j k) (basicSection j k)
        (basicPresentation j k) (openLiftStage j k) (openLiftGE j k) (openLift j k)
        (openLift_eq j k) d hd r
  L : ∀ j, Fin (K j) → ℕ
  U : ∀ j k, Fin (L j k) →
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE (openGE j k)).op)).Opens
  affineU : ∀ j k l, IsAffineOpen (U j k l)
  coverU : ∀ j k, ⨆ l, U j k l = descended j k ⊓
    ((pullback.snd p (D.map (homOfLE (openGE j k)).op) ≫
      D.map (homOfLE (openGE j k)).op) ⁻¹ᵁ T j)
  /-- A later generator-lifting stage and a still later relation-vanishing stage. -/
  generatorStage : ∀ j k, Fin (L j k) → I
  generatorGE : ∀ j k l, openStage j k ≤ generatorStage j k l
  coefficientStage : ∀ j k, Fin (L j k) → I
  coefficientGE : ∀ j k l, generatorStage j k l ≤ coefficientStage j k l
  /-- Canonical transport of the source charts to any later stage. -/
  chart : ∀ j k (_l : Fin (L j k)) (s : I) (hs : openStage j k ≤ s),
    ((baseChangeDiagram D p).obj
      (Over.mk (homOfLE ((openGE j k).trans hs)).op)).Opens
  chart_eq : ∀ j k l s (hs : openStage j k ≤ s), chart j k l s hs =
    ((baseChangeDiagram D p).map
      (Over.homMk (homOfLE hs).op (Subsingleton.elim _ _))) ⁻¹ᵁ U j k l
  /-- The lifted generators at the first coefficient stage. -/
  generatorLift : ∀ j k l, Fin (n j k) →
    Γ((chart j k l (generatorStage j k l) (generatorGE j k l)).toScheme, ⊤)
  /-- Transported lifts and the resulting map at the relation-vanishing stage. -/
  coefficientLift : ∀ j k l, Fin (n j k) →
    Γ((chart j k l (coefficientStage j k l)
      ((generatorGE j k l).trans (coefficientGE j k l))).toScheme, ⊤)
  coefficientTransition : ∀ j k l,
    (chart j k l (coefficientStage j k l)
      ((generatorGE j k l).trans (coefficientGE j k l))).toScheme ⟶
    (chart j k l (generatorStage j k l) (generatorGE j k l)).toScheme
  coefficientTransition_eq : ∀ j k l,
    coefficientTransition j k l ≫
      (chart j k l (generatorStage j k l) (generatorGE j k l)).ι =
    (chart j k l (coefficientStage j k l)
      ((generatorGE j k l).trans (coefficientGE j k l))).ι ≫
    (baseChangeDiagram D p).map
      (Over.homMk (homOfLE (coefficientGE j k l)).op (Subsingleton.elim _ _))
  coefficientLift_eq : ∀ j k l z, coefficientLift j k l z =
    (coefficientTransition j k l).appTop (generatorLift j k l z)
  localMap : ∀ j k l,
    (chart j k l (coefficientStage j k l)
      ((generatorGE j k l).trans (coefficientGE j k l))).toScheme ⟶ (V j k).toScheme
  localGenerators : ∀ j k l z,
    (localMap j k l).appTop (generators j k z) = coefficientLift j k l z
  localOver : ∀ j k l, localMap j k l ≫ (V j k).ι ≫ q =
    (chart j k l (coefficientStage j k l)
      ((generatorGE j k l).trans (coefficientGE j k l))).ι ≫
    pullback.fst p (D.map
      (homOfLE ((openGE j k).trans
        ((generatorGE j k l).trans (coefficientGE j k l)))).op) ≫ p
  localRelations : ∀ j k l z,
    (relations j k z).eval₂
      ((localMap j k l).appTop.hom.comp (targetToBase j k).appTop.hom)
      (coefficientLift j k l) = 0
  /-- Limit restriction of phi to the chart, with its canonical comparison map. -/
  limitChart : ∀ (j : Fin J) (k : Fin (K j)) (_l : Fin (L j k)), (baseChangeCone D c p).pt.Opens
  limitChart_eq : ∀ j k l, limitChart j k l =
    (baseChangeCone D c p).π.app (Over.mk (homOfLE (openGE j k)).op) ⁻¹ᵁ U j k l
  limitToGenerator : ∀ j k l, (limitChart j k l).toScheme ⟶
    (chart j k l (generatorStage j k l) (generatorGE j k l)).toScheme
  limitToGenerator_eq : ∀ j k l,
    limitToGenerator j k l ≫
      (chart j k l (generatorStage j k l) (generatorGE j k l)).ι =
    (limitChart j k l).ι ≫ (baseChangeCone D c p).π.app
      (Over.mk (homOfLE ((openGE j k).trans (generatorGE j k l))).op)
  limitMap : ∀ j k l, (limitChart j k l).toScheme ⟶ (V j k).toScheme
  limitMap_eq : ∀ j k l, limitMap j k l ≫ (V j k).ι =
    (limitChart j k l).ι ≫ phi ≫ pullback.fst q (c.π.app (op i₀))
  generatorLift_eq : ∀ j k l z,
    (limitToGenerator j k l).appTop (generatorLift j k l z) =
      (limitMap j k l).appTop (generators j k z)
  /-- F₀ contains the base and all stages chosen before rebase. -/
  F₀ : Finset I
  F₀_eq : F₀ = {i₀} ∪
    (Finset.univ.biUnion fun j => Finset.univ.biUnion fun k =>
      insert (openStage j k) ((Finset.univ.image (openLiftStage j k)) ∪
        (Finset.univ.biUnion fun l =>
          {generatorStage j k l, coefficientStage j k l})))
  prime : I
  prime_eq : prime = directedFiniteUpperBound i₀ d r F₀
  primeGE : i₀ ≤ prime
  chartPrimeGE : ∀ j k l, coefficientStage j k l ≤ prime
  /-- Transported chart maps, retaining the canonical comparison morphisms. -/
  mapAt : ∀ j k l s (hs : coefficientStage j k l ≤ s),
    (chart j k l s
      (((generatorGE j k l).trans (coefficientGE j k l)).trans hs)).toScheme ⟶
      (baseChangeDiagram D q).obj (Over.mk
        (homOfLE ((openGE j k).trans
          (((generatorGE j k l).trans (coefficientGE j k l)).trans hs))).op)
  toCoefficient : ∀ j k l s (hs : coefficientStage j k l ≤ s),
    (chart j k l s
      (((generatorGE j k l).trans (coefficientGE j k l)).trans hs)).toScheme ⟶
    (chart j k l (coefficientStage j k l)
      ((generatorGE j k l).trans (coefficientGE j k l))).toScheme
  toCoefficient_eq : ∀ j k l s (hs : coefficientStage j k l ≤ s),
    toCoefficient j k l s hs ≫
      (chart j k l (coefficientStage j k l)
        ((generatorGE j k l).trans (coefficientGE j k l))).ι =
    (chart j k l s
      (((generatorGE j k l).trans (coefficientGE j k l)).trans hs)).ι ≫
      (baseChangeDiagram D p).map
        (Over.homMk (homOfLE hs).op (Subsingleton.elim _ _))
  mapAt_fst : ∀ j k l s (hs : coefficientStage j k l ≤ s),
    mapAt j k l s hs ≫ pullback.fst q (D.map
      (homOfLE ((openGE j k).trans
        (((generatorGE j k l).trans (coefficientGE j k l)).trans hs))).op) =
      toCoefficient j k l s hs ≫ localMap j k l ≫ (V j k).ι
  mapAt_snd : ∀ j k l s (hs : coefficientStage j k l ≤ s),
    mapAt j k l s hs ≫ pullback.snd q (D.map
      (homOfLE ((openGE j k).trans
        (((generatorGE j k l).trans (coefficientGE j k l)).trans hs))).op) =
    (chart j k l s
      (((generatorGE j k l).trans (coefficientGE j k l)).trans hs)).ι ≫
      pullback.snd p (D.map
        (homOfLE ((openGE j k).trans
          (((generatorGE j k l).trans (coefficientGE j k l)).trans hs))).op)
  /-- The rebased source is qcqs, and its finite union has full limit inverse image. -/
  compactPrime : CompactSpace
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op))
  separatedPrime : QuasiSeparatedSpace
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op))
  unionOpen : ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op)).Opens
  unionOpen_eq : unionOpen = ⨆ j, ⨆ k, ⨆ l,
    chart j k l prime
      (((generatorGE j k l).trans (coefficientGE j k l)).trans (chartPrimeGE j k l))
  compactUnion : IsCompact (unionOpen : Set
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op)))
  unionLimit_eq :
    pullback.fst (pullback.snd p (D.map (homOfLE primeGE).op))
      (c.π.app (op prime)) ⁻¹ᵁ unionOpen =
    pullback.fst (pullback.snd p (D.map (homOfLE primeGE).op))
      (c.π.app (op prime)) ⁻¹ᵁ ⊤
  unionStage : I
  unionSelected : unionStage =
    @nagataQCOpenEqualityStage I _ _ _ D c hc (inferInstance) prime _
      (pullback.snd p (D.map (homOfLE primeGE).op)) compactPrime separatedPrime
      unionOpen ⊤ compactUnion isCompact_univ unionLimit_eq d r
  /-- Each pair of charts supplies exactly the dependency's overlap equality choices. -/
  overlap : (Σ j, Σ k : Fin (K j), Fin (L j k)) →
    (Σ j, Σ k : Fin (K j), Fin (L j k)) →
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op)).Opens
  overlap_eq : ∀ x y, overlap x y =
    chart x.1 x.2.1 x.2.2 prime
      (((generatorGE x.1 x.2.1 x.2.2).trans (coefficientGE x.1 x.2.1 x.2.2)).trans
        (chartPrimeGE x.1 x.2.1 x.2.2)) ⊓
    chart y.1 y.2.1 y.2.2 prime
      (((generatorGE y.1 y.2.1 y.2.2).trans (coefficientGE y.1 y.2.1 y.2.2)).trans
        (chartPrimeGE y.1 y.2.1 y.2.2))
  leftLE : ∀ x y, overlap x y ≤ chart x.1 x.2.1 x.2.2 prime
    (((generatorGE x.1 x.2.1 x.2.2).trans (coefficientGE x.1 x.2.1 x.2.2)).trans
      (chartPrimeGE x.1 x.2.1 x.2.2))
  rightLE : ∀ x y, overlap x y ≤ chart y.1 y.2.1 y.2.2 prime
    (((generatorGE y.1 y.2.1 y.2.2).trans (coefficientGE y.1 y.2.1 y.2.2)).trans
      (chartPrimeGE y.1 y.2.1 y.2.2))
  overlapLeft : ∀ x y, (overlap x y).toScheme ⟶
    (baseChangeDiagram D q).obj (Over.mk (homOfLE primeGE).op)
  overlapRight : ∀ x y, (overlap x y).toScheme ⟶
    (baseChangeDiagram D q).obj (Over.mk (homOfLE primeGE).op)
  overlapLeft_eq : ∀ x y, overlapLeft x y =
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op)).homOfLE (leftLE x y) ≫
      mapAt x.1 x.2.1 x.2.2 prime (chartPrimeGE x.1 x.2.1 x.2.2)
  overlapRight_eq : ∀ x y, overlapRight x y =
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE primeGE).op)).homOfLE (rightLE x y) ≫
      mapAt y.1 y.2.1 y.2.2 prime (chartPrimeGE y.1 y.2.1 y.2.2)
  overlapOverLeft : ∀ x y, overlapLeft x y ≫
    pullback.snd q (D.map (homOfLE primeGE).op) =
    (overlap x y).ι ≫ pullback.snd p (D.map (homOfLE primeGE).op)
  overlapOverRight : ∀ x y, overlapRight x y ≫
    pullback.snd q (D.map (homOfLE primeGE).op) =
    (overlap x y).ι ≫ pullback.snd p (D.map (homOfLE primeGE).op)
  compactBasePrime : CompactSpace (D.obj (op prime))
  separatedBasePrime : QuasiSeparatedSpace (D.obj (op prime))
  compactOverlap : ∀ x y, CompactSpace (overlap x y).toScheme
  separatedOverlap : ∀ x y, QuasiSeparatedSpace (overlap x y).toScheme
  fpOverlap : ∀ x y, LocallyOfFinitePresentation
    ((overlap x y).ι ≫ pullback.snd p (D.map (homOfLE primeGE).op))
  qcOverlap : ∀ x y, QuasiCompact
    ((overlap x y).ι ≫ pullback.snd p (D.map (homOfLE primeGE).op))
  qsOverlap : ∀ x y, QuasiSeparated
    ((overlap x y).ι ≫ pullback.snd p (D.map (homOfLE primeGE).op))
  fpTargetPrime : LocallyOfFinitePresentation (pullback.snd q (D.map (homOfLE primeGE).op))
  qcTargetPrime : QuasiCompact (pullback.snd q (D.map (homOfLE primeGE).op))
  qsTargetPrime : QuasiSeparated (pullback.snd q (D.map (homOfLE primeGE).op))
  overlapData : ∀ x y,
    @NagataMorphismEqualityStageData I _ _ _ D c hc (inferInstance) prime
      compactBasePrime separatedBasePrime (overlap x y).toScheme
      ((baseChangeDiagram D q).obj (Over.mk (homOfLE primeGE).op))
      (compactOverlap x y) (separatedOverlap x y)
      ((overlap x y).ι ≫ pullback.snd p (D.map (homOfLE primeGE).op))
      (pullback.snd q (D.map (homOfLE primeGE).op))
      (fpOverlap x y) (qcOverlap x y) (qsOverlap x y)
      fpTargetPrime qcTargetPrime qsTargetPrime
      (overlapLeft x y) (overlapRight x y)
      (overlapOverLeft x y) (overlapOverRight x y) d r
  overlapStage : (Σ j, Σ k : Fin (K j), Fin (L j k)) →
    (Σ j, Σ k : Fin (K j), Fin (L j k)) → I
  overlapSelected : ∀ x y, overlapStage x y = nagataMorphismEqualityStage (overlapData x y)

namespace NagataMorphismDescentData

variable {D c hc i₀ p q phi d hd r}

/-- The final finite set of stages F, including the initial choices, rebase, union-cover
and every overlap stage. Source: blueprint node order 353
(blueprint: def-nagata-morphism-descent). -/
noncomputable def stages
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) : Finset I := by
  classical
  exact data.F₀ ∪ {data.prime, data.unionStage} ∪
    (Finset.univ.biUnion fun x => Finset.univ.image (data.overlapStage x))

/-- The prescribed common stage λ_phi = u(F). Source: blueprint node order 353
(blueprint: def-nagata-morphism-descent). -/
noncomputable def stage
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) : I :=
  directedFiniteUpperBound i₀ d r data.stages

/-- The common stage dominates each local coefficient stage. Source: blueprint node order
353 (blueprint: def-nagata-morphism-descent).
Proof: all coefficient stages belong to F₀ by its displayed formula, hence to F;
apply `le_directedFiniteUpperBound` with hd. -/
theorem coefficient_le_stage
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) (j : Fin data.J)
    (k : Fin (data.K j)) (l : Fin (data.L j k)) :
    data.coefficientStage j k l ≤ data.stage := by
  sorry

/-- The final stage is in the original indexing tail. Source: blueprint node order 353
(blueprint: def-nagata-morphism-descent).
Proof: i₀ belongs to F₀ and hence F; apply `le_directedFiniteUpperBound` with hd. -/
theorem base_le_stage
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) : i₀ ≤ data.stage := by
  sorry

/-- The transported affine charts cover at the chosen stage. Source: blueprint node order
353 (blueprint: def-nagata-morphism-descent).
Proof: the descended opens have inverse images W by `nagataQCOpenDescent_spec`.
Intersecting with the base chart preserves that inverse image since phi is over S.
The U cover those intersections, so unionOpen has full limit inverse image. At unionStage,
`nagataQCOpenEqEventually` makes the transported union equal the whole source. The selected
stage dominates prime and unionStage by `le_directedFiniteUpperBound`. The chart comparison
maps and `chart_eq` identify that transported union with the union in the conclusion. -/
theorem charts_cover
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) :
    (⨆ j, ⨆ k, ⨆ l, data.chart j k l data.stage
      (((data.generatorGE j k l).trans (data.coefficientGE j k l)).trans
        (data.coefficient_le_stage j k l)) :
      ((baseChangeDiagram D p).obj
        (Over.mk (homOfLE data.base_le_stage).op)).Opens) = ⊤ := by
  sorry

/-- The transported maps agree on overlaps at the chosen stage. Source: blueprint node
order 353 (blueprint: def-nagata-morphism-descent).
Proof: generatorLift_eq identifies the limit images with phi on each affine chart.
localRelations and localGenerators define the corresponding R-algebra maps. Therefore their
limit base changes agree. Each overlapData is the exact choice record for that pair.
`nagataMorphismEqEventually` gives equality at every stage above its overlapStage.
Every such stage is in F; `le_directedFiniteUpperBound` puts it below stage. Canonical
base-change comparisons (chart_eq, toCoefficient_eq and mapAt projections) identify these
maps with the two maps in this conclusion. -/
theorem charts_agree
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r)
    (x y : Σ j, Σ k : Fin (data.K j), Fin (data.L j k)) :
    pullback.fst
      (data.chart x.1 x.2.1 x.2.2 data.stage
        (((data.generatorGE x.1 x.2.1 x.2.2).trans
          (data.coefficientGE x.1 x.2.1 x.2.2)).trans
          (data.coefficient_le_stage x.1 x.2.1 x.2.2))).ι
      (data.chart y.1 y.2.1 y.2.2 data.stage
        (((data.generatorGE y.1 y.2.1 y.2.2).trans
          (data.coefficientGE y.1 y.2.1 y.2.2)).trans
          (data.coefficient_le_stage y.1 y.2.1 y.2.2))).ι ≫
      data.mapAt x.1 x.2.1 x.2.2 data.stage
        (data.coefficient_le_stage x.1 x.2.1 x.2.2) =
    pullback.snd
      (data.chart x.1 x.2.1 x.2.2 data.stage
        (((data.generatorGE x.1 x.2.1 x.2.2).trans
          (data.coefficientGE x.1 x.2.1 x.2.2)).trans
          (data.coefficient_le_stage x.1 x.2.1 x.2.2))).ι
      (data.chart y.1 y.2.1 y.2.2 data.stage
        (((data.generatorGE y.1 y.2.1 y.2.2).trans
          (data.coefficientGE y.1 y.2.1 y.2.2)).trans
          (data.coefficient_le_stage y.1 y.2.1 y.2.2))).ι ≫
      data.mapAt y.1 y.2.1 y.2.2 data.stage
        (data.coefficient_le_stage y.1 y.2.1 y.2.2) := by
  sorry

end NagataMorphismDescentData

/-- Glue the transported affine maps at exactly λ_phi = u(F), retaining the chosen stage
and its tail-index witness. Source: blueprint node order 353
(blueprint: def-nagata-morphism-descent).
The definition depends on all the displayed covers, lifts, relations, and equality witnesses.
Its base-change comparison with phi is the subsequent node lemma-nagata-morphism-descends. -/
noncomputable def nagataMorphismDescentGluedMap
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) :
    Σ' s : I, Σ' hs : i₀ ≤ s,
      (baseChangeDiagram D p).obj (Over.mk (homOfLE hs).op) ⟶
      (baseChangeDiagram D q).obj (Over.mk (homOfLE hs).op) := by
  classical
  let U : (Σ j, Σ k : Fin (data.K j), Fin (data.L j k)) →
      ((baseChangeDiagram D p).obj (Over.mk (homOfLE data.base_le_stage).op)).Opens :=
    fun x => data.chart x.1 x.2.1 x.2.2 data.stage
      (((data.generatorGE x.1 x.2.1 x.2.2).trans
        (data.coefficientGE x.1 x.2.1 x.2.2)).trans
        (data.coefficient_le_stage x.1 x.2.1 x.2.2))
  let cover := Scheme.openCoverOfIsOpenCover _ U (by
    simpa only [TopologicalSpace.IsOpenCover, U, iSup_sigma] using data.charts_cover)
  exact ⟨data.stage, data.base_le_stage, cover.glueMorphisms
    (fun x => data.mapAt x.1 x.2.1 x.2.2 data.stage
      (data.coefficient_le_stage x.1 x.2.1 x.2.2)) data.charts_agree⟩

/-- The glued map is over the selected base stage. Source: blueprint node order 353
(blueprint: def-nagata-morphism-descent).
Proof: each mapAt has the prescribed second projection by mapAt_snd. The restrictions
of the glued map are the mapAt by `Scheme.Cover.ι_glueMorphisms`. Thus its composite
with the target's second projection and the source's second projection agree on the
cover; `Scheme.Cover.hom_ext` makes them equal globally. -/
theorem nagataMorphismDescentGluedMap_over
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) :
    (nagataMorphismDescentGluedMap D c hc i₀ p q phi d hd r data).2.2 ≫
      pullback.snd q (D.map (homOfLE
        (nagataMorphismDescentGluedMap D c hc i₀ p q phi d hd r data).2.1).op) =
      pullback.snd p (D.map (homOfLE
        (nagataMorphismDescentGluedMap D c hc i₀ p q phi d hd r data).2.1).op) := by
  sorry

/-- The finite-stage model of phi, as a morphism over S at the selected stage u(F).
Source: blueprint node order 353 (blueprint: def-nagata-morphism-descent).
The raw map is computed by affine-chart gluing; the named over-base theorem supplies
only the proof that this map commutes with the structural morphisms. -/
noncomputable def nagataMorphismDescent
    (data : NagataMorphismDescentData D c hc i₀ p q phi d hd r) :
    Σ' s : I, Σ' hs : i₀ ≤ s,
      (Over.mk (pullback.snd p (D.map (homOfLE hs).op)) ⟶
        Over.mk (pullback.snd q (D.map (homOfLE hs).op))) :=
  ⟨(nagataMorphismDescentGluedMap D c hc i₀ p q phi d hd r data).1,
    (nagataMorphismDescentGluedMap D c hc i₀ p q phi d hd r data).2.1,
    Over.homMk (nagataMorphismDescentGluedMap D c hc i₀ p q phi d hd r data).2.2
      (nagataMorphismDescentGluedMap_over D c hc i₀ p q phi d hd r data)⟩

end AlgebraicGeometry
