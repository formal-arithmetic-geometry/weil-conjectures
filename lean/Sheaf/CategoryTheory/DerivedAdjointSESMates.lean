/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Sheaf.Algebra.Homology.ProductHomSesBoundary

/-!
# Derived adjunction mates of a short exact sequence

Source: Stacks Project, derived.tex, Tags 0152, 09T5, 0A8D; the combined signed
adjoint-sequence argument in the DAG (blueprint: lem-sfb-derived-adjoint-ses-mates).
The structures below package the specified data and conclusions of this one assertion.
The comparison condition retains maps of entire short exact sequences of complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB uA' vA' uB' vB' wA' wB'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- The ordinary and derived data specified in the adjoint-sequence assertion.
Source: derived.tex, Tags 0152 and 09T5 and the DAG's combined assertion
(blueprint: lem-sfb-derived-adjoint-ses-mates).
The comparison maps are part of total derived functors, not arbitrary object isomorphisms.
The resolving class computes the left derived functors and contains representatives of
all derived objects. Additivity of the right adjoints is recorded explicitly. -/
structure DerivedAdjointSESData
    (A : Type uA) (B : Type uB) [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] where
  E : Fin 3 → A ⥤ A
  H : Fin 3 → A ⥤ A
  E_zero : E 0 = 𝟭 A
  H_zero : H 0 = 𝟭 A
  addE (i : Fin 3) : (E i).Additive
  addH (i : Fin 3) : (H i).Additive
  exactE_left (i : Fin 3) : PreservesFiniteLimits (E i)
  exactE_right (i : Fin 3) : PreservesFiniteColimits (E i)
  adj (i : Fin 3) : E i ⊣ H i
  d : E 2 ⟶ E 1
  e : E 1 ⟶ E 0
  zero : d ≫ e = 0
  shortExact (X : A) : (ShortComplex.mk (d.app X) (e.app X)
    (NatTrans.congr_app zero X)).ShortExact
  P : B ⥤ A
  F : A ⥤ B
  addP : P.Additive
  addF : F.Additive
  adjPF : P ⊣ F
  resolving : Set (CochainComplex B ℤ)
  resolves (M : CochainComplex B ℤ) :
    ∃ (N : CochainComplex B ℤ) (f : N ⟶ M), N ∈ resolving ∧ QuasiIso f
  injectiveResolves (K : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ (∀ n : ℤ, Injective (I.X n)) ∧ QuasiIso f
  injectiveResolvesB (M : CochainComplex B ℤ) :
    ∃ (J : CochainComplex B ℤ) (f : M ⟶ J),
      J.IsKInjective ∧ (∀ n : ℤ, Injective (J.X n)) ∧ QuasiIso f
  LP : DerivedCategory B ⥤ DerivedCategory A
  shiftLP : LP.CommShift ℤ
  εP : DerivedCategory.Q ⋙ LP ⟶
    P.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  shiftεP : NatTrans.CommShift εP ℤ
  leftDerived : LP.IsLeftDerivedFunctor εP (HomologicalComplex.quasiIso B (.up ℤ))
  computesP (M : CochainComplex B ℤ) : M ∈ resolving → IsIso (εP.app M)
  R : Fin 3 → DerivedCategory A ⥤ DerivedCategory B
  shiftR (i : Fin 3) : (R i).CommShift ℤ
  ηR (i : Fin 3) : (H i ⋙ F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ R i
  shiftηR (i : Fin 3) : NatTrans.CommShift (ηR i) ℤ
  rightDerived (i : Fin 3) : (R i).IsRightDerivedFunctor (ηR i)
    (HomologicalComplex.quasiIso A (.up ℤ))

attribute [instance] DerivedAdjointSESData.addE DerivedAdjointSESData.addH
  DerivedAdjointSESData.exactE_left DerivedAdjointSESData.exactE_right
  DerivedAdjointSESData.addP DerivedAdjointSESData.addF
  DerivedAdjointSESData.shiftLP DerivedAdjointSESData.shiftR

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

namespace DerivedAdjointSESData

/-- The left derived composite `D(E_i) LP` (Lean writes composition left to right).
Source: derived.tex, Tag 09T5 (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def L (D : DerivedAdjointSESData A B) (i : Fin 3) :
    DerivedCategory B ⥤ DerivedCategory A := D.LP ⋙ (D.E i).mapDerivedCategory

/-- The cochain shift on the derived composite. Source: derived.tex, Tag 09T5
(blueprint: lem-sfb-derived-adjoint-ses-mates). -/
instance L_commShift (D : DerivedAdjointSESData A B) (i : Fin 3) :
    (D.L i).CommShift ℤ :=
  inferInstanceAs ((D.LP ⋙ (D.E i).mapDerivedCategory).CommShift ℤ)

/-- Its comparison on complexes, constructed from the two specified comparisons.
Source: derived.tex, Tag 09T5 (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def εL (D : DerivedAdjointSESData A B) (i : Fin 3) :
    DerivedCategory.Q ⋙ D.L i ⟶
      D.P.mapHomologicalComplex (.up ℤ) ⋙
        (D.E i).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight D.εP (D.E i).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (D.P.mapHomologicalComplex (.up ℤ))
      (D.E i).mapDerivedCategoryFactors.hom

/-- The ordinary right mate of the epimorphism in the left sequence.
Source: derived.tex, Tags 0152, 09T5 (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def er (D : DerivedAdjointSESData A B) : D.H 0 ⟶ D.H 1 :=
  conjugateEquiv (D.adj 0) (D.adj 1) D.e

/-- The ordinary right mate of the monomorphism in the left sequence.
Source: derived.tex, Tags 0152, 09T5 (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def dr (D : DerivedAdjointSESData A B) : D.H 1 ⟶ D.H 2 :=
  conjugateEquiv (D.adj 1) (D.adj 2) D.d

/-- The two ordinary mates have zero composite.
Source: derived.tex, Tag 09T5 and the DAG proof, step 1
(blueprint: lem-sfb-derived-adjoint-ses-mates).
Proof: transpose against any object. The composite becomes precomposition by
`d ≫ e = 0`; the adjunction bijection therefore identifies it with zero. -/
theorem mates_zero (D : DerivedAdjointSESData A B) : D.er ≫ D.dr = 0 := by
  sorry

/-- The actual left short sequence on a resolving complex, before localization.
Source: derived.tex, Tag 0152 (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def leftRow (D : DerivedAdjointSESData A B) (M : CochainComplex B ℤ) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex D.d (.up ℤ)).app
      ((D.P.mapHomologicalComplex (.up ℤ)).obj M))
    ((NatTrans.mapHomologicalComplex D.e (.up ℤ)).app
      ((D.P.mapHomologicalComplex (.up ℤ)).obj M))
    (by ext n; exact NatTrans.congr_app D.zero _)

/-- The actual reversed right sequence after applying the additive right adjoint `F`.
Source: derived.tex, Tag 0152 (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def rightRow (D : DerivedAdjointSESData A B) (I : CochainComplex A ℤ) :
    ShortComplex (CochainComplex B ℤ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (Functor.whiskerRight D.er D.F) (.up ℤ)).app I)
    ((NatTrans.mapHomologicalComplex (Functor.whiskerRight D.dr D.F) (.up ℤ)).app I)
    (by
      ext n
      change D.F.map (D.er.app (I.X n)) ≫ D.F.map (D.dr.app (I.X n)) = 0
      rw [← D.F.map_comp]
      have h := NatTrans.congr_app D.mates_zero (I.X n)
      change D.er.app (I.X n) ≫ D.dr.app (I.X n) = 0 at h
      rw [h, D.F.map_zero])

end DerivedAdjointSESData

/-- The canonical conclusions for one system: split mates, K-injectivity, derived
adjunctions, and both triangles with their resolution boundaries.
Source: derived.tex, Tags 0152, 09T5, 0A8D, DAG proof steps 1--5
(blueprint: lem-sfb-derived-adjoint-ses-mates).
The normalization equations quantify over every representative, so they include
independence of resolution, rather than choosing arbitrary triangle completions. -/
structure DerivedAdjointSESResult (D : DerivedAdjointSESData A B) where
  split (J : A) [Injective J] :
    Nonempty (ShortComplex.mk (D.er.app J) (D.dr.app J)
      (NatTrans.congr_app D.mates_zero J)).Splitting
  kInjective (i : Fin 3) (I : CochainComplex A ℤ) : I.IsKInjective →
    CochainComplex.IsKInjective (((D.H i).mapHomologicalComplex (.up ℤ)).obj I)
  computesR (i : Fin 3) (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((D.ηR i).app I)
  adj (i : Fin 3) : D.L i ⊣ D.R i
  normalize (i : Fin 3) (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
    (f : ((D.E i).mapHomologicalComplex (.up ℤ)).obj
      ((D.P.mapHomologicalComplex (.up ℤ)).obj M) ⟶ I) :
    (adj i).homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
      ((D.εL i).app M ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          (((D.adjPF.comp (D.adj i)).mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫
            (D.ηR i).app I
  l21 : D.L 2 ⟶ D.L 1
  l10 : D.L 1 ⟶ D.L 0
  b : D.L 0 ⟶ D.L 2 ⋙ shiftFunctor (DerivedCategory A) (1 : ℤ)
  r01 : D.R 0 ⟶ D.R 1
  r12 : D.R 1 ⟶ D.R 2
  δ : D.R 2 ⟶ D.R 0 ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ)
  left_distinguished (M : DerivedCategory B) :
    Triangle.mk (l21.app M) (l10.app M) (b.app M) ∈ distTriang (DerivedCategory A)
  right_distinguished (K : DerivedCategory A) :
    Triangle.mk (r01.app K) (r12.app K) (δ.app K) ∈ distTriang (DerivedCategory B)
  left_exact (M : CochainComplex B ℤ) : (D.leftRow M).ShortExact
  right_exact (I : CochainComplex A ℤ) [I.IsKInjective]
    [∀ n : ℤ, Injective (I.X n)] : (D.rightRow I).ShortExact
  left_first (M : CochainComplex B ℤ) :
    l21.app (DerivedCategory.Q.obj M) ≫ (D.εL 1).app M =
      (D.εL 2).app M ≫ DerivedCategory.Q.map (D.leftRow M).f
  left_second (M : CochainComplex B ℤ) :
    l10.app (DerivedCategory.Q.obj M) ≫ (D.εL 0).app M =
      (D.εL 1).app M ≫ DerivedCategory.Q.map (D.leftRow M).g
  left_boundary (M : CochainComplex B ℤ) : M ∈ D.resolving →
    b.app (DerivedCategory.Q.obj M) ≫ ((D.εL 2).app M)⟦(1 : ℤ)⟧' =
      (D.εL 0).app M ≫ DerivedCategory.triangleOfSESδ (left_exact M)
  right_split (I : CochainComplex A ℤ) [I.IsKInjective]
    [∀ n : ℤ, Injective (I.X n)] (n : ℤ) :
    Nonempty (((D.rightRow I).map (HomologicalComplex.eval B (.up ℤ) n)).Splitting)
  right_first (I : CochainComplex A ℤ) [I.IsKInjective]
    [∀ n : ℤ, Injective (I.X n)] :
    DerivedCategory.Q.map (D.rightRow I).f ≫ (D.ηR 1).app I =
      (D.ηR 0).app I ≫ r01.app (DerivedCategory.Q.obj I)
  right_second (I : CochainComplex A ℤ) [I.IsKInjective]
    [∀ n : ℤ, Injective (I.X n)] :
    DerivedCategory.Q.map (D.rightRow I).g ≫ (D.ηR 2).app I =
      (D.ηR 1).app I ≫ r12.app (DerivedCategory.Q.obj I)
  right_boundary (I : CochainComplex A ℤ) [I.IsKInjective]
    [∀ n : ℤ, Injective (I.X n)] :
    DerivedCategory.triangleOfSESδ (right_exact I) ≫ ((D.ηR 0).app I)⟦(1 : ℤ)⟧' =
      (D.ηR 2).app I ≫ δ.app (DerivedCategory.Q.obj I)
  first_mate : conjugateEquiv (adj 0) (adj 1) l10 = r01
  second_mate : conjugateEquiv (adj 1) (adj 2) l21 = r12
  boundary_mate (M : DerivedCategory B) (K : DerivedCategory A)
    (u : M ⟶ (D.R 2).obj K) :
    ((adj 0).homEquiv M (K⟦(1 : ℤ)⟧)).symm
      (u ≫ δ.app K ≫ ((D.R 0).commShiftIso (1 : ℤ)).inv.app K) =
        -(b.app M ≫ (((adj 2).homEquiv M K).symm u)⟦(1 : ℤ)⟧')

/-- Maps of whole short exact diagrams, with objectwise quasi-isomorphisms inverted.
Source: derived.tex, Tag 0152 and the DAG comparison hypothesis
(blueprint: lem-sfb-derived-adjoint-ses-mates).
A backwards step is allowed only for a chain diagram map whose localized map is
an isomorphism, equivalently whose three components are quasi-isomorphisms. -/
inductive DerivedAdjointSESDiagramPath :
    (U V : ShortComplex (CochainComplex A ℤ)) →
    (U.map DerivedCategory.Q ⟶ V.map DerivedCategory.Q) → Prop
  | forward {U V : ShortComplex (CochainComplex A ℤ)}
      (hU : U.ShortExact) (hV : V.ShortExact) (f : U ⟶ V) :
      DerivedAdjointSESDiagramPath U V (DerivedCategory.Q.mapShortComplex.map f)
  | backward {U V : ShortComplex (CochainComplex A ℤ)}
      (hU : U.ShortExact) (hV : V.ShortExact) (f : U ⟶ V)
      (q : U.map DerivedCategory.Q ≅ V.map DerivedCategory.Q)
      (hq : q.hom = DerivedCategory.Q.mapShortComplex.map f) :
      DerivedAdjointSESDiagramPath V U q.inv
  | comp {U V W : ShortComplex (CochainComplex A ℤ)}
      {f : U.map DerivedCategory.Q ⟶ V.map DerivedCategory.Q}
      {g : V.map DerivedCategory.Q ⟶ W.map DerivedCategory.Q}
      (hf : DerivedAdjointSESDiagramPath U V f)
      (hg : DerivedAdjointSESDiagramPath V W g) :
      DerivedAdjointSESDiagramPath U W (f ≫ g)

variable {A' : Type uA'} {B' : Type uB'} [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A'] [Abelian B'] [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']

/-- The specified comparison between two systems, including its lift to whole resolution
short exact diagrams. Source: derived.tex, Tag 0152, and the DAG proof step 6
(blueprint: lem-sfb-derived-adjoint-ses-mates).
The left-derived comparison for `s` is invertible on the three row objects and their
mapping cone; thus its shift comparison is the one computed by the cochain signs.
No boundary-commutativity hypothesis is imposed. -/
structure DerivedAdjointSESComparison
    (D : DerivedAdjointSESData A B) (D' : DerivedAdjointSESData A' B') where
  s : A ⥤ A'
  t : B ⥤ B'
  add_s : s.Additive
  add_t : t.Additive
  S : DerivedCategory A ⥤ DerivedCategory A'
  T : DerivedCategory B ⥤ DerivedCategory B'
  shiftS : S.CommShift ℤ
  shiftT : T.CommShift ℤ
  exactS : S.IsTriangulated
  exactT : T.IsTriangulated
  εS : DerivedCategory.Q ⋙ S ⟶
    s.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  εT : DerivedCategory.Q ⋙ T ⟶
    t.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  derivedS : S.IsLeftDerivedFunctor εS (HomologicalComplex.quasiIso A (.up ℤ))
  derivedT : T.IsLeftDerivedFunctor εT (HomologicalComplex.quasiIso B (.up ℤ))
  shiftεS : NatTrans.CommShift εS ℤ
  shiftεT : NatTrans.CommShift εT ℤ
  θ (i : Fin 3) : T ⋙ D'.L i ≅ D.L i ⋙ S
  shiftθ (i : Fin 3) : NatTrans.CommShift (θ i).hom ℤ
  diagrams (N : DerivedCategory B) :
    ∃ (M : CochainComplex B ℤ) (M' : CochainComplex B' ℤ)
      (x : DerivedCategory.Q.obj M ≅ N) (x' : DerivedCategory.Q.obj M' ≅ T.obj N),
      M ∈ D.resolving ∧ M' ∈ D'.resolving ∧
      IsIso (εS.app (D.leftRow M).X₁) ∧
      IsIso (εS.app (D.leftRow M).X₂) ∧
      IsIso (εS.app (D.leftRow M).X₃) ∧
      IsIso (εS.app (CochainComplex.mappingCone (D.leftRow M).f)) ∧
      ((D.leftRow M).map (s.mapHomologicalComplex (.up ℤ))).ShortExact ∧
      ∃ f : (D'.leftRow M').map DerivedCategory.Q ⟶
          ((D.leftRow M).map (s.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q,
        DerivedAdjointSESDiagramPath (D'.leftRow M')
          ((D.leftRow M).map (s.mapHomologicalComplex (.up ℤ))) f ∧
        (D'.εL 2).app M' ≫ f.τ₁ =
          (D'.L 2).map x'.hom ≫ (θ 2).hom.app N ≫
            S.map ((D.L 2).map x.inv) ≫ S.map ((D.εL 2).app M) ≫
              εS.app (D.leftRow M).X₁ ∧
        (D'.εL 1).app M' ≫ f.τ₂ =
          (D'.L 1).map x'.hom ≫ (θ 1).hom.app N ≫
            S.map ((D.L 1).map x.inv) ≫ S.map ((D.εL 1).app M) ≫
              εS.app (D.leftRow M).X₂ ∧
        (D'.εL 0).app M' ≫ f.τ₃ =
          (D'.L 0).map x'.hom ≫ (θ 0).hom.app N ≫
            S.map ((D.L 0).map x.inv) ≫ S.map ((D.εL 0).app M) ≫
              εS.app (D.leftRow M).X₃

attribute [instance] DerivedAdjointSESComparison.add_s DerivedAdjointSESComparison.add_t
  DerivedAdjointSESComparison.shiftS DerivedAdjointSESComparison.shiftT
  DerivedAdjointSESComparison.exactS DerivedAdjointSESComparison.exactT

/-- The comparison map is exactly the transpose of `θ`, followed by the image of the
normalized counit and the supplied map `φ`. Source: derived.tex, Tag 09T5, and the DAG
comparison formula (blueprint: lem-sfb-derived-adjoint-ses-mates). -/
def derivedAdjointSESComparisonMate
    {D : DerivedAdjointSESData A B} {D' : DerivedAdjointSESData A' B'}
    (O : DerivedAdjointSESResult D) (O' : DerivedAdjointSESResult D')
    (C : DerivedAdjointSESComparison D D') (i : Fin 3)
    (K : DerivedCategory A) (K' : DerivedCategory A') (φ : C.S.obj K ⟶ K') :
    C.T.obj ((D.R i).obj K) ⟶ (D'.R i).obj K' :=
  (O'.adj i).homEquiv _ _
    ((C.θ i).hom.app ((D.R i).obj K) ≫ C.S.map ((O.adj i).counit.app K) ≫ φ)

/-- The canonical derived adjoint sequence and compatibility of its comparison mates.
Source: derived.tex, Tags 0152, 09T5, 0A8D; combined signed cochain argument in the DAG
(blueprint: lem-sfb-derived-adjoint-ses-mates).

Proof, following the eight DAG steps:
1. For injective J, adjunction identifies Hom into the mate sequence with the exact
   sequence Hom(E₀X,J) → Hom(E₁X,J) → Hom(E₂X,J). The cokernel property gives the
   kernel, and injectivity extends maps across E₂X → E₁X. Lift the identity of H₂J
   to obtain a section. The right adjoints are additive by transposing sums.
2. The right-adjoint-preserves-K-injective lemma applies to each exact Eᵢ. The split
   sequence in each degree stays split under additive F. Total right derivation is
   computed on these K-injectives; F need not preserve K-injectives.
3. Apply the SES triangle lemma and the degreewise split formula π d s for its boundary.
   Maps of representatives give maps of these triangles. Full faithfulness on
   K-injectives and preservation of homotopy equivalences imply independence of every
   chosen resolution and naturality under the normalized derived comparisons.
4. Apply resolving-derived-adjunction normalization to EᵢP ⊣ FHᵢ. Exactness of Eᵢ
   identifies its left derived functor with D(Eᵢ) LP. Termwise transposition identifies
   the signed product Hom complexes, since naturality respects d f - (-1)^n f d.
5. The product-Hom SES boundary lemma identifies transposition of δ u with minus
   u-sharp shifted and composed with the left boundary. On the right a graded lift s u
   has projected differential π d s u. Resolving representatives extend this signed
   identity to all derived objects. The first two arrows are ordinary mates.
6. Each whole-diagram map in the comparison induces a map of canonical SES triangles.
   The additive functor s preserves the cone matrix and the signed shift differential.
   Its derived comparison, computed on the row and cone, therefore transports the
   canonical boundary. Invert the objectwise quasi-isomorphisms and compose along the
   diagram path. This proves all three left comparison squares, including the boundary.
7. Transpose the right connecting square. Apply the signed identity of step 5 in the
   primed system, the left boundary square of step 6, and the unprimed identity at
   id of R₂K. The two minus signs cancel. Naturality of θ₀ and normalized shift
   compatibility identify the result with the transpose of β₀[1] δ. Bijectivity of
   adjunction proves equality; no βᵢ is inverted.
8. For each earlier arrow, transpose its desired square and use the counit equation
   for mates, the corresponding left square, and naturality of θ. These two squares
   and step 7 give the morphism of the specified right triangles. -/
theorem derivedAdjointSESMates
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    (D : DerivedAdjointSESData A B) :
    ∃ O : DerivedAdjointSESResult D,
      ∀ {A' : Type uA'} {B' : Type uB'} [Category.{vA'} A'] [Category.{vB'} B']
        [Abelian A'] [Abelian B'] [HasDerivedCategory.{wA'} A']
        [HasDerivedCategory.{wB'} B']
        [IsGrothendieckAbelian.{vA'} A'] [IsGrothendieckAbelian.{vB'} B']
        (D' : DerivedAdjointSESData A' B') (O' : DerivedAdjointSESResult D')
        (C : DerivedAdjointSESComparison D D')
        (K : DerivedCategory A) (K' : DerivedCategory A') (φ : C.S.obj K ⟶ K'),
        C.T.map (O.r01.app K) ≫ derivedAdjointSESComparisonMate O O' C 1 K K' φ =
          derivedAdjointSESComparisonMate O O' C 0 K K' φ ≫ O'.r01.app K' ∧
        C.T.map (O.r12.app K) ≫ derivedAdjointSESComparisonMate O O' C 2 K K' φ =
          derivedAdjointSESComparisonMate O O' C 1 K K' φ ≫ O'.r12.app K' ∧
        C.T.map (O.δ.app K) ≫
            (C.T.commShiftIso (1 : ℤ)).hom.app ((D.R 0).obj K) ≫
              (derivedAdjointSESComparisonMate O O' C 0 K K' φ)⟦(1 : ℤ)⟧' =
          derivedAdjointSESComparisonMate O O' C 2 K K' φ ≫ O'.δ.app K' := by
  sorry

end CategoryTheory
