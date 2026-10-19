/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.SheafExt
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Noetherian.Defs

import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Sheaf.RingTheory.RelativeRegularEquationsBaseChange
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.RingTheory.KoszulRegularSequenceDualComplex
import Sheaf.RingTheory.RegularSequenceConormal
import Sheaf.RingTheory.RegularSequenceKoszulRegular
import Mathlib.RingTheory.MvPolynomial.Localization
import Sheaf.TraceFormula.TwoTermPerfectDeterminant

/-!
# Canonical adjunction for flat local complete intersections

Source: Stacks Project, Duality for Schemes, Tags 0B6V, 0BQZ and 0E2Y;
Perfect Complexes, Tags 0FJX and 0FJY (blueprint: lem-trf-flat-lci-canonical-adjunction).

## Main definitions

* `FlatLCIPresentation`: the actual regular polynomial chart and its adjunction module.
* `FlatLCIAdjunctionSystem`: the global lines, normalized transitions and coherent base change.
* `FlatLCIPresentation.HasExtIdentification` and `.HasDualityModel`: the local Ext/duality models.

## Main statement

* `exists_flatLCICanonicalAdjunction`: existence of the full normalized construction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
namespace AlgebraicGeometry

/-- A polynomial regular presentation, including its open source and ambient affine-space
chart. The regularity condition is local at every point of the closed source, so it also
makes sense after arbitrary, possibly non-Noetherian, base change.
Source: Stacks, Tag 0B6V (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
structure FlatLCIPresentation {X S : Scheme.{u}} (p : X ⟶ S) (d : ℕ) (U : X.Opens) where
  n : ℕ
  c : ℕ
  rank_eq : n = c + d
  P : Scheme.{u}
  ambient : P ⟶ AffineSpace (ULift.{u} (Fin n)) S
  ambient_open : IsOpenImmersion ambient
  i : U.toScheme ⟶ P
  closed : IsClosedImmersion i
  factor : i ≫ ambient ≫ pullback.fst _ _ = U.ι ≫ p
  regular : ∀ x : U.toScheme, ∃ A : P.affineOpens, i x ∈ A.1 ∧
    ∃ f : Fin c → Γ(P, A.1), Ideal.span (Set.range f) = i.ker.ideal A ∧
      ∀ q : PrimeSpectrum Γ(P, A.1), i.ker.ideal A ≤ q.asIdeal →
        RingTheory.Sequence.IsRegular (Localization.AtPrime q.asIdeal)
          (List.ofFn fun j ↦ algebraMap Γ(P, A.1) (Localization.AtPrime q.asIdeal) (f j))

/-- The conormal module is the tensor pullback of the immersion ideal, hence `I/I²`.
Source: Stacks, Tag 01R2 (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentation.conormal {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : FlatLCIPresentation p d U) :
    U.toScheme.Modules :=
  (Scheme.Modules.tensorPullback C.i).obj C.i.ker.toModules

/-- The ambient differentials restricted to the closed source by tensor pullback.
Source: Stacks, Tags 01UM, 0B6V (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentation.differentials
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : FlatLCIPresentation p d U) :
    U.toScheme.Modules :=
  (Scheme.Modules.tensorPullback C.i).obj
    (C.ambient ≫ pullback.fst _ _).relativeDifferentials

/-- The actual adjunction module `(∧ᶜ C)∨ ⊗ ∧ⁿ V`, using sheafified exterior powers.
Source: Stacks, Tag 0BQZ (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentation.line {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : FlatLCIPresentation p d U) :
    U.toScheme.Modules :=
  SheafOfModules.homObj (R := U.toScheme.sheaf)
      (Scheme.Modules.exteriorSheaf C.conormal C.c)
      (SheafOfModules.unit U.toScheme.ringCatSheaf) ⊗
    Scheme.Modules.exteriorSheaf C.differentials C.n

/-- A cartesian change of base, retaining the maps to the original family. No finiteness
or Noetherian assumption is placed on the new base.
Source: Stacks, Tag 0E2Y (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
structure FlatLCIBaseChange {X S : Scheme.{u}} (p : X ⟶ S) where
  X' : Scheme.{u}
  S' : Scheme.{u}
  p' : X' ⟶ S'
  g : X' ⟶ X
  b : S' ⟶ S
  cartesian : IsPullback g p' p b

/-- The identity change of base, used to include the original family in the same system.
Source: Stacks, Tag 0E2Y (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIBaseChange.identity {X S : Scheme.{u}} (p : X ⟶ S) : FlatLCIBaseChange p :=
  ⟨X, S, p, 𝟙 X, 𝟙 S, IsPullback.of_id_fst⟩

/-- The canonical conormal differential is characterized on actual ideal sections by
`[f] ↦ df`. In particular no arbitrary map between the two modules can satisfy this
predicate: the pulled-back ideal sections locally generate the conormal module.
Source: Stacks, Tag 08SL (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIPresentation.IsConormalDifferential {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C : FlatLCIPresentation p d U)
    (δ : C.conormal ⟶ C.differentials) : Prop :=
  ∀ (A : C.P.Opens) (f : Γ(C.i.ker.toModules, A)),
    δ.app (C.i ⁻¹ᵁ A) (Scheme.Modules.tensorPullbackSection C.i C.i.ker.toModules A f) =
      Scheme.Modules.tensorPullbackSection C.i
        (C.ambient ≫ pullback.fst _ _).relativeDifferentials A
          ((C.ambient ≫ pullback.fst _ _).relativeDifferentialsDerivation.d (X := op A)
            (C.i.ker.toModulesι.app A f))

/-- The two-term determinant formula, with the scheme-module tensor structure explicit
through the return type. Source: Stacks, Tag 0FJX
(blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def flatLCITwoTermLine (Y : Scheme.{u}) (A V : Y.Modules) (a n : ℕ) :
    Y.Modules :=
  SheafOfModules.homObj (R := Y.sheaf) (Scheme.Modules.exteriorSheaf A a)
    (SheafOfModules.unit Y.ringCatSheaf) ⊗ Scheme.Modules.exteriorSheaf V n

/-- Determinant of a quasi-isomorphism of two-term finite locally free complexes.
This is an algebraic normalization, not an arbitrary isomorphism of line bundles.
On every trivializing open form the exact cone
`0 → A → B ⊕ V → W → 0`, with maps `(a,-dA)` and `(dB,v)`. If `M` is the matrix whose
columns are the images of a basis of A followed by lifts of a basis of W, relative to
the ordered bases of B and V, the determinant map carries the A,V orientation to
`det(M)⁻¹` times the B,W orientation. The equation below avoids division and therefore
also applies over rings with zero divisors. Identity complexes give a triangular matrix
of determinant one; adjoining `[E → E]` gives evaluation, including the empty wedge.
Source: Stacks, Tags 0FJX, 0FJM (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def IsFlatLCIDeterminantComparison {Y : Scheme.{u}}
    (A B V W : Y.Modules) (a b n m : ℕ) (hr : a + m = b + n)
    (dA : A ⟶ V) (dB : B ⟶ W) (f : A ⟶ B) (g : V ⟶ W)
    (e : flatLCITwoTermLine Y A V a n ≅ flatLCITwoTermLine Y B W b m) : Prop :=
  dA ≫ g = f ≫ dB ∧
  ∀ (O : Y.Opens)
    (ba : Module.Basis (Fin a) Γ(Y, O) Γ(A, O))
    (bb : Module.Basis (Fin b) Γ(Y, O) Γ(B, O))
    (bv : Module.Basis (Fin n) Γ(Y, O) Γ(V, O))
    (bw : Module.Basis (Fin m) Γ(Y, O) Γ(W, O))
    (α : Γ(SheafOfModules.homObj (R := Y.sheaf) (Scheme.Modules.exteriorSheaf A a)
      (SheafOfModules.unit Y.ringCatSheaf), O))
    (β : Γ(SheafOfModules.homObj (R := Y.sheaf) (Scheme.Modules.exteriorSheaf B b)
      (SheafOfModules.unit Y.ringCatSheaf), O))
    (l : Fin m → Γ(B, O) × Γ(V, O))
    (M : Matrix (Fin (b + n)) (Fin (b + n)) Γ(Y, O)),
    α.app (op (Over.mk (𝟙 O))) (Scheme.Modules.exteriorSheafSection A a O ba) = (1 : Γ(Y, O)) →
    β.app (op (Over.mk (𝟙 O))) (Scheme.Modules.exteriorSheafSection B b O bb) = (1 : Γ(Y, O)) →
    (∀ j, dB.app O (l j).1 + g.app O (l j).2 = bw j) →
    (∀ j,
      ((∑ k : Fin b, M (Fin.castAdd n k) j • bb k),
        (∑ k : Fin n, M (Fin.natAdd b k) j • bv k)) =
          Fin.append (fun k ↦ (f.app O (ba k), -dA.app O (ba k))) l
            (Fin.cast hr.symm j)) →
    M.det • e.hom.app O (Scheme.Modules.tmulSection (X := Y) α
      (Scheme.Modules.exteriorSheafSection V n O bv)) =
        Scheme.Modules.tmulSection (X := Y)
          (M := SheafOfModules.homObj (R := Y.sheaf) (Scheme.Modules.exteriorSheaf B b)
            (SheafOfModules.unit Y.ringCatSheaf))
          (N := Scheme.Modules.exteriorSheaf W m) β (Scheme.Modules.exteriorSheafSection W m O bw)

/-- A normalized ambient refinement between two presentations on the same open.
The ideal map is specified by its actual inclusion into the structure sheaf, and the
map on differentials by the universal derivations. These formulas uniquely determine
both maps, even though their existence is proved together with the adjunction theorem.
Source: Stacks, Tags 01R4, 01UV, 0BZJ
(blueprint: lem-trf-flat-lci-canonical-adjunction). -/
structure FlatLCIPresentationRefinement {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C D : FlatLCIPresentation p d U) where
  q : D.P ⟶ C.P
  source_eq : D.i ≫ q = C.i
  base_eq : q ≫ (C.ambient ≫ pullback.fst _ _) = D.ambient ≫ pullback.fst _ _
  idealMap : (Scheme.Modules.tensorPullback q).obj C.i.ker.toModules ⟶ D.i.ker.toModules
  ideal_normal : ∀ (A : C.P.Opens) (s : Γ(C.i.ker.toModules, A)),
    D.i.ker.toModulesι.app (q ⁻¹ᵁ A)
      (idealMap.app (q ⁻¹ᵁ A)
        (Scheme.Modules.tensorPullbackSection q C.i.ker.toModules A s)) =
          q.app A (C.i.ker.toModulesι.app A s)
  differentialMap : (Scheme.Modules.tensorPullback q).obj
      (C.ambient ≫ pullback.fst _ _).relativeDifferentials ⟶
        (D.ambient ≫ pullback.fst _ _).relativeDifferentials
  differential_normal : ∀ (A : C.P.Opens) (s : Γ(C.P, A)),
    differentialMap.app (q ⁻¹ᵁ A)
      (Scheme.Modules.tensorPullbackSection q
        (C.ambient ≫ pullback.fst _ _).relativeDifferentials A
          ((C.ambient ≫ pullback.fst _ _).relativeDifferentialsDerivation.d (X := op A) s)) =
      (D.ambient ≫ pullback.fst _ _).relativeDifferentialsDerivation.d
        (X := op (q ⁻¹ᵁ A)) (q.app A s)

/-- The canonical source comparison for a refinement, using the normalized tensor
adjunctions and the equality of the two maps into the ambient scheme.
Source: Stacks, Tags 0097, 01R4 (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentationRefinement.sourceComparison
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C D : FlatLCIPresentation p d U} (r : FlatLCIPresentationRefinement C D) :
    Scheme.Modules.tensorPullback C.i ≅
      Scheme.Modules.tensorPullback r.q ⋙ Scheme.Modules.tensorPullback D.i :=
  (eqToIso (congrArg Scheme.Modules.tensorPullback r.source_eq.symm)) ≪≫
    Scheme.Modules.tensorPullbackSectionComp D.i r.q

/-- The induced conormal map of a normalized polynomial refinement.
Source: Stacks, Tag 01R4 (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentationRefinement.conormalMap
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C D : FlatLCIPresentation p d U} (r : FlatLCIPresentationRefinement C D) :
    C.conormal ⟶ D.conormal :=
  r.sourceComparison.hom.app C.i.ker.toModules ≫
    (Scheme.Modules.tensorPullback D.i).map r.idealMap

/-- The induced differential map of a normalized polynomial refinement.
Source: Stacks, Tag 01UV (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentationRefinement.differentialsMap
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C D : FlatLCIPresentation p d U} (r : FlatLCIPresentationRefinement C D) :
    C.differentials ⟶ D.differentials :=
  r.sourceComparison.hom.app (C.ambient ≫ pullback.fst _ _).relativeDifferentials ≫
    (Scheme.Modules.tensorPullback D.i).map r.differentialMap

/-- Normalization of a determinant map under pullback: normalized dual wedges and
wedges of pulled-back bases give precisely the pulled-back orientation. Equalities of
ranks are transported explicitly, so the definition does not assume definitional
identification of different presentations.
Source: Stacks, Tag 0FJY (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def IsFlatLCIPullbackDeterminantComparison {Y Z : Scheme.{u}} (h : Z ⟶ Y)
    (A V : Y.Modules) (B W : Z.Modules) (a b n m : ℕ) (ha : a = b) (hn : n = m)
    (f : (Scheme.Modules.tensorPullback h).obj A ⟶ B)
    (g : (Scheme.Modules.tensorPullback h).obj V ⟶ W)
    (e : (Scheme.Modules.tensorPullback h).obj (flatLCITwoTermLine Y A V a n) ≅
      flatLCITwoTermLine Z B W b m) : Prop :=
  IsIso f ∧ IsIso g ∧ ∀ (O : Y.Opens)
    (ba : Module.Basis (Fin a) Γ(Y, O) Γ(A, O))
    (bv : Module.Basis (Fin n) Γ(Y, O) Γ(V, O))
    (bb : Module.Basis (Fin b) Γ(Z, h ⁻¹ᵁ O) Γ(B, h ⁻¹ᵁ O))
    (bw : Module.Basis (Fin m) Γ(Z, h ⁻¹ᵁ O) Γ(W, h ⁻¹ᵁ O))
    (α : Γ(SheafOfModules.homObj (R := Y.sheaf) (Scheme.Modules.exteriorSheaf A a)
      (SheafOfModules.unit Y.ringCatSheaf), O))
    (β : Γ(SheafOfModules.homObj (R := Z.sheaf) (Scheme.Modules.exteriorSheaf B b)
      (SheafOfModules.unit Z.ringCatSheaf), h ⁻¹ᵁ O)),
    α.app (op (Over.mk (𝟙 O))) (Scheme.Modules.exteriorSheafSection A a O ba) =
      (1 : Γ(Y, O)) →
    β.app (op (Over.mk (𝟙 (h ⁻¹ᵁ O))))
      (Scheme.Modules.exteriorSheafSection B b (h ⁻¹ᵁ O) bb) = (1 : Γ(Z, h ⁻¹ᵁ O)) →
    (∀ j, f.app (h ⁻¹ᵁ O) (Scheme.Modules.tensorPullbackSection h A O (ba j)) =
      bb (Fin.cast ha j)) →
    (∀ j, g.app (h ⁻¹ᵁ O) (Scheme.Modules.tensorPullbackSection h V O (bv j)) =
      bw (Fin.cast hn j)) →
    e.hom.app (h ⁻¹ᵁ O)
      (Scheme.Modules.tensorPullbackSection h (flatLCITwoTermLine Y A V a n) O
        (Scheme.Modules.tmulSection (X := Y) α
          (Scheme.Modules.exteriorSheafSection V n O bv))) =
      Scheme.Modules.tmulSection (X := Z)
        (M := SheafOfModules.homObj (R := Z.sheaf) (Scheme.Modules.exteriorSheaf B b)
          (SheafOfModules.unit Z.ringCatSheaf))
        (N := Scheme.Modules.exteriorSheaf W m) β
        (Scheme.Modules.exteriorSheafSection W m (h ⁻¹ᵁ O) bw)

/-- A base change or open restriction of polynomial presentations, with the canonical
maps fixed on ideal sections and universal differentials. Its closed-source square is
cartesian. The ambient square is either a base change or an open restriction.
Source: Stacks, Tags 01R4, 01UV, 0E2Y
(blueprint: lem-trf-flat-lci-canonical-adjunction). -/
structure FlatLCIPresentationPullback {X S Y T : Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ T}
    {d : ℕ} {U : X.Opens} {V : Y.Opens}
    (C : FlatLCIPresentation p d U) (D : FlatLCIPresentation p' d V) where
  h : V.toScheme ⟶ U.toScheme
  q : D.P ⟶ C.P
  k : T ⟶ S
  source_eq : D.i ≫ q = h ≫ C.i
  source_cartesian : IsPullback h D.i C.i q
  base_eq : q ≫ (C.ambient ≫ pullback.fst _ _) =
    (D.ambient ≫ pullback.fst _ _) ≫ k
  ambient_cartesian : (IsOpenImmersion q ∧ Etale k) ∨
    IsPullback q (D.ambient ≫ pullback.fst _ _) (C.ambient ≫ pullback.fst _ _) k
  idealMap : (Scheme.Modules.tensorPullback q).obj C.i.ker.toModules ⟶ D.i.ker.toModules
  ideal_normal : ∀ (O : C.P.Opens) (s : Γ(C.i.ker.toModules, O)),
    D.i.ker.toModulesι.app (q ⁻¹ᵁ O)
      (idealMap.app (q ⁻¹ᵁ O)
        (Scheme.Modules.tensorPullbackSection q C.i.ker.toModules O s)) =
      q.app O (C.i.ker.toModulesι.app O s)
  differentialMap : (Scheme.Modules.tensorPullback q).obj
      (C.ambient ≫ pullback.fst _ _).relativeDifferentials ⟶
    (D.ambient ≫ pullback.fst _ _).relativeDifferentials
  differential_normal : ∀ (O : C.P.Opens) (s : Γ(C.P, O)),
    differentialMap.app (q ⁻¹ᵁ O)
      (Scheme.Modules.tensorPullbackSection q
        (C.ambient ≫ pullback.fst _ _).relativeDifferentials O
          ((C.ambient ≫ pullback.fst _ _).relativeDifferentialsDerivation.d (X := op O) s)) =
      (D.ambient ≫ pullback.fst _ _).relativeDifferentialsDerivation.d
        (X := op (q ⁻¹ᵁ O)) (q.app O s)

/-- The canonical comparison between the two paths of tensor pullback in a presentation
square. Source: Stacks, Tag 0097 (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentationPullback.sourceComparison
    {X S Y T : Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ T} {d : ℕ}
    {U : X.Opens} {V : Y.Opens} {C : FlatLCIPresentation p d U}
    {D : FlatLCIPresentation p' d V} (r : FlatLCIPresentationPullback C D) :
    Scheme.Modules.tensorPullback C.i ⋙ Scheme.Modules.tensorPullback r.h ≅
      Scheme.Modules.tensorPullback r.q ⋙ Scheme.Modules.tensorPullback D.i :=
  (Scheme.Modules.tensorPullbackSectionComp r.h C.i).symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback r.source_eq.symm) ≪≫
      Scheme.Modules.tensorPullbackSectionComp D.i r.q

/-- Canonical conormal base-change map, retaining its tensor normalization.
Source: Stacks, Tag 01R4 (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentationPullback.conormalMap
    {X S Y T : Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ T} {d : ℕ}
    {U : X.Opens} {V : Y.Opens} {C : FlatLCIPresentation p d U}
    {D : FlatLCIPresentation p' d V} (r : FlatLCIPresentationPullback C D) :
    (Scheme.Modules.tensorPullback r.h).obj C.conormal ⟶ D.conormal :=
  r.sourceComparison.hom.app C.i.ker.toModules ≫
    (Scheme.Modules.tensorPullback D.i).map r.idealMap

/-- Canonical differential base-change map, retaining its derivation normalization.
Source: Stacks, Tag 01UV (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIPresentationPullback.differentialsMap
    {X S Y T : Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ T} {d : ℕ}
    {U : X.Opens} {V : Y.Opens} {C : FlatLCIPresentation p d U}
    {D : FlatLCIPresentation p' d V} (r : FlatLCIPresentationPullback C D) :
    (Scheme.Modules.tensorPullback r.h).obj C.differentials ⟶ D.differentials :=
  r.sourceComparison.hom.app (C.ambient ≫ pullback.fst _ _).relativeDifferentials ≫
    (Scheme.Modules.tensorPullback D.i).map r.differentialMap

/-- The line bundles, their local adjunction identifications, and the coherent base-change
isomorphisms. Their canonical determinant normalization is stated separately below.
Source: Stacks, Tags 0B6V, 0E2Y (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
structure FlatLCIAdjunctionSystem {X S : Scheme.{u}} (p : X ⟶ S) (d : ℕ) where
  line : ∀ B : FlatLCIBaseChange p, B.X'.Modules
  invertible : ∀ B, (line B).IsInvertible
  localIso : ∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' d U),
    C.line ≅ (Scheme.Modules.tensorPullback U.ι).obj (line B)
  baseChange : ∀ (B D : FlatLCIBaseChange p) (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S'),
    IsPullback g D.p' B.p' b → g ≫ B.g = D.g → b ≫ B.b = D.b →
      ((Scheme.Modules.tensorPullback g).obj (line B) ≅ line D)
  identity : ∀ (B : FlatLCIBaseChange p) (hc : IsPullback (𝟙 B.X') B.p' B.p' (𝟙 B.S'))
    (hg : 𝟙 B.X' ≫ B.g = B.g) (hb : 𝟙 B.S' ≫ B.b = B.b),
    baseChange B B (𝟙 B.X') (𝟙 B.S') hc hg hb =
      (Scheme.Modules.tensorPullbackSectionId B.X').app (line B)
  composition : ∀ (B D E : FlatLCIBaseChange p)
    (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
    (h : E.X' ⟶ D.X') (c : E.S' ⟶ D.S')
    (hc₁ : IsPullback g D.p' B.p' b) (hg₁ : g ≫ B.g = D.g) (hb₁ : b ≫ B.b = D.b)
    (hc₂ : IsPullback h E.p' D.p' c) (hg₂ : h ≫ D.g = E.g) (hb₂ : c ≫ D.b = E.b)
    (hc₃ : IsPullback (h ≫ g) E.p' B.p' (c ≫ b))
    (hg₃ : (h ≫ g) ≫ B.g = E.g) (hb₃ : (c ≫ b) ≫ B.b = E.b),
    baseChange B E (h ≫ g) (c ≫ b) hc₃ hg₃ hb₃ =
      (Scheme.Modules.tensorPullbackSectionComp h g).app (line B) ≪≫
        (Scheme.Modules.tensorPullback h).mapIso (baseChange B D g b hc₁ hg₁ hb₁) ≪≫
          baseChange D E h c hc₂ hg₂ hb₂

/-- The local comparison induced by the base-change system, with every pullback
composition and equality transport displayed.
Source: Stacks, Tags 0097, 0E2Y (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def FlatLCIAdjunctionSystem.localBaseChange
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} (F : FlatLCIAdjunctionSystem p d)
    (B D : FlatLCIBaseChange p) (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
    (hc : IsPullback g D.p' B.p' b) (hg : g ≫ B.g = D.g) (hb : b ≫ B.b = D.b)
    (U : B.X'.Opens) (V : D.X'.Opens) (C : FlatLCIPresentation B.p' d U)
    (E : FlatLCIPresentation D.p' d V) (r : FlatLCIPresentationPullback C E)
    (hw : r.h ≫ U.ι = V.ι ≫ g) :
    (Scheme.Modules.tensorPullback r.h).obj C.line ≅ E.line :=
  (Scheme.Modules.tensorPullback r.h).mapIso (F.localIso B U C) ≪≫
    (Scheme.Modules.tensorPullbackSectionComp r.h U.ι).symm.app (F.line B) ≪≫
      (eqToIso (congrArg Scheme.Modules.tensorPullback hw)).app (F.line B) ≪≫
        (Scheme.Modules.tensorPullbackSectionComp V.ι g).app (F.line B) ≪≫
          (Scheme.Modules.tensorPullback V.ι).mapIso (F.baseChange B D g b hc hg hb) ≪≫
            (F.localIso D V E).symm

/-- The differential map from the ambient presentation to the source, normalized on
universal derivations. Source: Stacks, Tags 01UV, 08R5
(blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIPresentation.IsSourceDifferentialMap {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C : FlatLCIPresentation p d U)
    (β : C.differentials ⟶ (U.ι ≫ p).relativeDifferentials) : Prop :=
  ∀ (O : C.P.Opens) (a : Γ(C.P, O)),
    β.app (C.i ⁻¹ᵁ O)
      (Scheme.Modules.tensorPullbackSection C.i
        (C.ambient ≫ pullback.fst _ _).relativeDifferentials O
          ((C.ambient ≫ pullback.fst _ _).relativeDifferentialsDerivation.d (X := op O) a)) =
      (U.ι ≫ p).relativeDifferentialsDerivation.d (X := op (C.i ⁻¹ᵁ O)) (C.i.app O a)

/-- Normalized transitions are those induced by the exact cone determinant, and open
restrictions and arbitrary base changes carry normalized local orientations to their
pullbacks. Thus comparisons are constrained by algebraic formulas, including the acyclic
normalization, rather than by existence of an unspecified natural isomorphism.
Source: Stacks, Tags 0FJX, 0FJY, 0BZJ
(blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIAdjunctionSystem.IsNormalized {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    (F : FlatLCIAdjunctionSystem p d) : Prop :=
  (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens) (C : FlatLCIPresentation B.p' d U),
    (∃! δ : C.conormal ⟶ C.differentials, C.IsConormalDifferential δ) ∧
      (∃! β : C.differentials ⟶ (U.ι ≫ B.p').relativeDifferentials,
        C.IsSourceDifferentialMap β)) ∧
  (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C D : FlatLCIPresentation B.p' d U) (q : D.P ⟶ C.P),
    D.i ≫ q = C.i →
    q ≫ (C.ambient ≫ pullback.fst _ _) = D.ambient ≫ pullback.fst _ _ →
      ∃ r : FlatLCIPresentationRefinement C D, r.q = q) ∧
  (∀ (B D : FlatLCIBaseChange p) (U : B.X'.Opens) (V : D.X'.Opens)
    (C : FlatLCIPresentation B.p' d U) (E : FlatLCIPresentation D.p' d V)
    (h : V.toScheme ⟶ U.toScheme) (q : E.P ⟶ C.P) (k : D.S' ⟶ B.S'),
    IsPullback h E.i C.i q →
    q ≫ (C.ambient ≫ pullback.fst _ _) = (E.ambient ≫ pullback.fst _ _) ≫ k →
    ((IsOpenImmersion q ∧ Etale k) ∨
      IsPullback q (E.ambient ≫ pullback.fst _ _) (C.ambient ≫ pullback.fst _ _) k) →
      ∃ r : FlatLCIPresentationPullback C E, r.h = h ∧ r.q = q ∧ r.k = k) ∧
  (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C D : FlatLCIPresentation B.p' d U) (r : FlatLCIPresentationRefinement C D)
    (δC : C.conormal ⟶ C.differentials) (δD : D.conormal ⟶ D.differentials),
    C.IsConormalDifferential δC → D.IsConormalDifferential δD →
    ∀ hr : C.c + D.n = D.c + C.n,
      IsFlatLCIDeterminantComparison C.conormal D.conormal C.differentials D.differentials
        C.c D.c C.n D.n hr δC δD r.conormalMap r.differentialsMap
        (F.localIso B U C ≪≫ (F.localIso B U D).symm)) ∧
  (∀ (B D : FlatLCIBaseChange p) (g : D.X' ⟶ B.X') (b : D.S' ⟶ B.S')
    (hc : IsPullback g D.p' B.p' b) (hg : g ≫ B.g = D.g) (hb : b ≫ B.b = D.b)
    (U : B.X'.Opens) (V : D.X'.Opens) (C : FlatLCIPresentation B.p' d U)
    (E : FlatLCIPresentation D.p' d V) (r : FlatLCIPresentationPullback C E)
    (hw : r.h ≫ U.ι = V.ι ≫ g) (ha : C.c = E.c) (hn : C.n = E.n),
    r.k = b →
      IsFlatLCIPullbackDeterminantComparison r.h C.conormal C.differentials
        E.conormal E.differentials C.c E.c C.n E.n ha hn r.conormalMap r.differentialsMap
          (F.localBaseChange B D g b hc hg hb U V C E r hw))

/-- Multiplication on a module by an endomorphism of its structure module. This writes
out the induced closed-source action without replacing it by an arbitrary action.
Source: Stacks, Tag 0BQZ (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def flatLCIScalarAction (Y : Scheme.{u}) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    M ⟶ M :=
  (MonoidalCategory.leftUnitor (C := Y.Modules) M).inv ≫
    MonoidalCategory.whiskerRight (C := Y.Modules) s M ≫
      (MonoidalCategory.leftUnitor (C := Y.Modules) M).hom

/-- The local shifted-duality model, exactly in the ambient derived category where the
closed-immersion computation takes place. The identification on the closed source is
expressed using the single complex of its direct image; closed-immersion direct image is
exact. All derived-category universes are explicitly quantified by the caller.
Source: Stacks, Tags 0B6V, 0BQZ (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIPresentation.HasDualityModel {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C : FlatLCIPresentation p d U) : Prop :=
  ∀ [_h : HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (moduleRings C.P.toRingedSpace))],
    ∃ e : ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward C.i).obj C.line))⟦(d : ℤ)⟧ ≅
      (derivedInternalHom (Opens.grothendieckTopology C.P) C.P.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)) 0).obj
            ((Scheme.Modules.pushforward C.i).obj
              (SheafOfModules.unit U.toScheme.ringCatSheaf))),
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)) 0).obj
              (Scheme.Modules.exteriorSheaf
                (C.ambient ≫ pullback.fst _ _).relativeDifferentials C.n))⟦(C.n : ℤ)⟧),
      ∀ s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf,
        (shiftFunctor _ (d : ℤ)).map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)) 0).map
            ((Scheme.Modules.pushforward C.i).map
              (flatLCIScalarAction U.toScheme C.line s))) ≫ e.hom =
          e.hom ≫
            (derivedInternalHom (Opens.grothendieckTopology C.P) C.P.sheaf).map
              (((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings C.P.toRingedSpace)) 0).map
                  ((Scheme.Modules.pushforward C.i).map s)).op, 𝟙 _)

/-- The sheaf Ext identification of the adjunction line. Both arguments are ordinary
modules, and the Ext sheaf uses the recorded derived-internal-Hom definition.
Source: Stacks, Tag 0BQZ (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIPresentation.HasExtIdentification {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    {U : X.Opens} (C : FlatLCIPresentation p d U) : Prop :=
  ∀ [_h : HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (moduleRings C.P.toRingedSpace))],
    ∃ e : (Scheme.Modules.pushforward C.i).obj C.line ≅
      moduleSheafExt C.P (C.c : ℤ)
        ((Scheme.Modules.pushforward C.i).obj (SheafOfModules.unit U.toScheme.ringCatSheaf))
        (Scheme.Modules.exteriorSheaf
          (C.ambient ≫ pullback.fst _ _).relativeDifferentials C.n),
      ∀ s : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
        SheafOfModules.unit U.toScheme.ringCatSheaf,
        (Scheme.Modules.pushforward C.i).map (flatLCIScalarAction U.toScheme C.line s) ≫
            e.hom = e.hom ≫
          (moduleSheafExtFunctor C.P (C.c : ℤ)).map
            (((Scheme.Modules.pushforward C.i).map s).op, 𝟙 _)

/-- The geometric fibre over the specified algebraic closure of the residue field.
Source: Stacks, Tag 01JO (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
noncomputable def flatLCIGeometricFibre {X S : Scheme.{u}} (p : X ⟶ S) (s : S) :
    Scheme.{u} :=
  pullback p (Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
      S.fromSpecResidueField s)

/-- Nonempty geometric fibres have pure dimension d: every irreducible component has
that dimension. Quantification over components automatically makes an empty fibre
vacuous and does not impose surjectivity on the original family.
Source: Stacks, Tags 0055, 02G1 (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def HasPureFlatLCIGeometricFibres {X S : Scheme.{u}} (p : X ⟶ S) (d : ℕ) : Prop :=
  ∀ (s : S) (Z : Set (flatLCIGeometricFibre p s)),
    Z ∈ irreducibleComponents (flatLCIGeometricFibre p s) →
      topologicalKrullDim Z = (d : WithBot ℕ∞)

/-- On a smooth open the determinant identification is normalized by the conormal
sequence: the included conormal factors precede any lifts of the differential factors.
The formula includes rank zero by the empty wedge, and fixes the smooth-locus comparison
rather than merely asserting an isomorphism between two invertible modules.
Source: Stacks, Tags 08R5, 0FJX (blueprint: lem-trf-flat-lci-canonical-adjunction). -/
def FlatLCIAdjunctionSystem.IsSmoothComparison {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ}
    (F : FlatLCIAdjunctionSystem p d) (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (e : (Scheme.Modules.tensorPullback U.ι).obj (F.line B) ≅
      Scheme.Modules.exteriorSheaf (U.ι ≫ B.p').relativeDifferentials d) : Prop :=
  ∀ (C : FlatLCIPresentation B.p' d U)
    (δ : C.conormal ⟶ C.differentials)
    (β : C.differentials ⟶ (U.ι ≫ B.p').relativeDifferentials),
    C.IsConormalDifferential δ → C.IsSourceDifferentialMap β →
    ∀ (O : U.toScheme.Opens) (a : Fin C.c → Γ(C.conormal, O))
      (b : Fin d → Γ((U.ι ≫ B.p').relativeDifferentials, O))
      (l : Fin d → Γ(C.differentials, O))
      (α : Γ(SheafOfModules.homObj (R := U.toScheme.sheaf)
        (Scheme.Modules.exteriorSheaf C.conormal C.c)
          (SheafOfModules.unit U.toScheme.ringCatSheaf), O)),
      α.app (op (Over.mk (𝟙 O)))
        (Scheme.Modules.exteriorSheafSection C.conormal C.c O a) =
          (1 : Γ(U.toScheme, O)) →
      (∀ j, β.app O (l j) = b j) →
      e.hom.app O ((F.localIso B U C).hom.app O
        (Scheme.Modules.tmulSection (X := U.toScheme)
          (M := SheafOfModules.homObj (R := U.toScheme.sheaf)
            (Scheme.Modules.exteriorSheaf C.conormal C.c)
              (SheafOfModules.unit U.toScheme.ringCatSheaf))
          (N := Scheme.Modules.exteriorSheaf C.differentials C.n) α
          (Scheme.Modules.exteriorSheafSection C.differentials C.n O
            (fun j ↦ Fin.append (fun k ↦ δ.app O (a k)) l (Fin.cast C.rank_eq j))))) =
        Scheme.Modules.exteriorSheafSection (U.ι ≫ B.p').relativeDifferentials d O b

/-- Canonical adjunction for a flat, finitely presented, pure-dimensional local complete
intersection over a Noetherian scheme. The construction is made simultaneously on every
cartesian change of base, with no Noetherian hypothesis on the changed base. The original
line is `F.line (FlatLCIBaseChange.identity p)`. Local identifications with this single
line give the transition isomorphisms on overlaps; their cocycle condition follows by
cancellation. The determinant formulas in `IsNormalized` specify those comparisons
independently of presentation, including the evaluation normalization on acyclic terms.

Source: Stacks, Tags 0B6V, 0BQZ, 0E2Y, 08SL, 08QQ, 08R5, 0FJX and 0FJY
(blueprint: lem-trf-flat-lci-canonical-adjunction).

Proof, following the nine steps of the DAG:
1. A local regular sequence is Koszul-regular and its conormal classes are a basis
   (lem-weil-pbc-regular-sequence-koszul-regular and
   lem-weil-pbc-regular-sequence-conormal-free). Coordinate differentials form the
   ambient basis, so the displayed dual exterior tensor is an invertible module.
2. The canonical two-term conormal presentation represents the intrinsic cotangent
   complex (lem-trf-lci-cotangent-presentation). Apply the determinant functor of
   lem-trf-two-term-perfect-determinant to obtain the global line, also nonseparated.
3. The chart identifications with that line define transitions by cancellation. The
   cone determinant formula is its normalization on quasi-isomorphisms; composition
   and identity give the overlap cocycle and independence of all refinements.
4. The finite free Koszul resolution computes derived internal Hom
   (lem-sc-derived-hom-finite-free-model); its normalized dual has only the top
   cohomology, the dual conormal determinant
   (lem-sc-koszul-regular-sequence-dual-complex). Tensor by the ambient differential
   line and restrict by lem-sc-derived-internal-hom-restrict-open. This gives sheaf
   Ext in degree c and the shifted derived model with n-c=d.
5. On every separated open, lem-trf-relative-duality-polynomial-chart identifies
   that local model with the relative dualizing object.
6. On adjoining a coordinate mapping to a lift a, the extra complex is
   [O --1--> O], using d(t-a)=dt-da. Its determinant and the polynomial-duality
   comparison both contract the dual equation with its differential to 1. Changes
   of generators and common polynomial refinements therefore give precisely the
   same transitions, including their ordered wedge and cohomological signs.
7. On arbitrary base change the polynomial localization is flat over the base
   (lem-pc-affine-flat-module-localization-preserves-flatness), is finitely presented
   (lem-weil-pbc-localization-away-polynomial-quotient), and the quotient is flat
   (lem-weil-pbc-flat-morphism-affine-criterion). Apply
   lem-pur-relative-regular-equations-base-change at primes of the closed source.
   The resulting Koszul-regular equations have the same conormal bases and ambient
   coordinate differential bases. They supply the base-changed presentations.
8. Flatness makes the square Tor-independent. Cotangent base change
   (lem-trf-lci-cotangent-presentation) and coherent determinant pullback
   (lem-trf-two-term-perfect-determinant) give the base-change isomorphisms, with
   exactly the pure-tensor normalization above. Their identity and composition
   laws are those of these canonical maps and the normalized tensor adjunctions.
9. On a smooth open, the cotangent complex is the differential module in degree
   zero; lem-sc-smooth-omega-finite-locally-free gives its rank d. The determinant
   of its conormal exact sequence is the specified smooth comparison. -/
theorem exists_flatLCICanonicalAdjunction {X S : Scheme.{u}} (p : X ⟶ S)
    [IsNoetherian S] [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p] (d : ℕ) (hpure : HasPureFlatLCIGeometricFibres p d)
    (hlci : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ Nonempty (FlatLCIPresentation p d U)) :
    ∃ F : FlatLCIAdjunctionSystem p d,
      F.IsNormalized ∧
      (∀ (B : FlatLCIBaseChange p) (x : B.X'),
        ∃ (U : B.X'.Opens), x ∈ U ∧ Nonempty (FlatLCIPresentation B.p' d U)) ∧
      (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens) (C : FlatLCIPresentation B.p' d U),
        C.HasExtIdentification ∧ C.HasDualityModel) ∧
      (∀ (B : FlatLCIBaseChange p) (U : B.X'.Opens), Smooth (U.ι ≫ B.p') →
        ∃ e : (Scheme.Modules.tensorPullback U.ι).obj (F.line B) ≅
          Scheme.Modules.exteriorSheaf (U.ι ≫ B.p').relativeDifferentials d,
          F.IsSmoothComparison B U e) := by
  sorry

end AlgebraicGeometry
