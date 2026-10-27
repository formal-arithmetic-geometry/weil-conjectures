/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.TraceFormula.TwoTermPerfectDeterminant
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import Sheaf.AlgebraicGeometry.SmoothLocalDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.RingTheory.EtaleCotangentVanishing
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale

/-!
# Étale source locality of the adjunction line

Source: Stacks Project, Duality, Tags 0B6V, 0FWI, 0E9Z; Cotangent, Tags 08T4, 08R2;
Perfect, Tags 0FJX, 0FJY (blueprint: lem-sfb-etale-source-adjunction-line).

The comparison is a coherent system over the finitely presented étale sources of the
original family. Its normalization is tested on conormal complexes of polynomial
presentations, including nonsmooth charts. On smooth opens it is specified on `da`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- An index for the finitely presented étale sources of a scheme. Finite presentation
means local finite presentation (included in étaleness), quasi-compactness and
quasi-separatedness, with no separatedness or surjectivity condition.
Source: Stacks, Tags 02GI, 01TO (blueprint: lem-sfb-etale-source-adjunction-line). -/
structure FlatLCIEtaleSource (X : Scheme.{u}) where
  scheme : Scheme.{u}
  map : scheme ⟶ X
  etale : Etale map
  quasiCompact : QuasiCompact map
  quasiSeparated : QuasiSeparated map

/-- A map of polynomial presentations over the same base, lying over the source map
`h`. The ideal map is fixed on actual ideal sections. Ambient dimensions can differ:
this includes the extra variable and monic equation in a standard-étale presentation.
Source: Stacks, Tags 00UE, 08SL, 08QL
(blueprint: lem-sfb-etale-source-adjunction-line). -/
structure FlatLCIEtalePresentationMap {Y Z S : Scheme.{u}}
    {p : Y ⟶ S} {q : Z ⟶ S} {U : Y.Opens} {V : Z.Opens}
    (C : FlatLCIPresentation p 1 U) (D : FlatLCIPresentation q 1 V)
    (h : V.toScheme ⟶ U.toScheme) where
  ambient : D.P ⟶ C.P
  source_eq : D.i ≫ ambient = h ≫ C.i
  base_eq : ambient ≫ (C.ambient ≫ pullback.fst _ _) =
    D.ambient ≫ pullback.fst _ _
  idealMap : (Scheme.Modules.tensorPullback ambient).obj C.i.ker.toModules ⟶
    D.i.ker.toModules
  ideal_normal : ∀ (O : C.P.Opens) (s : Γ(C.i.ker.toModules, O)),
    D.i.ker.toModulesι.app (ambient ⁻¹ᵁ O)
      (idealMap.app (ambient ⁻¹ᵁ O)
        (Scheme.Modules.tensorPullbackSection ambient C.i.ker.toModules O s)) =
      ambient.app O (C.i.ker.toModulesι.app O s)

/-- The comparison between the two paths of tensor pullback in a presentation map.
Source: Stacks, Tag 0097 (blueprint: lem-sfb-etale-source-adjunction-line). -/
noncomputable def FlatLCIEtalePresentationMap.sourceComparison
    {Y Z S : Scheme.{u}} {p : Y ⟶ S} {q : Z ⟶ S} {U : Y.Opens} {V : Z.Opens}
    {C : FlatLCIPresentation p 1 U} {D : FlatLCIPresentation q 1 V}
    {h : V.toScheme ⟶ U.toScheme} (r : FlatLCIEtalePresentationMap C D h) :
    Scheme.Modules.tensorPullback C.i ⋙ Scheme.Modules.tensorPullback h ≅
      Scheme.Modules.tensorPullback r.ambient ⋙ Scheme.Modules.tensorPullback D.i :=
  (Scheme.Modules.tensorPullbackSectionComp h C.i).symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback r.source_eq.symm) ≪≫
      Scheme.Modules.tensorPullbackSectionComp D.i r.ambient

/-- The induced conormal map, with its actual ideal-section normalization.
Source: Stacks, Tag 01R4 (blueprint: lem-sfb-etale-source-adjunction-line). -/
noncomputable def FlatLCIEtalePresentationMap.conormalMap
    {Y Z S : Scheme.{u}} {p : Y ⟶ S} {q : Z ⟶ S} {U : Y.Opens} {V : Z.Opens}
    {C : FlatLCIPresentation p 1 U} {D : FlatLCIPresentation q 1 V}
    {h : V.toScheme ⟶ U.toScheme} (r : FlatLCIEtalePresentationMap C D h) :
    (Scheme.Modules.tensorPullback h).obj C.conormal ⟶ D.conormal :=
  r.sourceComparison.hom.app C.i.ker.toModules ≫
    (Scheme.Modules.tensorPullback D.i).map r.idealMap

/-- The induced ambient-differential map is the universal differential pullback.
Source: Stacks, Tag 01UV (blueprint: lem-sfb-etale-source-adjunction-line). -/
noncomputable def FlatLCIEtalePresentationMap.differentialsMap
    {Y Z S : Scheme.{u}} {p : Y ⟶ S} {q : Z ⟶ S} {U : Y.Opens} {V : Z.Opens}
    {C : FlatLCIPresentation p 1 U} {D : FlatLCIPresentation q 1 V}
    {h : V.toScheme ⟶ U.toScheme} (r : FlatLCIEtalePresentationMap C D h) :
    (Scheme.Modules.tensorPullback h).obj C.differentials ⟶ D.differentials :=
  r.sourceComparison.hom.app (C.ambient ≫ pullback.fst _ _).relativeDifferentials ≫
    (Scheme.Modules.tensorPullback D.i).map
      (Scheme.Hom.relativeDifferentialsPullbackMap
          (C.ambient ≫ pullback.fst _ _) r.ambient ≫
        (Scheme.Hom.relativeDifferentialsCongr
          (r.ambient ≫ (C.ambient ≫ pullback.fst _ _)) r.base_eq).hom)

/-- Restriction of a line comparison to a pair of opens in a commutative source
square. Every associativity and equality transport uses the normalized tensor pullback.
Source: Stacks, Tags 0097, 08QL (blueprint: lem-sfb-etale-source-adjunction-line). -/
noncomputable def flatLCIEtaleLocalComparison {Y Z : Scheme.{u}}
    (a : Z ⟶ Y) (K : Y.Modules) (L : Z.Modules)
    (φ : (Scheme.Modules.tensorPullback a).obj K ≅ L)
    (U : Y.Opens) (V : Z.Opens) (h : V.toScheme ⟶ U.toScheme)
    (w : h ≫ U.ι = V.ι ≫ a) :
    (Scheme.Modules.tensorPullback h).obj ((Scheme.Modules.tensorPullback U.ι).obj K) ≅
      (Scheme.Modules.tensorPullback V.ι).obj L :=
  (Scheme.Modules.tensorPullbackSectionComp h U.ι).symm.app K ≪≫
    (eqToIso (congrArg Scheme.Modules.tensorPullback w)).app K ≪≫
      (Scheme.Modules.tensorPullbackSectionComp V.ι a).app K ≪≫
        (Scheme.Modules.tensorPullback V.ι).mapIso φ

/-- Canonical determinant normalization on all polynomial presentation charts. First
pull the determinant formula back by the normalized pure-tensor comparison `ρ`, then
apply the exact-cone determinant of the canonical map of conormal complexes. Thus the
condition fixes the comparison even when the smooth locus is empty.
Source: Stacks, Tags 08SL, 0FJX, 0FJY
(blueprint: lem-sfb-etale-source-adjunction-line). -/
def IsFlatLCIEtaleLineComparison {Y Z S : Scheme.{u}}
    (p : Y ⟶ S) (q : Z ⟶ S) (a : Z ⟶ Y)
    (F : FlatLCIAdjunctionSystem p 1) (G : FlatLCIAdjunctionSystem q 1)
    (φ : (Scheme.Modules.tensorPullback a).obj (F.line (FlatLCIBaseChange.identity p)) ≅
      G.line (FlatLCIBaseChange.identity q)) : Prop :=
  ∀ (U : Y.Opens) (V : Z.Opens) (h : V.toScheme ⟶ U.toScheme),
    h ≫ U.ι = V.ι ≫ a → Etale h →
    ∀ (C : FlatLCIPresentation p 1 U) (D : FlatLCIPresentation q 1 V)
      (r : FlatLCIEtalePresentationMap C D h)
      (δC : C.conormal ⟶ C.differentials) (δD : D.conormal ⟶ D.differentials),
      C.IsConormalDifferential δC → D.IsConormalDifferential δD →
      ∀ (w : h ≫ U.ι = V.ι ≫ a) (hr : C.c + D.n = D.c + C.n)
        (ρ : (Scheme.Modules.tensorPullback h).obj C.line ≅
          flatLCITwoTermLine V.toScheme
            ((Scheme.Modules.tensorPullback h).obj C.conormal)
            ((Scheme.Modules.tensorPullback h).obj C.differentials) C.c C.n),
        IsFlatLCIPullbackDeterminantComparison h C.conormal C.differentials
          ((Scheme.Modules.tensorPullback h).obj C.conormal)
          ((Scheme.Modules.tensorPullback h).obj C.differentials)
          C.c C.c C.n C.n rfl rfl (𝟙 _) (𝟙 _) ρ →
        IsFlatLCIDeterminantComparison
          ((Scheme.Modules.tensorPullback h).obj C.conormal) D.conormal
          ((Scheme.Modules.tensorPullback h).obj C.differentials) D.differentials
          C.c D.c C.n D.n hr ((Scheme.Modules.tensorPullback h).map δC) δD
          r.conormalMap r.differentialsMap
          (ρ.symm ≪≫ (Scheme.Modules.tensorPullback h).mapIso
              (F.localIso (FlatLCIBaseChange.identity p) U C) ≪≫
            flatLCIEtaleLocalComparison a _ _ φ U V h w ≪≫
              (G.localIso (FlatLCIBaseChange.identity q) V D).symm)

/-- Adjunction lines and comparison data on all finitely presented étale sources of `X`.
The laws in `IsCoherent` include open restriction squares and identify the comparison
with differential pullback on arbitrary smooth opens. All this data is constructed
in the theorem's conclusion.
Source: Stacks, Tags 0B6V, 0FWI, 0E9Z, 08QL, 0FJY
(blueprint: lem-sfb-etale-source-adjunction-line). -/
structure FlatLCIEtaleAdjunctionData {X S : Scheme.{u}} (p : X ⟶ S) where
  adjunction : ∀ E : FlatLCIEtaleSource X, FlatLCIAdjunctionSystem (E.map ≫ p) 1
  smooth : ∀ (E : FlatLCIEtaleSource X) (U : E.scheme.Opens),
    Smooth (U.ι ≫ (E.map ≫ p)) →
      ((Scheme.Modules.tensorPullback U.ι).obj
          ((adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p))) ≅
            Scheme.Modules.exteriorSheaf (U.ι ≫ (E.map ≫ p)).relativeDifferentials 1)
  comparison : ∀ (E D : FlatLCIEtaleSource X) (a : D.scheme ⟶ E.scheme),
    Etale a → QuasiCompact a → QuasiSeparated a → a ≫ E.map = D.map →
      ((Scheme.Modules.tensorPullback a).obj
          ((adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p))) ≅
        (adjunction D).line (FlatLCIBaseChange.identity (D.map ≫ p)))

/-- All geometric preservation, determinant, composition, restriction and differential
laws of the comparison data. Keeping these laws in a proposition avoids generating
large dependent equality and size lemmas for the underlying data package.
Source: Stacks, Tags 0B6V, 0FWI, 0E9Z, 08QL, 0FJY
(blueprint: lem-sfb-etale-source-adjunction-line). -/
def FlatLCIEtaleAdjunctionData.IsCoherent {X S : Scheme.{u}} {p : X ⟶ S}
    (F : FlatLCIEtaleAdjunctionData p) : Prop :=
  -- Normalization of the adjunction systems.
  (∀ E : FlatLCIEtaleSource X, (F.adjunction E).IsNormalized) ∧
  -- Preserved flatness, finite presentation, pure fibres and regular presentations.
  (∀ E : FlatLCIEtaleSource X, Flat (E.map ≫ p)) ∧
  (∀ E : FlatLCIEtaleSource X, LocallyOfFinitePresentation (E.map ≫ p)) ∧
  (∀ E : FlatLCIEtaleSource X, QuasiCompact (E.map ≫ p)) ∧
  (∀ E : FlatLCIEtaleSource X, QuasiSeparated (E.map ≫ p)) ∧
  (∀ E : FlatLCIEtaleSource X, HasPureFlatLCIGeometricFibres (E.map ≫ p) 1) ∧
  (∀ (E : FlatLCIEtaleSource X) (x : E.scheme),
      ∃ U : E.scheme.Opens, x ∈ U ∧ Nonempty (FlatLCIPresentation (E.map ≫ p) 1 U)) ∧
  -- Normalization of the chosen smooth comparisons.
  (∀ (E : FlatLCIEtaleSource X) (U : E.scheme.Opens)
      (hU : Smooth (U.ι ≫ (E.map ≫ p))),
      (F.adjunction E).IsSmoothComparison (FlatLCIBaseChange.identity (E.map ≫ p)) U
        (F.smooth E U hU)) ∧
  -- Determinant normalization, including nonsmooth charts.
  (∀ (E D : FlatLCIEtaleSource X) (a : D.scheme ⟶ E.scheme)
      (ha : Etale a) (hq : QuasiCompact a) (hs : QuasiSeparated a) (w : a ≫ E.map = D.map),
      IsFlatLCIEtaleLineComparison (E.map ≫ p) (D.map ≫ p) a (F.adjunction E) (F.adjunction D)
        (F.comparison E D a ha hq hs w)) ∧
  -- Identity.
  (∀ (E : FlatLCIEtaleSource X) (ha : Etale (𝟙 E.scheme))
      (hq : QuasiCompact (𝟙 E.scheme)) (hs : QuasiSeparated (𝟙 E.scheme))
      (w : 𝟙 E.scheme ≫ E.map = E.map),
      F.comparison E E (𝟙 E.scheme) ha hq hs w =
        (Scheme.Modules.tensorPullbackSectionId E.scheme).app
          ((F.adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p)))) ∧
  -- Composition.
  (∀ (E D H : FlatLCIEtaleSource X)
      (a : D.scheme ⟶ E.scheme) (b : H.scheme ⟶ D.scheme)
      (ha : Etale a) (hqa : QuasiCompact a) (hsa : QuasiSeparated a)
      (hb : Etale b) (hqb : QuasiCompact b) (hsb : QuasiSeparated b)
      (hc : Etale (b ≫ a)) (hqc : QuasiCompact (b ≫ a)) (hsc : QuasiSeparated (b ≫ a))
      (wa : a ≫ E.map = D.map) (wb : b ≫ D.map = H.map)
      (wc : (b ≫ a) ≫ E.map = H.map),
      F.comparison E H (b ≫ a) hc hqc hsc wc =
        (Scheme.Modules.tensorPullbackSectionComp b a).app
            ((F.adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p))) ≪≫
          (Scheme.Modules.tensorPullback b).mapIso (F.comparison E D a ha hqa hsa wa) ≪≫
            F.comparison D H b hb hqb hsb wb) ∧
  -- Restriction to open subschemes.
  (∀ (E D E' D' : FlatLCIEtaleSource X)
      (a : D.scheme ⟶ E.scheme) (a' : D'.scheme ⟶ E'.scheme)
      (j : E'.scheme ⟶ E.scheme) (k : D'.scheme ⟶ D.scheme)
      (ha : Etale a) (hqa : QuasiCompact a) (hsa : QuasiSeparated a)
      (ha' : Etale a') (hqa' : QuasiCompact a') (hsa' : QuasiSeparated a')
      (hj : Etale j) (hqj : QuasiCompact j) (hsj : QuasiSeparated j)
      (hk : Etale k) (hqk : QuasiCompact k) (hsk : QuasiSeparated k)
      (wa : a ≫ E.map = D.map) (wa' : a' ≫ E'.map = D'.map)
      (wj : j ≫ E.map = E'.map) (wk : k ≫ D.map = D'.map)
      (w : a' ≫ j = k ≫ a),
      IsOpenImmersion j → IsOpenImmersion k →
        (Scheme.Modules.tensorPullbackSectionComp a' j).app
            ((F.adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p))) ≪≫
          (Scheme.Modules.tensorPullback a').mapIso (F.comparison E E' j hj hqj hsj wj) ≪≫
            F.comparison E' D' a' ha' hqa' hsa' wa' =
        (eqToIso (congrArg Scheme.Modules.tensorPullback w)).app
            ((F.adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p))) ≪≫
          (Scheme.Modules.tensorPullbackSectionComp k a).app
            ((F.adjunction E).line (FlatLCIBaseChange.identity (E.map ≫ p))) ≪≫
          (Scheme.Modules.tensorPullback k).mapIso (F.comparison E D a ha hqa hsa wa) ≪≫
            F.comparison D D' k hk hqk hsk wk) ∧
  -- Preservation of smoothness on corresponding opens.
  (∀ (E D : FlatLCIEtaleSource X) (a : D.scheme ⟶ E.scheme)
      (U : E.scheme.Opens) (V : D.scheme.Opens) (h : V.toScheme ⟶ U.toScheme),
      a ≫ E.map = D.map → h ≫ U.ι = V.ι ≫ a →
      Smooth (U.ι ≫ (E.map ≫ p)) → Etale h → Smooth (V.ι ≫ (D.map ≫ p))) ∧
  -- The usual differential pullback under the smooth identifications.
  (∀ (E D : FlatLCIEtaleSource X) (a : D.scheme ⟶ E.scheme)
      (ha : Etale a) (hq : QuasiCompact a) (hs : QuasiSeparated a)
      (wa : a ≫ E.map = D.map) (U : E.scheme.Opens) (V : D.scheme.Opens)
      (h : V.toScheme ⟶ U.toScheme) (w : h ≫ U.ι = V.ι ≫ a)
      (hU : Smooth (U.ι ≫ (E.map ≫ p))) (hV : Smooth (V.ι ≫ (D.map ≫ p))),
      Etale h → ∀ (O : U.toScheme.Opens) (s : Γ(U.toScheme, O)),
        ((Scheme.Modules.tensorPullback h).mapIso (F.smooth E U hU).symm ≪≫
          flatLCIEtaleLocalComparison a _ _ (F.comparison E D a ha hq hs wa) U V h w ≪≫
          F.smooth D V hV).hom.app (h ⁻¹ᵁ O)
          (Scheme.Modules.tensorPullbackSection h
            (Scheme.Modules.exteriorSheaf (U.ι ≫ (E.map ≫ p)).relativeDifferentials 1) O
            (Scheme.Modules.exteriorSheafSection
              (U.ι ≫ (E.map ≫ p)).relativeDifferentials 1 O
              (fun _ ↦ (U.ι ≫ (E.map ≫ p)).relativeDifferentialsDerivation.d
                (X := op O) s))) =
          Scheme.Modules.exteriorSheafSection
            (V.ι ≫ (D.map ≫ p)).relativeDifferentials 1 (h ⁻¹ᵁ O)
            (fun _ ↦ (V.ι ≫ (D.map ≫ p)).relativeDifferentialsDerivation.d
              (X := op (h ⁻¹ᵁ O)) (h.app O s)))

/-- The comparison data together with exactly the laws in `IsCoherent`.
Source: Stacks, Tags 0B6V, 0FWI, 0E9Z, 08QL, 0FJY
(blueprint: lem-sfb-etale-source-adjunction-line). -/
structure FlatLCIEtaleAdjunctionSystem {X S : Scheme.{u}} (p : X ⟶ S) where
  data : FlatLCIEtaleAdjunctionData p
  coherent : data.IsCoherent

/-- Étale source locality of the canonical relative adjunction line, including all
preserved geometric properties, coherent restriction and composition, and the smooth
normalization. The identity étale source supplies the original line `K_{X/S}`.
Source: Stacks, Tags 0B6V, 0FWI, 0E9Z, 08T4, 08R2, 0FJX, 0FJY
(blueprint: lem-sfb-etale-source-adjunction-line).

Proof (the nine DAG steps):
1. Étale maps are flat and locally finitely presented. Composition preserves both;
   preimages of quasi-compact opens show quasi-compactness. All source schemes are
   Noetherian, hence quasi-separated, giving finite presentation without separatedness.
2. On a standard-étale chart write B[t]_h/(g), with g monic. Lift g and h to the
   regular polynomial presentation A of B. The old equations followed by the monic
   lift remain regular (coefficientwise injectivity, then localization). There are
   n equations in n+1 variables, giving the dimension-one presentation.
3. Geometric base change is étale. Its local dimension is unchanged, because its
   smooth relative dimension is zero. Thus every nonempty fibre remains pure of
   dimension one (lem-per-smooth-local-dimension and the two local-dimension lemmas).
4. Normalize each adjunction line by the determinant of its conormal cotangent
   presentation, using lem-sfb-adjunction-cotangent-determinant-normalization and
   lem-trf-two-term-perfect-determinant. The same normalization gives the smooth
   comparison with the first exterior power of differentials.
5. Formal étaleness gives L_{V/T}=0 (lem-trf-etale-cotangent-vanishing). The scheme
   cotangent transitivity triangle makes the specified functoriality arrow
   Le* L_{T/S} → L_{V/S} an isomorphism (lem-sfb-scheme-cotangent-transitivity).
6. Take its determinant and conjugate by the normalized adjunction/determinant
   identifications. On presentation charts this is precisely the cone determinant
   comparison required in `IsCoherent`, independently of all presentations.
7. Cotangent functoriality, determinant naturality and determinant pullback
   composition give the identity and composition formulas; the middle adjunction
   identifications cancel.
8. Restrict the same intrinsic arrow and its determinant to arbitrary opens.
   This gives open compatibility without affine-intersection or separatedness assumptions.
9. On smooth opens the cotangent augmentations identify that arrow with
   1 ⊗ da ↦ d(e♯a). Rank-one degree-zero determinant gives the stated differential formula,
   with no density assumption on the smooth locus. -/
theorem exists_flatLCIEtaleAdjunctionSystem {X S : Scheme.{u}} (p : X ⟶ S)
    [IsNoetherian S] [Flat p] [LocallyOfFinitePresentation p] [QuasiCompact p]
    [QuasiSeparated p] (hpure : HasPureFlatLCIGeometricFibres p 1)
    (hlci : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (FlatLCIPresentation p 1 U)) :
    Nonempty (FlatLCIEtaleAdjunctionSystem p) := by
  sorry

end AlgebraicGeometry
