/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
public import Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
public import Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization
public import Sheaf.AlgebraicGeometry.LciDeterminantDescentSmooth
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence
import Sheaf.RingTheory.LineModuleDuality
import Sheaf.SecTraceFormula.TwoTermKernelNormalization
import Mathlib.Algebra.Exact.Basic
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.RingTheory.RegularSequenceConormal

/-! # Ordered-wedge normalization of two-term augmentation determinants

Source: Stacks Project, Duality, Tags 0E9Y and 0E9Z; More on Algebra, Tag 0FJI;
Perfect Complexes, Tags 0FJX and 0FJY.
(blueprint: lem-trf-two-term-augmentation-determinant-normalization).

The records below unpack the exact sequence, its augmentation and the normalization
of its determinant. The exterior powers and duals are the recorded sheaf constructions.
In particular the formulas are tested on every open, rather than on global bases.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped ZeroObject

namespace AlgebraicGeometry

/-- A short exact sequence in the assertion, packaged with its constant ranks.
On an affine spectrum these are precisely the sheaves of finite projective modules
of the displayed ranks. Source: Stacks, Tags 0FJB and 0E9Y
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
structure TwoTermAugmentationSequence (X : Scheme.{u}) where
  model : TwoTermDeterminantModel X
  quotient : X.Modules
  d : ℕ
  rank_eq : model.nonnegRank = model.negRank + d
  quotient_free : quotient.IsFiniteLocallyFreeOfRank d
  projection : model.nonneg ⟶ quotient
  zero : model.differential ≫ projection = 0
  exact : (ShortComplex.mk model.differential projection zero).ShortExact

/-- The relation-first formula, on every free chart and for every choice of lifts.
Evaluation of α on the relation wedge is one; no choice of α or of lifts is made.
The definition includes the empty wedges in ranks zero.
Source: Stacks, Tag 0E9Y, displayed formula in the proof
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
def TwoTermAugmentationSequence.IsOrderedWedge {X : Scheme.{u}}
    (S : TwoTermAugmentationSequence X)
    (δ : exteriorSheaf S.quotient S.d ≅ S.model.line) : Prop :=
  ∀ (O : X.Opens) (a : Fin S.model.negRank → Γ(S.model.neg, O))
    (b : Fin S.d → Γ(S.quotient, O)) (l : Fin S.d → Γ(S.model.nonneg, O))
    (α : Γ(dual (exteriorSheaf S.model.neg S.model.negRank), O)),
    α.app (op (Over.mk (𝟙 O)))
      (exteriorSheafSection S.model.neg S.model.negRank O a) = (1 : Γ(X, O)) →
    (∀ j, S.projection.app O (l j) = b j) →
    δ.hom.app O (exteriorSheafSection S.quotient S.d O b) =
      tmulSection (X := X)
        (M := dual (exteriorSheaf S.model.neg S.model.negRank))
        (N := exteriorSheaf S.model.nonneg S.model.nonnegRank) α
        (exteriorSheafSection S.model.nonneg S.model.nonnegRank O
          (fun j ↦ Fin.append (fun k ↦ S.model.differential.app O (a k)) l
            (Fin.cast S.rank_eq j)))

/-- The degree-zero target of the augmentation, including its empty negative term.
Source: Stacks, Tag 0FJI
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
def TwoTermAugmentationSequence.degreeZero {X : Scheme.{u}}
    (S : TwoTermAugmentationSequence X)
    (h0 : (0 : X.Modules).IsFiniteLocallyFreeOfRank 0) : TwoTermDeterminantModel X :=
  ⟨0, S.quotient, 0, 0, S.d, h0, S.quotient_free⟩

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The augmentation and its exterior-model normalization. Its two component equations
fix q to be `(0,p)`, and `degreeZero_normalization` fixes the identification of det(W[0])
by evaluation on the empty negative wedge. The determinant equation concerns this q.
Source: Stacks, Tags 0FJI and 0FJX
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
structure TwoTermAugmentationNormalization {X : Scheme.{u}}
    (S : TwoTermAugmentationSequence X) (T : TwoTermPerfectDeterminantData.{u, w}) where
  zero_rank : (0 : X.Modules).IsFiniteLocallyFreeOfRank 0
  augmentation : S.model.complex ⟶ (S.degreeZero zero_rank).complex
  negative : S.model.negativeMap (S.degreeZero zero_rank) augmentation = 0
  zero : S.model.zeroMap (S.degreeZero zero_rank) augmentation = S.projection
  quasiIso : QuasiIso augmentation
  degreeZeroExterior : (S.degreeZero zero_rank).line ≅ exteriorSheaf S.quotient S.d
  degreeZero_normalization : ∀ (O : X.Opens)
    (α : Γ(dual (exteriorSheaf (0 : X.Modules) 0), O))
    (b : Fin S.d → Γ(S.quotient, O)),
    degreeZeroExterior.hom.app O
        (tmulSection (X := X) α (exteriorSheafSection S.quotient S.d O b)) =
      α.app (op (Over.mk (𝟙 O)))
        (exteriorSheafSection (0 : X.Modules) 0 O Fin.elim0) •
          exteriorSheafSection S.quotient S.d O b
  delta : exteriorSheaf S.quotient S.d ≅ S.model.line
  ordered_wedge : S.IsOrderedWedge delta
  determinant : ∀ e : DerivedCategory.Q.obj S.model.complex ≅
      DerivedCategory.Q.obj (S.degreeZero zero_rank).complex,
    e.hom = DerivedCategory.Q.map augmentation →
    (T.modelIso S.model).symm ≪≫
        twoTermDeterminantIso (T.functor X) (T.model_mem S.model)
          (T.model_mem (S.degreeZero zero_rank)) e ≪≫
        T.modelIso (S.degreeZero zero_rank) ≪≫ degreeZeroExterior = delta.symm

/-- The exterior comparison on quotient wedges for a change of scalars or an isomorphism
of exact sequences. It is specified on pulled-back sections, not chosen up to a scalar.
Source: Stacks, Tags 0FJY and 0E9Y
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
def IsAugmentationQuotientComparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    (S : TwoTermAugmentationSequence X) (S' : TwoTermAugmentationSequence Y)
    (hd : S.d = S'.d) (q : (tensorPullback g).obj S.quotient ≅ S'.quotient)
    (e : (tensorPullback g).obj (exteriorSheaf S.quotient S.d) ≅
      exteriorSheaf S'.quotient S'.d) : Prop :=
  ∀ (O : X.Opens) (b : Fin S.d → Γ(S.quotient, O)),
    e.hom.app (g ⁻¹ᵁ O)
      (tensorPullbackSection g (exteriorSheaf S.quotient S.d) O
        (exteriorSheafSection S.quotient S.d O b)) =
      exteriorSheafSection S'.quotient S'.d (g ⁻¹ᵁ O)
        (fun j ↦ q.hom.app (g ⁻¹ᵁ O)
          (tensorPullbackSection g S.quotient O (b (Fin.cast hd.symm j))))

/-- All compatibilities of a normalized augmentation with arbitrary pullback and with
changes of resolution. Ordinary tensor symmetry is already built into the recorded
pullback determinant predicate. The final clause permits any chain map, including one
whose term maps are not invertible.
Source: Stacks, Tags 0FJI, 0FJX and 0FJY
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
structure TwoTermAugmentationCompatibilities (T : TwoTermPerfectDeterminantData.{u, w})
    (N : ∀ (X : Scheme.{u}) [IsAffine X] (S : TwoTermAugmentationSequence X),
      TwoTermAugmentationNormalization S T) : Prop where
  independent : ∀ (X : Scheme.{u}) [IsAffine X] (S : TwoTermAugmentationSequence X)
    (δ : exteriorSheaf S.quotient S.d ≅ S.model.line),
    S.IsOrderedWedge δ → δ = (N X S).delta
  scalar : ∀ (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (S : TwoTermAugmentationSequence X) (S' : TwoTermAugmentationSequence Y)
    (ha : S.model.negRank = S'.model.negRank)
    (hn : S.model.nonnegRank = S'.model.nonnegRank) (hd : S.d = S'.d)
    (f : (tensorPullback g).obj S.model.neg ≅ S'.model.neg)
    (h : (tensorPullback g).obj S.model.nonneg ≅ S'.model.nonneg)
    (q : (tensorPullback g).obj S.quotient ≅ S'.quotient),
    (tensorPullback g).map S.model.differential ≫ h.hom = f.hom ≫ S'.model.differential →
    (tensorPullback g).map S.projection ≫ q.hom = h.hom ≫ S'.projection →
    ∀ (eL : (tensorPullback g).obj S.model.line ≅ S'.model.line)
      (eW : (tensorPullback g).obj (exteriorSheaf S.quotient S.d) ≅
        exteriorSheaf S'.quotient S'.d),
      IsFlatLCIPullbackDeterminantComparison g S.model.neg S.model.nonneg
        S'.model.neg S'.model.nonneg S.model.negRank S'.model.negRank
        S.model.nonnegRank S'.model.nonnegRank ha hn f.hom h.hom eL →
      IsAugmentationQuotientComparison g S S' hd q eW →
      (tensorPullback g).mapIso (N X S).delta ≪≫ eL = eW ≪≫ (N Y S').delta
  resolution : ∀ (X : Scheme.{u}) [IsAffine X] (S S' : TwoTermAugmentationSequence X)
    (_hq : S.quotient = S'.quotient) (_hd : S.d = S'.d)
    (f : S.model.complex ⟶ S'.model.complex),
    HEq (f ≫ (N X S').augmentation) (N X S).augmentation →
    ∃ e : DerivedCategory.Q.obj S.model.complex ≅ DerivedCategory.Q.obj S'.model.complex,
      e.hom = DerivedCategory.Q.map f ∧
      HEq (((T.modelIso S.model).symm ≪≫
        twoTermDeterminantIso (T.functor X) (T.model_mem S.model)
          (T.model_mem S'.model) e ≪≫ T.modelIso S'.model ≪≫ (N X S').delta.symm).hom)
        (N X S).delta.inv

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]

/-- The exact smooth conormal sequence for an actual adjunction chart. Its negative
map is the specified conormal differential from the cotangent comparison, and its
projection is fixed on universal differentials by the existing source predicate.
Source: Stacks, Tags 0E9Y, 0E9Z and 08SL
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
structure SmoothConormalAugmentation
    {A : Algebra.CotangentResolution.Coherence.{u}} {D : CotangentPresentation.System A}
    {F : CotangentPresentation.AffineIdentifications D}
    {κ : Algebra.CotangentResolution.Naive.Comparison A}
    {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation p d U} (H : FlatLCICotangentChart D F κ E C) where
  rank : (U.ι ≫ p).relativeDifferentials.IsFiniteLocallyFreeOfRank d
  projection : C.differentials ⟶ (U.ι ≫ p).relativeDifferentials
  source : C.IsSourceDifferentialMap projection
  zero : H.differential ≫ projection = 0
  exact : (ShortComplex.mk H.differential projection zero).ShortExact

/-- The exact sequence used by the ordered-wedge map in the smooth chart clause.
Source: Stacks, Tags 0E9Y and 08SL
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
def SmoothConormalAugmentation.sequence
    {A : Algebra.CotangentResolution.Coherence.{u}} {D : CotangentPresentation.System A}
    {F : CotangentPresentation.AffineIdentifications D}
    {κ : Algebra.CotangentResolution.Naive.Comparison A}
    {E : CotangentPresentation.LciIdentifications D F κ}
    {X S : Scheme.{u}} {p : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : FlatLCIPresentation p d U} {H : FlatLCICotangentChart D F κ E C}
    (G : SmoothConormalAugmentation H) : TwoTermAugmentationSequence U.toScheme where
  model := C.determinantModel H.differential H.conormal_free H.differentials_free
  quotient := (U.ι ≫ p).relativeDifferentials
  d := d
  rank_eq := C.rank_eq
  quotient_free := G.rank
  projection := G.projection
  zero := G.zero
  exact := G.exact

/-- The algebraic interpretation with the actual normalized θ and actual smooth β.
The chart map is their composite with the specified adjunction chart comparison.
The equations include its stalk and every extension of the residue field. There is
no arbitrary smooth-locus isomorphism in this predicate.
Source: Stacks, Tags 0E9Y and 0E9Z
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
def IsGeometricAugmentationNormalization (T : TwoTermPerfectDeterminantData.{u, w}) : Prop :=
  ∀ {A : Algebra.CotangentResolution.Coherence.{u}} (D : CotangentPresentation.System A)
    (F : CotangentPresentation.AffineIdentifications D)
    (κ : Algebra.CotangentResolution.Naive.Comparison A)
    (E : CotangentPresentation.LciIdentifications D F κ)
    (_hD : CotangentPresentation.Properties D F κ E)
    (k : Type u) [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {d : ℕ}
    (_hp : Smooth p) (_hpure : X.IsPureDimension d)
    (K : FlatLCIAdjunctionSystem p d) (_hK : K.IsNormalized)
    (H : FlatLCIAdjunctionCotangentNormalization D F κ E K T)
    (B : FlatLCIBaseChange p) (U : B.X'.Opens)
    (C : FlatLCIPresentation B.p' d U)
    (_hs : Smooth (U.ι ≫ B.p'))
    (V : LciDeterminantDescent.SmoothComparison D B.p' d T (H.perfect B) U),
    ∃ G : SmoothConormalAugmentation (H.chart B U C),
      ∃ δ : exteriorSheaf (U.ι ≫ B.p').relativeDifferentials d ≅ C.line,
      G.sequence.IsOrderedWedge δ ∧
      (K.localIso B U C).hom ≫ (tensorPullback U.ι).map (H.theta B).hom ≫
          (V.beta D).hom = δ.inv ∧
      (∀ x : U.toScheme,
        (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).map
          ((K.localIso B U C).hom ≫ (tensorPullback U.ι).map (H.theta B).hom ≫
            (V.beta D).hom) =
        (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).map
          δ.inv) ∧
      (∀ (x : U.toScheme) (L : Type u) [Field L]
        (ρ : U.toScheme.residueField x →+* L),
        (ModuleCat.extendScalars ((ρ.comp (U.toScheme.residue x).hom))).map
          ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).map
            ((K.localIso B U C).hom ≫ (tensorPullback U.ι).map (H.theta B).hom ≫
              (V.beta D).hom)) =
        (ModuleCat.extendScalars ((ρ.comp (U.toScheme.residue x).hom))).map
          ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).map
            δ.inv))

/-- Explicit realization of the ring-module inputs as their associated quasi-coherent
sequence on Spec B. The maps and terms are fixed by the tilde functor. Localized ranks
allow nonfree projective modules and impose nothing at a prime of the zero ring.
Source: Stacks, Tags 0FJB, 0E9Y and 0FJX
(blueprint: lem-trf-two-term-augmentation-determinant-normalization). -/
def HasAffineAugmentationRealizations : Prop :=
  ∀ (B : Type u) [CommRing B] (U V W : ModuleCat.{u} B)
    [Module.Finite B U] [Module.Projective B U]
    [Module.Finite B V] [Module.Projective B V]
    [Module.Finite B W] [Module.Projective B W]
    (i : U ⟶ V) (p : V ⟶ W)
    (_hi : Function.Injective i.hom) (_hp : Function.Surjective p.hom)
    (_hex : Function.Exact i.hom p.hom) (a d : ℕ)
    (_hU : ∀ x : PrimeSpectrum B, Module.rankAtStalk (R := B) U x = a)
    (_hV : ∀ x : PrimeSpectrum B, Module.rankAtStalk (R := B) V x = a + d)
    (_hW : ∀ x : PrimeSpectrum B, Module.rankAtStalk (R := B) W x = d),
    ∃ S : TwoTermAugmentationSequence (Spec (CommRingCat.of B)),
      S.model.neg = tilde U ∧ S.model.nonneg = tilde V ∧ S.quotient = tilde W ∧
      S.model.negRank = a ∧ S.model.nonnegRank = a + d ∧ S.d = d ∧
      HEq S.model.differential
        (tilde.map (R := CommRingCat.of B) (M := U) (N := V) i) ∧
      HEq S.projection (tilde.map (R := CommRingCat.of B) (M := V) (N := W) p)

/-- The ordered-wedge augmentation theorem, expressed on the sheaves of the modules.
This local formulation also supplies exactly the conormal-sequence map in the geometric
clause. In particular it applies on Spec B to every finite projective short exact
sequence, without requiring a global basis, a splitting or positive ranks.
Source: Stacks, Duality, Tags 0E9Y and 0E9Z; More on Algebra, Tag 0FJI;
Perfect Complexes, Tags 0FJX and 0FJY
(blueprint: lem-trf-two-term-augmentation-determinant-normalization).

Proof (the DAG's seven steps):
1. Let L=det U and M=det W. The kernel-first exact-sequence map γ:L⊗M≅det V
   is [lem-trf-projective-determinant-exact-sequence]. Invert evaluation L∨⊗L≅B
   using [lem-trf-line-module-duality], tensor with M, and apply 1⊗γ to obtain δ.
   Its local formula is the displayed relation-first wedge. Changing a relation
   basis multiplies the wedge and its dual by inverse factors. Changing a lift
   adds a wedge with too many relation vectors, hence zero.
2. The augmentation is degreewise surjective with kernel [U→i(U)], identified
   with [U→U]. Its differential generator is i(u)⊗u∨. The Γ construction of
   [lem-trf-two-term-kernel-normalization] sends w⊗this generator to γ(u⊗w)⊗u∨.
   Ordinary tensor symmetry gives precisely δ(w). Thus T_q=δ⁻¹ by
   [lem-trf-surjective-two-term-determinant-calculus], and the canonical exterior
   comparisons of [lem-trf-two-term-perfect-determinant] identify det(q) with T_q.
3. Projectivity of W splits the sequence [lem-weil-pbc-ses-projective-quotient-splits].
   Tensoring this splitting preserves exactness under every scalar extension.
   Exterior powers, duals, evaluation and γ commute with it by
   [lem-trf-projective-exterior-scalar-comparisons]. Consequently δ and its inverse do.
4. [lem-trf-two-term-normalization-locality-equivariance] gives equivariance under
   isomorphisms of exact sequences. An arbitrary chain map over the same quotient
   induces the identity on its only cohomology, so is a derived isomorphism.
   Determinant functoriality gives det(q')det(f)=det(q), hence δ'⁻¹det(f)=δ⁻¹.
5. Empty wedges give the unit formula if a=0 and the acyclic evaluation if d=0.
   If both vanish all maps are unit identifications, without an additional sign.
6. In a regular polynomial presentation the conormal basis is supplied by
   [lem-weil-pbc-regular-sequence-conormal-free]; regular implies Koszul-regular by
   [lem-weil-pbc-regular-sequence-koszul-regular]. The adjunction chart line of
   [lem-trf-flat-lci-canonical-adjunction] is this same exterior line. The specified
   θ of [lem-sfb-adjunction-cotangent-determinant-normalization] takes its comparison
   to the exterior model followed by det(λ).
7. [lem-trf-lci-determinant-descent-smooth] identifies the smooth determinant map
   with det of the canonical cotangent augmentation, hence with δ⁻¹ by step 2.
   Equality on opens gives equality of sheaf maps, then equality on stalks and
   after tensoring with every extension of the residue field. This last assertion
   is recorded by the geometric predicate above with the same fixed θ and smooth comparison.
-/
theorem exists_twoTermAugmentationDeterminantNormalization
    (T : TwoTermPerfectDeterminantData.{u, w}) (hT : T.IsCanonical) :
    ∃ N : ∀ (X : Scheme.{u}) [IsAffine X] (S : TwoTermAugmentationSequence X),
      TwoTermAugmentationNormalization S T,
      TwoTermAugmentationCompatibilities T N ∧ IsGeometricAugmentationNormalization T ∧
        HasAffineAugmentationRealizations.{u} := by
  sorry

end AlgebraicGeometry
