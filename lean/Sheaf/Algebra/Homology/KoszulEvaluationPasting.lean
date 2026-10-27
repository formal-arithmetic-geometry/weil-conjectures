/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Sheaf.Algebra.Homology.PerfectCoinductionTorIndependentExchange
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.TotalTensorSignedCoherence
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Shift.Adjunction
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.RingTheory.KoszulComplementaryEquivalences
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.AlgebraicGeometry.KoszulDifferential
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat

/-! # Ordered Koszul evaluation and signed coinduction pasting

Source: Stacks Project, more-algebra.tex, Tags 0624, 0625, 0664, 0669;
duality.tex, Tag 0BQZ; dualizing.tex, lemma-composition-right-adjoints.
The signed pasting and Tor-independent normalization are the explicit refinement
in (blueprint: lem-sfb-koszul-evaluation-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat
namespace KoszulEvaluation

/-- A quotient presentation, allowing any specified carrier for R/(f).
Source: Stacks 0623, 0BQZ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
structure Presentation (R B : Type u) [CommRing R] [CommRing B] (r : ℕ) where
  tuple : Fin r → R
  quotient : R →+* B
  surjective : Function.Surjective quotient
  kernel : RingHom.ker quotient = Ideal.span (Set.range tuple)

variable {R B : Type u} [CommRing R] [CommRing B] {r : ℕ}

/-- The recorded Koszul complex extended by zero to cohomological degrees.
Source: Stacks 0623 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.complex (F : Presentation R B r) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (ExteriorAlgebra.koszulComplex R r F.tuple).extend ComplexShape.embeddingDownNat

/-- The ordered top exterior line, without choosing its data from an existence theorem.
Source: Stacks 0BQZ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.line (_F : Presentation R B r) : ModuleCat.{u} R :=
  of R (⋀[R]^r (Fin r →₀ R))

/-- The ordered volume, including the empty exterior product.
Source: Stacks 0623 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.volume (F : Presentation R B r) : F.line :=
  exteriorPower.ιMulti R r (fun i ↦ Finsupp.single i 1)

/-- The coefficient V_f[r], in degree -r.
Source: Stacks 0BQZ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.coefficient (F : Presentation R B r) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor _ (-(r : ℤ))).obj F.line

/-- The generator transported to degree -r of the extended Koszul complex.
Source: Stacks 0623 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.top (F : Presentation R B r) : F.complex.X (-(r : ℤ)) :=
  ((ExteriorAlgebra.koszulComplex R r F.tuple).extendXIso
    ComplexShape.embeddingDownNat (i := r) rfl).inv F.volume

/-- The coefficient volume transported into its single complex.
Source: Stacks 0BQZ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.coefficientVolume (F : Presentation R B r) :
    F.coefficient.X (-(r : ℤ)) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (-(r : ℤ)) F.line).inv F.volume

/-- The quotient module as a complex over its own ring.
Source: Stacks 0A70 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def unitComplex (B : Type u) [CommRing B] : CochainComplex (ModuleCat.{u} B) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (of B B)

/-- The quotient module in the derived category.
Source: Stacks 0A70 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def unitObject (B : Type u) [CommRing B] : DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (unitComplex B)

/-- Normalization of the quotient augmentation on the degree-zero exterior power.
Source: Stacks 0623 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.IsAugmentation (F : Presentation R B r)
    (a : F.complex ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((restrictScalars F.quotient).obj (of B B))) : Prop :=
  ∀ x : ⋀[R]^0 (Fin r →₀ R),
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      ((restrictScalars F.quotient).obj (of B B))).hom
      (a.f 0 (((ExteriorAlgebra.koszulComplex R r F.tuple).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
    F.quotient (exteriorPower.zeroEquiv R (Fin r →₀ R) x)

/-- Exactly the hypothesis that the quotient augmentation is a quasi-isomorphism.
Source: Stacks 0669 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.Resolves (F : Presentation R B r) : Prop :=
  ∃ a : F.complex ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((restrictScalars F.quotient).obj (of B B)),
    F.IsAugmentation a ∧ QuasiIso a

/-- The coinduction object with the prescribed precomposition action.
Source: Stacks 0A70, 0A71 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.model (F : Presentation R B r) : DerivedCategory (ModuleCat.{u} B) :=
  (derivedCoinduction F.quotient).obj (DerivedCategory.Q.obj F.coefficient)

/-- The forward trace is the top-coefficient chain map on the normalized total Hom model.
All nonzero degrees map to zero, because the target is a single complex.
Source: Stacks 0BQZ, 0A71 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Presentation.IsNormalized (F : Presentation R B r) (τ : F.model ≅ unitObject B) : Prop :=
  ∃ (a : F.complex ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((restrictScalars F.quotient).obj (of B B)))
    (e : DerivedCategory.Q.obj (CochainComplex.moduleHomComplex F.complex F.coefficient) ≅
      (restrictScalars F.quotient).mapDerivedCategory.obj F.model)
    (π : CochainComplex.moduleHomComplex F.complex F.coefficient ⟶
      ((restrictScalars F.quotient).mapHomologicalComplex (.up ℤ)).obj (unitComplex B)),
    F.IsAugmentation a ∧ QuasiIso a ∧
    CoinductionHomModel F.quotient F.complex F.coefficient a e ∧
    (∀ (z : (CochainComplex.moduleHomComplex F.complex F.coefficient).X 0) (c : R),
      (HomologicalComplex.singleObjXSelf (.up ℤ) (-(r : ℤ)) F.line).hom
        ((z.v (-(r : ℤ)) (-(r : ℤ)) (add_zero _)) F.top) = c • F.volume →
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (of B B)).hom (π.f 0 z) =
        F.quotient c) ∧
    e.hom ≫ (restrictScalars F.quotient).mapDerivedCategory.map τ.hom ≫
      (restrictScalars F.quotient).mapDerivedCategoryFactors.hom.app (unitComplex B) =
        DerivedCategory.Q.map π

/-- Coinduction transitivity from uniqueness of right adjoints to the composed restriction.
Its counit is the composite of the two evaluation-at-one counits.
Source: Stacks 0C0F (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def coinductionComp {D : Type u} [CommRing D] (f : R →+* B) (g : B →+* D) :
    derivedCoinduction (g.comp f) ≅ derivedCoinduction f ⋙ derivedCoinduction g :=
  ((((derivedCoinductionAdjunction g).comp (derivedCoinductionAdjunction f)).ofNatIsoLeft
    (Functor.mapDerivedCategoryNatIso (restrictScalarsComp f g) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm).rightAdjointUniq
        (derivedCoinductionAdjunction (g.comp f))).symm

/-- The shift comparison fixed by the evaluation adjunction.
On total Hom models this is the unsigned `Cochain.rightShift`. It already incorporates
the right-shift identification s²_b in t^Ch = s¹[b] ∘ s²_b.
Source: Stacks 0A70, 0FPQ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def coinductionShift (f : R →+* B) (n : ℤ) :
    shiftFunctor _ n ⋙ derivedCoinduction f ≅ derivedCoinduction f ⋙ shiftFunctor _ n :=
  ((derivedCoinductionAdjunction f).rightAdjointCommShift ℤ).commShiftIso n

/-- A scalar comparison on a single finite free coefficient, fixed on pure tensors.
The counit equation identifies it with the existing derived extension, without choosing
an arbitrary derived isomorphism.
Source: Stacks 06Y6, 0A6A (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def IsSingleScalarComparison {S : Type u} [CommRing S] (g : R →+* S)
    (d : CoinductionScalarPair g) (n : ℤ) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (l : M ⟶ (restrictScalars g).obj N)
    (c : d.F.obj (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ n).obj M)) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ n).obj N)) : Prop :=
  ∃ e : ((extendScalars g).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ n).obj M) ≅
        (CochainComplex.singleFunctor _ n).obj N,
    (∀ (t : S) (x : M),
      (HomologicalComplex.singleObjXSelf (.up ℤ) n N).hom
        (e.hom.f n (t ⊗ₜ[R,g]
          (HomologicalComplex.singleObjXSelf (.up ℤ) n M).inv x)) = t • l x) ∧
    c.hom = d.counit.app ((CochainComplex.singleFunctor _ n).obj M) ≫
      DerivedCategory.Q.map e.hom

/-- The two coefficient maps used in pasting, expressed in the ordered trivializations.
After the s²_b identification already present in `coinductionShift`, the first
map sends the concatenated volume to the shifted first volume with no extra sign.
The second sends 1 to the ordered second volume over B. These coordinate equations
uniquely determine both maps; the raw t^Ch sign remains in the pasted evaluation.
Source: Stacks 0664, 0FPQ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def IsPastingCoefficient {D : Type u} [CommRing D] {s : ℕ}
    (F : Presentation R B r) (G : Presentation B D s) (H : Presentation R D (r + s))
    (k : H.coefficient ≅ F.coefficient⟦(s : ℤ)⟧)
    (l : (unitComplex B)⟦(s : ℤ)⟧ ≅ G.coefficient) : Prop :=
  (F.coefficient.shiftFunctorObjXIso (s : ℤ) (-((r + s : ℕ) : ℤ))
    (-(r : ℤ)) (by omega)).hom
      (k.hom.f (-((r + s : ℕ) : ℤ)) H.coefficientVolume) =
      F.coefficientVolume ∧
  l.hom.f (-(s : ℤ))
    (((unitComplex B).shiftFunctorObjXIso (s : ℤ) (-(s : ℤ)) 0 (by omega)).inv
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (of B B)).inv 1)) =
    G.coefficientVolume

/-- Contract the first ordered coefficient, using the adjunction-normalized shift.
The shift comparison incorporates s²_b from t^Ch = s¹[b] ∘ s²_b, so the ordered
coefficient map `k` is unsigned. In the ordered trivialization of the second exterior
line this is the coinduction tensor comparison followed by tau_f.
Source: Stacks 0A70, 0BQZ, 0FPQ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def firstContraction {D : Type u} [CommRing D] {s : ℕ}
    (F : Presentation R B r) (G : Presentation B D s) (H : Presentation R D (r + s))
    (τ : F.model ≅ unitObject B)
    (k : H.coefficient ≅ F.coefficient⟦(s : ℤ)⟧)
    (l : (unitComplex B)⟦(s : ℤ)⟧ ≅ G.coefficient) :
    (derivedCoinduction F.quotient).obj (DerivedCategory.Q.obj H.coefficient) ⟶
      DerivedCategory.Q.obj G.coefficient :=
  (derivedCoinduction F.quotient).map (DerivedCategory.Q.map k.hom) ≫
    (derivedCoinduction F.quotient).map
      ((DerivedCategory.Q.commShiftIso (s : ℤ)).hom.app F.coefficient) ≫
    (coinductionShift F.quotient (s : ℤ)).hom.app (DerivedCategory.Q.obj F.coefficient) ≫
    τ.hom⟦(s : ℤ)⟧' ≫
    (DerivedCategory.Q.commShiftIso (s : ℤ)).inv.app (unitComplex B) ≫
    DerivedCategory.Q.map l.hom

/-- The actual transitivity and evaluation composite in D(D).
Source: Stacks 0C0F (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def pasted {D : Type u} [CommRing D] {s : ℕ}
    (F : Presentation R B r) (G : Presentation B D s) (H : Presentation R D (r + s))
    (h : H.quotient = G.quotient.comp F.quotient)
    (τ : F.model ≅ unitObject B) (υ : G.model ≅ unitObject D)
    (k : H.coefficient ≅ F.coefficient⟦(s : ℤ)⟧)
    (l : (unitComplex B)⟦(s : ℤ)⟧ ≅ G.coefficient) : H.model ⟶ unitObject D :=
  (eqToIso (congrArg (fun q : R →+* D ↦
    (derivedCoinduction q).obj (DerivedCategory.Q.obj H.coefficient)) h)).hom ≫
    (coinductionComp F.quotient G.quotient).hom.app (DerivedCategory.Q.obj H.coefficient) ≫
    (derivedCoinduction G.quotient).map (firstContraction F G H τ k l) ≫ υ.hom

/-- Pasting for every ordered second block and every specified concatenation.
The final universal equation also handles the comparison multiplied by (-1)^(rs):
its normalized factor is (-1)^(rs) instead of 1. The standard unsigned coefficient
map uses the s²_b identification in `coinductionShift` and gives the signed evaluation.
Source: Stacks 0664, 0669, 0C0F (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def Pasting (F : Presentation R B r) (τ : F.model ≅ unitObject B) : Prop :=
  ∀ (D : Type u) [CommRing D] (s : ℕ) (g : Fin s → R)
    (G : Presentation B D s) (H : Presentation R D (r + s)),
    (∀ i, G.tuple i = F.quotient (g i)) → H.tuple = Fin.append F.tuple g →
    ∀ h : H.quotient = G.quotient.comp F.quotient,
    G.Resolves → H.Resolves ∧
    ∀ (υ : G.model ≅ unitObject D) (ω : H.model ≅ unitObject D),
      G.IsNormalized υ → H.IsNormalized ω →
      (∃ (k : H.coefficient ≅ F.coefficient⟦(s : ℤ)⟧)
        (l : (unitComplex B)⟦(s : ℤ)⟧ ≅ G.coefficient), IsPastingCoefficient F G H k l) ∧
      (∀ (k : H.coefficient ≅ F.coefficient⟦(s : ℤ)⟧)
        (l : (unitComplex B)⟦(s : ℤ)⟧ ≅ G.coefficient),
        IsPastingCoefficient F G H k l →
        pasted F G H h τ υ k l = ((r : ℤ) * (s : ℤ)).negOnePow • ω.hom) ∧
      (∀ (k : H.coefficient ≅ F.coefficient⟦(s : ℤ)⟧)
        (l : (unitComplex B)⟦(s : ℤ)⟧ ≅ G.coefficient),
        (F.coefficient.shiftFunctorObjXIso (s : ℤ) (-((r + s : ℕ) : ℤ))
          (-(r : ℤ)) (by omega)).hom
          (k.hom.f (-((r + s : ℕ) : ℤ)) H.coefficientVolume) =
            ((r : ℤ) * (s : ℤ)).negOnePow • F.coefficientVolume →
        l.hom.f (-(s : ℤ))
          (((unitComplex B).shiftFunctorObjXIso (s : ℤ) (-(s : ℤ)) 0 (by omega)).inv
            ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (of B B)).inv 1)) =
          G.coefficientVolume → pasted F G H h τ υ k l = ω.hom)

/-- Tor-independent scalar naturality, including the augmentation and the actual counit mate.
A pushout of commutative rings is exactly the specified tensor-product quotient carrier.
The exchange tower records successive extension; the same formula includes identity
extension and localization, without an extra flatness hypothesis.
Source: Stacks 0621, 0A6A (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def ScalarNaturality (F : Presentation R B r) (τ : F.model ≅ unitObject B) : Prop :=
  ∀ (S A : Type u) [CommRing S] [CommRing A]
    (g : R →+* S) (b : B →+* A) (F' : Presentation S A r),
    IsPushout (CommRingCat.ofHom F.quotient) (CommRingCat.ofHom g)
      (CommRingCat.ofHom b) (CommRingCat.ofHom F'.quotient) →
    (∀ i, F'.tuple i = g (F.tuple i)) →
    ∀ (dR : CoinductionScalarPair g) (dB : CoinductionScalarPair b),
      Nonempty (dR.F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars F.quotient).obj (of B B))) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
            ((restrictScalars F'.quotient).obj (of A A))) →
      F'.Resolves ∧
      ∃ θ : dB.F ⋙ (restrictScalars F'.quotient).mapDerivedCategory ≅
          (restrictScalars F.quotient).mapDerivedCategory ⋙ dR.F,
        CoinductionTensorNormalized F.quotient g b F'.quotient dR dB θ ∧
        CoinductionExchangeTower.{u, u, u, u, u, u, u}
          F.quotient g b F'.quotient dR dB θ ∧
        ∀ τ' : F'.model ≅ unitObject A, F'.IsNormalized τ' →
          ∃ (l : F.line ⟶ (restrictScalars g).obj F'.line)
            (cR : dR.F.obj (DerivedCategory.Q.obj F.coefficient) ≅
              DerivedCategory.Q.obj F'.coefficient)
            (cB : dB.F.obj (unitObject B) ≅ unitObject A),
            l F.volume = F'.volume ∧
            IsSingleScalarComparison g dR (-(r : ℤ)) F.line F'.line l cR ∧
            IsSingleScalarComparison b dB 0 (of B B) (of A A)
              (unitToRestrictScalars b) cB ∧
            dB.F.map τ.hom ≫ cB.hom =
              coinductionScalarExchange F.quotient F'.quotient dR dB θ
                (DerivedCategory.Q.obj F.coefficient) ≫
              (derivedCoinduction F'.quotient).map cR.hom ≫ τ'.hom

/-- Change of ordered generators by an invertible linear map, equivalently M transpose
for f'=Mf. Every degree of the Koszul isomorphism and the coefficient line is specified.
In particular the top comparison preserves the volume whenever its determinant is 1,
as for a triangular matrix with diagonal 1.
Source: Stacks 0624, 0625 (blueprint: lem-sfb-koszul-evaluation-pasting). -/
def GeneratorNaturality (F : Presentation R B r) (τ : F.model ≅ unitObject B) : Prop :=
  ∀ (G : Presentation R B r) (hq : F.quotient = G.quotient)
    (T : (Fin r →₀ R) ≃ₗ[R] (Fin r →₀ R)),
    (Finsupp.linearCombination R F.tuple).comp T.toLinearMap =
      Finsupp.linearCombination R G.tuple →
    G.Resolves ∧
    ∃ (U : G.complex ≅ F.complex) (a : G.coefficient ≅ F.coefficient),
      (∀ n : ℕ,
        ((ExteriorAlgebra.koszulComplex R r G.tuple).extendXIso
          ComplexShape.embeddingDownNat (i := n) rfl).inv ≫
          U.hom.f (-(n : ℤ)) ≫
          ((ExteriorAlgebra.koszulComplex R r F.tuple).extendXIso
            ComplexShape.embeddingDownNat (i := n) rfl).hom =
          ofHom (exteriorPower.map n T.toLinearMap)) ∧
      (∀ x : G.line,
        (HomologicalComplex.singleObjXSelf (.up ℤ) (-(r : ℤ)) F.line).hom
          (a.hom.f (-(r : ℤ))
            ((HomologicalComplex.singleObjXSelf (.up ℤ) (-(r : ℤ)) G.line).inv x)) =
          exteriorPower.map r T.toLinearMap x) ∧
      (∀ υ : G.model ≅ unitObject B, G.IsNormalized υ →
        τ.hom = (derivedCoinduction F.quotient).map (DerivedCategory.Q.map a.inv) ≫
          (eqToIso (congrArg (fun q : R →+* B ↦
            (derivedCoinduction q).obj (DerivedCategory.Q.obj G.coefficient)) hq)).hom ≫
          υ.hom) ∧
      (exteriorPower.map r T.toLinearMap G.volume = F.volume →
        a.hom.f (-(r : ℤ)) G.coefficientVolume = F.coefficientVolume)

/-- A finite ordered iteration of the corrected coefficient convention. A step multiplies
by (-1)^(pq) to replace t^Ch by (-1)^(pq)t^Ch, exactly as in the equivalent formulation
of the statement. The intermediate ring and either block may be zero or empty.
Source: Stacks 0664, 0C0F, 0FPQ (blueprint: lem-sfb-koszul-evaluation-pasting). -/
inductive OrderedPasting :
    {S A : Type u} → [CommRing S] → [CommRing A] → {n : ℕ} →
      (H : Presentation S A n) → (H.model ⟶ unitObject A) → Prop
  | single {S A : Type u} [CommRing S] [CommRing A] {n : ℕ}
      (H : Presentation S A n) (τ : H.model ≅ unitObject A)
      (hτ : H.IsNormalized τ) : OrderedPasting H τ.hom
  | step {S A D : Type u} [CommRing S] [CommRing A] [CommRing D] {p q : ℕ}
      (F : Presentation S A p) (G : Presentation A D q) (H : Presentation S D (p + q))
      (g : Fin q → S) (hg : ∀ i, G.tuple i = F.quotient (g i))
      (hH : H.tuple = Fin.append F.tuple g)
      (h : H.quotient = G.quotient.comp F.quotient)
      (τ : F.model ≅ unitObject A) (hτ : OrderedPasting F τ.hom)
      (υ : G.model ⟶ unitObject D) (hυ : OrderedPasting G υ)
      (k : H.coefficient ≅ F.coefficient⟦(q : ℤ)⟧)
      (l : (unitComplex A)⟦(q : ℤ)⟧ ≅ G.coefficient)
      (hc : IsPastingCoefficient F G H k l) :
      OrderedPasting H
        (((p : ℤ) * (q : ℤ)).negOnePow •
          ((eqToIso (congrArg (fun t : S →+* D ↦
            (derivedCoinduction t).obj (DerivedCategory.Q.obj H.coefficient)) h)).hom ≫
            (coinductionComp F.quotient G.quotient).hom.app
              (DerivedCategory.Q.obj H.coefficient) ≫
            (derivedCoinduction G.quotient).map (firstContraction F G H τ k l) ≫ υ))

/-- The top-normalized Koszul evaluation isomorphism, with all signed naturality laws.
Empty tuples, a zero quotient, and the zero base ring are included.

Source: Stacks Project, more-algebra.tex, Tags 0624, 0625, 0664 and 0669;
duality.tex, Tag 0BQZ; dualizing.tex, lemma-composition-right-adjoints.
The explicit counit-normalized, Tor-independent, signed refinement is
(blueprint: lem-sfb-koszul-evaluation-pasting).

Proof:
1. Put P=K_R(f), L=V_f[r], E=Hom_R(P,L). The increasing-wedge basis makes P
bounded finite free and V_f free on the ordered volume
(lem-weil-pbc-exterior-power-free-basis). The projective evaluation model
(lem-pod-projective-hom-evaluation-model) and the complementary Koszul dual
(lem-sc-koszul-complementary-equivalences) identify H^n(E) with zero for n != 0.
In degree zero the incoming Hom differential evaluates to the ideal generated by f
in the top coefficient line. Thus [z] maps to q(c) when z(v_f)=c v_f, giving
H^0(E)=B. For r=0 there is no incoming differential and the ideal is zero.
2. The B-action is precomposition, as fixed by
lem-trf-derived-coinduction-adjunction. A lift of b to R acts on P by scalar
multiplication and hence on top evaluation by b. A different lift changes the
coefficient by the boundary ideal. The normalization is therefore B-linear.
Use lem-sf-derived-concentrated-single to get tau in D(B), normalized on H^0.
Full faithfulness of single complexes
(lem-weil-pbc-derived-single-fully-faithful) makes this normalization unique.
The projective Hom model, normalized through its K-injective comparison, gives
exactly the chain map pi in IsNormalized. No faithfulness of restriction on
arbitrary derived morphisms is asserted.
3. The wedgewise scalar comparison preserves quotient augmentations
(lem-trf-koszul-augmented-scalar-extension). Tor independence makes the extended
augmentation a resolution (lem-trf-koszul-augmentation-kflat-model).
The perfect coinduction exchange
(lem-sfb-perfect-coinduction-tor-independent-exchange) is the mate of the extended
evaluation counit and on Hom models sends z tensor t to the functional
(x tensor s -> ts(z(x) tensor 1)). Both top reductions are q(c)t, proving the
square by single-complex full faithfulness. Its exchange tower gives successive
and identity compatibility. Localization is a case since it is flat
(lem-weil-pbc-localization-flat).
4. For f'=Mf use T=M transpose. The equality of contraction forms implies that
exteriorPower.map T commutes with every differential
(lem-weil-pbc-koszul-differential); its inverse is induced by T inverse.
In degree zero it is the identity, so augmentations agree. Write a=wedge^r T.
The Hom map is z -> a inverse z wedge(T), and if z(v_f)=c v_f its image also
has coefficient c. This proves GeneratorNaturality. A triangular matrix with
diagonal 1 fixes the ordered top volume.
5. The ordered exterior product identifies P tensor K_R(g) with K_R(f,g).
Increasing subsets of the disjoint ordered blocks give a bijection of bases.
Contraction obeys d(x wedge y)=dx wedge y+(-1)^deg(x) x wedge dy, so this is a
chain isomorphism. The second Koszul complex is bounded free, hence K-flat
(lem-weil-pbc-projective-module-flat, lem-pc-module-bounded-flat-kflat,
def-pc-module-kflat-complex). Tensor the first augmentation with it, then use
lem-trf-koszul-augmented-scalar-extension and the second augmentation. This proves
that the concatenated augmentation resolves D, with the first block ordered first.
6. The comparison in lem-sfb-perfect-resolution-coinduction-comparison identifies
the actual right-adjoint composition with signed block exchange followed by
Hom currying. Its counit is evaluation at 1 twice, exactly the composed counit
of lem-cat-right-adjoint-composition and
lem-trf-derived-coinduction-adjunction. Extract the right coefficient and apply
the two top reductions. The ordered trivialization of its free rank-one line
identifies this extraction with firstContraction. These are equations in D(D).
7. In the raw coefficient tensor V_f[r] tensor V_g[s], right coefficient insertion
is h tensor t -> (x -> (-1)^(deg(t)deg(x))h(x) tensor t): move t past h, use
unsigned left insertion (lem-trf-coinduction-tensor-comparison-model), and move
it back past h(x). The block flip and right coefficient extraction contribute
two factors (-1)^(rs), which cancel. The remaining t^Ch coefficient comparison
has sign (-1)^(rs) (lem-pur-total-tensor-signed-coherence).
To express it through firstContraction, use t^Ch = s¹[b] composed with s²_b.
The whole (-1)^(bp) factor belongs to this right-shift identification s²_b.
The adjunction comparison coinductionShift is unsigned Cochain.rightShift on
Hom models and already incorporates s²_b. Consequently k sends the concatenated
volume to the shifted first volume without an extra sign, exactly as specified
by IsPastingCoefficient. With this unsigned k, pasted=(-1)^(rs)tau_H.
Multiplying k by (-1)^(rs) instead gives tau_H, as in the third Pasting conjunct.
The generator equations uniquely determine these maps between single free lines.
For r=s=1 over Q[x,y], d(e_x wedge e_y)=x e_y-y e_x and the counit-pinned
composition comparison is -1 on top functionals: unsigned k gives -tau_H,
whereas signed k gives tau_H.
8. Wedge maps and top reduction commute with the scalar formula in step 3, so
the pasting equations remain valid after all admissible scalar extensions.
For three blocks the exponents are pq+(p+q)t and qt+p(q+t), which agree.
The unsigned associator, signed shift coherence, and composite evaluation counit
therefore give equality for both parenthesizations. Induct on OrderedPasting to
obtain all finite ordered iterates; its scalar correction records precisely the
equivalent corrected coefficient convention of step 7. Empty blocks have exponent
zero. In a zero quotient all targets are zero; in the zero base ring all modules
are zero. None of these arguments assumes a proper ideal or a nonzero ring. -/
theorem koszul_evaluation_pasting (F : Presentation R B r) (hF : F.Resolves) :
    ∃ τ : F.model ≅ unitObject B,
      F.IsNormalized τ ∧
      (∀ υ : F.model ≅ unitObject B, F.IsNormalized υ → υ = τ) ∧
      ScalarNaturality F τ ∧ GeneratorNaturality F τ ∧ Pasting F τ ∧
      (∀ m : F.model ⟶ unitObject B, OrderedPasting F m → m = τ.hom) := by
  sorry

end KoszulEvaluation
end ModuleCat
