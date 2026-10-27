/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FourierAdicCharacterOf
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.WeilComplexTraceFunction
public import Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Sheaf.Paper.FiniteEtaleAdicCohomology
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import WeilConjectures.WeilSheaf.ArtinSchreierTrace
import WeilConjectures.FourierTransform.ArtinSchreierCohomology

/-! # Properties of the adic Artin--Schreier character sheaf

Source: main-20261015, sec-fourier-transform/sk-lem-as-properties/_section.md
(blueprint: sk-lem-as-properties).
The degree-q definition and the auxiliary degree-p cover are kept distinct. All
coefficient objects below are completed integral realizations followed by the recorded
rationalization and common-stage inclusion; none is a discrete rational etale sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

/-- Invertibility inherited from the fixed finite-field model.
Source: standing coefficient convention (blueprint: sk-lem-as-properties). -/
@[instance_reducible]
def fourierPropertyPrimeInvertible (F : FourierSetting.{u})
    (X₀ : Over (Spec (.of F.field.k₀))) (x : X₀.left) :
    Invertible (F.coefficients.l : X₀.left.residueField x) :=
  letI := fourierPrimeAlgebra F
  letI : CharP F.field.k₀ F.field.p := charP_of_injective_algebraMap'
    (ZMod F.field.p) F.field.p
  let h : IsUnit (F.coefficients.l : F.field.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime F.field.k₀
      (Fact.out : F.coefficients.l.Prime) F.coefficients.different.symm).isUnit
  let φ := ((Scheme.ΓSpecIso (.of F.field.k₀)).inv ≫ X₀.hom.appTop ≫
    X₀.left.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ F.coefficients.l)) (h.map φ)).invertible

/-- The base change to the prime field, induced by the given finite-field structure.
It also exists on the empty scheme. Source: the auxiliary prime-degree cover
(blueprint: sk-lem-as-properties). -/
@[instance_reducible]
def fourierPrimeOver (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] : X.Over (Spec (.of (ULift.{u} (ZMod F.field.p)))) :=
  letI := fourierPrimeAlgebra F
  ⟨(X ↘ Spec (.of F.field.k₀)) ≫ Spec.map (CommRingCat.ofHom
    ((algebraMap (ZMod F.field.p) F.field.k₀).comp ULift.ringEquiv.toRingHom))⟩

/-- The prime-field character sheaf before completion, with the same integral lift.
Source: prime-degree character decomposition (blueprint: sk-lem-as-properties). -/
def fourierPrimeEtaleCharacterOf (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) :=
  letI := fourierPrimeOver F X
  letI : Invertible (Fintype.card (ULift.{u} (ZMod F.field.p)) : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers F.coefficients.l (fourierCoefficient F))) :=
    Eq.mp (congrArg (fun n : ℕ ↦ Invertible (n : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers F.coefficients.l (fourierCoefficient F))))
      ((Fintype.card_ulift (ZMod F.field.p)).trans (ZMod.card F.field.p)).symm)
      (fourierIntegerPrimeInvertible F)
  Etale.artinSchreierSheafOf X
    ((fourierIntegralCharacter F Ψ).compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f

/-- The prime-degree character and finite direct image, both completed in degree zero.
The Boolean index selects the direct image or its specified character summand.
Source: prime-degree decomposition and its finite-level realization
(blueprint: sk-lem-as-properties). -/
def fourierPrimeIntegralObject (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) (push : Bool) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (fourierCompletedRealization F.coefficients.l (fourierCoefficient F) X
      (if push then (Etale.lowerStar _ (artinSchreierFunctionProjection X F.field.p f)).obj
        ((constantSheaf (artinSchreierFunctionCover X F.field.p f).smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers
            F.coefficients.l (fourierCoefficient F))))).obj (ModuleCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers
              F.coefficients.l (fourierCoefficient F)))
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers
              F.coefficients.l (fourierCoefficient F)))))
      else fourierPrimeEtaleCharacterOf F X Ψ f))

/-- The prime-degree realized objects are constructible and derived complete.
Source: Steps 1--3 of the DAG proof (blueprint: sk-lem-as-properties).
Proof: the torsor is finite etale, so finite exchange identifies its direct image
locally with p copies of the completed unit. Each integral character projector has
rank-one image by evaluation at zero. The descriptions commute with all finite
coefficient reductions. The completed free modules are derived complete, with
constructible reductions uniformly in degree zero; descend along the finite cover. -/
theorem fourierPrimeIntegralObject_mem (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsNoetherian X]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) (push : Bool) :
    sfIntegralConstructible F.coefficients.l (fourierCoefficient F) X
      (fourierPrimeIntegralObject F X Ψ f push) := by
  sorry

/-- Rationalized prime-degree direct image or character summand at the fixed stage.
Source: adic realization paragraph (blueprint: sk-lem-as-properties). -/
def fourierPrimeObject (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsNoetherian X]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) (push : Bool) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar X :=
  ⟨fourierCoefficientStage F,
    (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F) X).obj
      ⟨fourierPrimeIntegralObject F X Ψ f push,
        fourierPrimeIntegralObject_mem F X Ψ f push⟩⟩

/-- The canonical arithmetic descent Weil structure on the current degree-q sheaf.
Source: sk-def-as and Step 6 of this unit (blueprint: sk-lem-as-properties). -/
def fourierCharacterWeil (F : FourierSetting.{u})
    (X₀ : Over (Spec (.of F.field.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsNoetherian X₀.left]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X₀.left, ⊤)) :=
  letI := fourierPropertyPrimeInvertible F X₀
  letI := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  letI := fourierBaseFintype F
  IsoAlgebra.mk
    ((commonStageDerivedPullback F.coefficients.l F.coefficients.Qbar
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom
        (algebraMap F.field.k₀ F.field.k))))).obj (fourierCharacterOf F X₀.left Ψ f))
    ((localQbarPullbackComposition F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFrobenius X₀).hom
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom
        (algebraMap F.field.k₀ F.field.k)))) (fourierCharacterOf F X₀.left Ψ f)).symm ≪≫
      eqToIso (congrArg (fun h ↦ (commonStageDerivedPullback F.coefficients.l
        F.coefficients.Qbar h).obj (fourierCharacterOf F X₀.left Ψ f))
        (F.field.galoisMap_projections X₀.hom
          (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic F.field.k₀ F.field.k)).1))

/-- The closed-point value psi(Tr_(kappa(u)/k0)(f(u))).
Source: trace clause (blueprint: sk-lem-as-properties). -/
def fourierClosedCharacterValue (F : FourierSetting.{u})
    (X₀ : Over (Spec (.of F.field.k₀)))
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X₀.left, ⊤))
    (y : X₀.left) : F.coefficients.Qbar :=
  letI := fourierPrimeAlgebra F
  letI := (X₀.hom.residueFieldAlgebraMap y).toAlgebra
  (Ψ.compAddMonoidHom (Algebra.trace (ZMod F.field.p) F.field.k₀).toAddMonoidHom)
    (Algebra.trace F.field.k₀ (X₀.left.residueField y) (X₀.left.Γevaluation y f))

/-- The same scalar using the absolute prime-field trace.
Source: trace transitivity clause (blueprint: sk-lem-as-properties). -/
def fourierClosedPrimeValue (F : FourierSetting.{u})
    (X₀ : Over (Spec (.of F.field.k₀)))
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X₀.left, ⊤))
    (y : X₀.left) : F.coefficients.Qbar :=
  letI := fourierPrimeAlgebra F
  letI := ((X₀.hom.residueFieldAlgebraMap y).comp
    (algebraMap (ZMod F.field.p) F.field.k₀)).toAlgebra
  Ψ (Algebra.trace (ZMod F.field.p) (X₀.left.residueField y) (X₀.left.Γevaluation y f))

/-- Ordinary adic cohomology, as shifted Hom from the actual coefficient unit on
this geometric fibre. Source: final paragraph (blueprint: sk-lem-as-properties). -/
def fourierCharacterCohomology (F : FourierSetting.{u})
    (X₀ : Over (Spec (.of F.field.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom]
    (K : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber X₀).left) (i : ℕ) :=
  letI := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  ModuleCat.of F.coefficients.Qbar
    (pullbackTensorCommonUnit F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber X₀).left ⟶ K⟦(i : ℤ)⟧)

/-- The prime-degree torsor and its two different automorphism groups.
Source: first paragraph and Step 1 (blueprint: sk-lem-as-properties).
Proof: lem-fd-as-cover gives finite etaleness and the p translations. The derivative
is -1 and a geometric fibre is the set of p roots differing by prime-field constants.
A commuting automorphism is translation by a locally constant section of Fp. On a
nonempty connected base such a section is constant. On a nonempty connected total
space any cover automorphism has one translation value, so all automorphisms are
translations. The split cover instead permits all permutations of its components. -/
theorem fourierPrimeCover_properties (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsSeparated (X ↘ Spec (.of F.field.k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.field.k₀))]
    [QuasiCompact (X ↘ Spec (.of F.field.k₀))] (f : Γ(X, ⊤)) :
    IsFinite (artinSchreierFunctionProjection X F.field.p f) ∧
    Etale (artinSchreierFunctionProjection X F.field.p f) ∧
    ∃ σ : Multiplicative (ZMod F.field.p) →*
        Aut (Over.mk (artinSchreierFunctionProjection X F.field.p f)),
      (∀ a : ZMod F.field.p,
        (σ (Multiplicative.ofAdd a)).hom.left.appTop
            (artinSchreierFunctionRoot X F.field.p f) =
          artinSchreierFunctionRoot X F.field.p f +
            (artinSchreierFunctionProjection X F.field.p f).appTop
              (artinSchreierBaseConstants F.field.k₀ X
                (@algebraMap (ZMod F.field.p) F.field.k₀ _ _ (fourierPrimeAlgebra F) a))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Nonempty ↥(pullback (artinSchreierFunctionProjection X F.field.p f) x : Scheme.{u}) ∧
        Nat.card ↥(pullback (artinSchreierFunctionProjection X F.field.p f) x : Scheme.{u}) =
          F.field.p ∧
        ∀ z z' : ↥(pullback (artinSchreierFunctionProjection X F.field.p f) x : Scheme.{u}),
          ∃! a : Multiplicative (ZMod F.field.p),
            artinSchreierFibreMap _ _ x (σ a).hom.left (Over.w (σ a).hom) z = z') ∧
      Nonempty (Subgroup.centralizer (Set.range σ) ≃*
        LocallyConstant X (Multiplicative (ZMod F.field.p))) ∧
      (ConnectedSpace X → Nonempty (LocallyConstant X (Multiplicative (ZMod F.field.p)) ≃*
        Multiplicative (ZMod F.field.p))) ∧
      (ConnectedSpace (artinSchreierFunctionCover X F.field.p f) → Function.Bijective σ) := by
  sorry

/-- The zero cover is the split p-fold cover, with its specified root sections.
Source: first-paragraph split example (blueprint: sk-lem-as-properties).
Proof: T^p-T factors into the pairwise coprime linear factors T-a. The Chinese
remainder isomorphisms give the displayed sections and coproduct universal property.
Their coordinates specify the usual split-cover isomorphism, including when X is empty. -/
theorem fourierPrimeCover_zero (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] :
    ∃ s : ZMod F.field.p → (X ⟶ artinSchreierFunctionCover X F.field.p 0),
      (∀ a, s a ≫ artinSchreierFunctionProjection X F.field.p 0 = 𝟙 X) ∧
      (∀ a, (s a).appTop (artinSchreierFunctionRoot X F.field.p 0) =
        artinSchreierBaseConstants F.field.k₀ X
          (@algebraMap (ZMod F.field.p) F.field.k₀ _ _ (fourierPrimeAlgebra F) a)) ∧
      Nonempty (IsColimit (Cofan.mk (artinSchreierFunctionCover X F.field.p 0) s)) := by
  sorry

/-- The explicitly stated S3 counterexample to the unrestricted automorphism claim.
Source: first paragraph (blueprint: sk-lem-as-properties).
Proof: the zero cover over Spec F3 is three copies of Spec F3. An automorphism over
the base permutes these three components arbitrarily, giving the permutation group. -/
theorem fourierPrimeCover_three_aut :
    Nonempty (Aut (Over.mk (artinSchreierFunctionProjection
      (Spec (.of (ZMod 3))) 3 0)) ≃* Equiv.Perm (ZMod 3)) := by
  sorry

/-- The coordinate prime-degree cover of the line is y maps to y^p-y.
Source: Step 2, lem-fd-as-cover-affine-line (blueprint: sk-lem-as-properties).
Proof: the equation y^p-y=x eliminates x. Projection to y and the graph of y^p-y
are inverse morphisms over the x-line. -/
theorem fourierPrimeCover_line (F : FourierSetting.{u}) :
    Nonempty (Over.mk (artinSchreierFunctionProjection
        (AffineSpace PUnit (Spec (.of F.field.k₀))) F.field.p
        (AffineSpace.coord (Spec (.of F.field.k₀)) PUnit.unit)) ≅
      Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of F.field.k₀)) F.field.p)) := by
  sorry

/-- The current degree-q line is the prime-degree summand, and is lisse of rank one;
its addition and inverse identities are in the adic common-stage category.
Source: Steps 2--5 (blueprint: sk-lem-as-properties).
Proof: apply lem-fd-as-characters at each finite quotient. The trace polynomial
sum_(j<r) y^(p^j) identifies the degree-q psi-eigenfunctions with the degree-p
Psi-eigenfunctions: they are exactly functions constant on the trace-kernel orbits.
These inverse maps commute with coefficient reductions and base change. Evaluation
at zero trivializes each integral summand. Complete, rationalize and include at E.
Transport lem-fd-as-lisse along this identification. Its multiplication of character
functions gives the tensor identity; setting g=-f gives the inverse. The zero function
has constant eigenfunctions and hence the unit sheaf, even for nontrivial characters. -/
theorem fourierCharacter_lisse_tensor_inverse (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsNoetherian X]
    [IsSeparated (X ↘ Spec (.of F.field.k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.field.k₀))]
    [QuasiCompact (X ↘ Spec (.of F.field.k₀))]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1) (f g : Γ(X, ⊤)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
      (fourierCompletedRealization F.coefficients.l (fourierCoefficient F) X
        (fourierEtaleCharacterOf F X Ψ f)) 1 ∧
    Nonempty (fourierCharacterOf F X Ψ f ≅ fourierPrimeObject F X Ψ f false) ∧
    Nonempty ((@commonStageDerivedTensor F.coefficients.l _ F.coefficients.Qbar _ _ _ X
      (fourierPropertyPrimeInvertible F (Over.mk (X ↘ Spec (.of F.field.k₀))))).obj
      (fourierCharacterOf F X Ψ f, fourierCharacterOf F X Ψ g) ≅
      fourierCharacterOf F X Ψ (f + g)) ∧
    Nonempty (fourierCharacterOf F X Ψ 0 ≅
      @pullbackTensorCommonUnit F.coefficients.l _ F.coefficients.Qbar _ _ _ X
        (fourierPropertyPrimeInvertible F (Over.mk (X ↘ Spec (.of F.field.k₀))))) ∧
    Nonempty ((@commonStageDerivedTensor F.coefficients.l _ F.coefficients.Qbar _ _ _ X
      (fourierPropertyPrimeInvertible F (Over.mk (X ↘ Spec (.of F.field.k₀))))).obj
      (fourierCharacterOf F X Ψ f, fourierCharacterOf F X Ψ (-f)) ≅
      @pullbackTensorCommonUnit F.coefficients.l _ F.coefficients.Qbar _ _ _ X
        (fourierPropertyPrimeInvertible F (Over.mk (X ↘ Spec (.of F.field.k₀))))) := by
  sorry

/-- The adic prime-cover pushforward is the direct sum of all character lines.
Source: Steps 2--3, lem-fd-as-characters (blueprint: sk-lem-as-properties).
Proof: the mutually orthogonal integral projectors p^-1 sum_a chi(-a)sigma_a sum
to the identity. Their images, inclusions and projections give a bilimit bicone.
All maps commute with coefficient quotients and realize the displayed adic splitting.
The nontrivial prime-field character parametrizes all characters by a in Fp.
Evaluation at zero gives rank one and the trivial summand is the constant line.
For f=0 the torsor is split, so every character summand is constant. -/
theorem fourierPrimeCharacters_decomposition (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsNoetherian X]
    [IsSeparated (X ↘ Spec (.of F.field.k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.field.k₀))]
    [QuasiCompact (X ↘ Spec (.of F.field.k₀))]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1) (f : Γ(X, ⊤)) :
    (∃ B : Bicone (fun a : ZMod F.field.p ↦
        fourierPrimeObject F X (Ψ.mulShift a) f false),
      Nonempty (Bicone.IsBilimit B) ∧ Nonempty (fourierPrimeObject F X Ψ f true ≅ B.pt)) ∧
    (∀ a : ZMod F.field.p, SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
      (fourierCompletedRealization F.coefficients.l (fourierCoefficient F) X
        (fourierPrimeEtaleCharacterOf F X (Ψ.mulShift a) f)) 1) ∧
    Nonempty (fourierPrimeObject F X (Ψ.mulShift 0) f false ≅
      @pullbackTensorCommonUnit F.coefficients.l _ F.coefficients.Qbar _ _ _ X
        (fourierPropertyPrimeInvertible F (Over.mk (X ↘ Spec (.of F.field.k₀))))) ∧
    (f = 0 → ∀ a : ZMod F.field.p, Nonempty (fourierPrimeObject F X (Ψ.mulShift a) f false ≅
      @pullbackTensorCommonUnit F.coefficients.l _ F.coefficients.Qbar _ _ _ X
        (fourierPropertyPrimeInvertible F (Over.mk (X ↘ Spec (.of F.field.k₀)))))) := by
  sorry

/-- Frobenius on the current degree-q sheaf for an arbitrary regular function,
including a zero value, is the specified trace-character scalar.
Source: Steps 6--7 and def-weil-local-frobenius-trace (blueprint: sk-lem-as-properties).
Proof: pull back the coordinate sheaf along f. Integral pullback composition and
lem-fix-weil-operations identify the iterated Weil map. Naturality of point transport
identifies the three-arrow local operator with the n-fold operator at f(u), even if
the degree of f(u) divides n properly. Apply lem-fd-as-trace to the coordinate sheaf
and transport along the degree-q/degree-p comparison defined over k0. Its stalk has
rank one in degree zero, so trace equals scalar. Expand finite-field traces as
Frobenius sums to obtain trace transitivity and the prime-field expression. -/
theorem fourierCharacter_closedFrobenius (F : FourierSetting.{u})
    (X₀ : Over (Spec (.of F.field.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] [IsNoetherian X₀.left]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (f : Γ(X₀.left, ⊤)) (y : {y : X₀.left // y ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField y.val →+* F.field.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap y.val) = algebraMap F.field.k₀ F.field.k) :
    localQbarClosedFrobeniusStalk F.coefficients.l F.coefficients.Qbar F.field
      F.coefficients.different X₀ (fourierCharacterWeil F X₀ Ψ f) y ι hι =
      fourierClosedCharacterValue F X₀ Ψ f y.val • 𝟙 _ ∧
    fourierClosedCharacterValue F X₀ Ψ f y.val = fourierClosedPrimeValue F X₀ Ψ f y.val := by
  sorry

/-- The standard line as an over-object inherits its finite-type structure.
Source: the line appearing in the unit (blueprint: sk-lem-as-properties). -/
instance fourierPropertyLine_finiteType (F : FourierSetting.{u}) :
    LocallyOfFiniteType (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
      Spec (.of F.field.k₀))).hom :=
  inferInstanceAs (LocallyOfFiniteType (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
    Spec (.of F.field.k₀)))

/-- Quasi-compactness of the affine-line structure morphism.
Source: the line appearing in the unit (blueprint: sk-lem-as-properties). -/
instance fourierPropertyLine_quasiCompact (F : FourierSetting.{u}) :
    QuasiCompact (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
      Spec (.of F.field.k₀))).hom :=
  inferInstanceAs (QuasiCompact (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
    Spec (.of F.field.k₀)))

/-- Separatedness inherited by the standard affine-line model.
Source: standing Fourier setting (blueprint: sk-lem-as-properties). -/
instance fourierPropertyLine_separated (F : FourierSetting.{u}) :
    IsSeparated (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
      Spec (.of F.field.k₀))).hom :=
  inferInstanceAs (IsSeparated (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
    Spec (.of F.field.k₀)))

/-- Noetherianity follows from the given finite-type model; it is not an extra
condition on the affine line. Source: standing Fourier setting
(blueprint: sk-lem-as-properties). -/
instance fourierPropertyLine_noetherian (F : FourierSetting.{u}) :
    IsNoetherian (AffineSpace PUnit (Spec (.of F.field.k₀))) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
    (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀))
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀))

/-- Noetherianity on the bundled line is the inherited instance on its source.
Source: standing affine-line geometry (blueprint: sk-lem-as-properties). -/
instance fourierPropertyLineModel_noetherian (F : FourierSetting.{u}) :
    IsNoetherian (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
      Spec (.of F.field.k₀))).left :=
  inferInstanceAs (IsNoetherian (AffineSpace PUnit (Spec (.of F.field.k₀))))

/-- The trace function of the linear character, for every parameter including zero.
Source: the displayed trace-function clause and Step 7 (blueprint: sk-lem-as-properties).
Proof: apply the arbitrary-function closed-point scalar formula to f=ax. At a point
of F_(q^n), the n-fold operator is the power corresponding to its actual closed-point
degree. Iterating the scalar and applying trace transitivity gives psi(Tr(a*x)).
The complex is a line in degree zero, so its alternating trace is this scalar. -/
theorem fourierCharacter_linear_trace (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (a : F.field.k₀) (n : ℕ) (hn : 1 ≤ n)
    (x : F.field.extensionPoints
      (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀))) n hn) :
    weilTraceFunction F.field F.coefficients.l F.coefficients.different F.coefficients.Qbar
      (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀)))
      (fourierCharacterWeil F
        (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀))) Ψ
        (artinSchreierBaseConstants F.field.k₀ _ a *
          AffineSpace.coord (Spec (.of F.field.k₀)) PUnit.unit)) n hn x =
      Ψ (@Algebra.trace (ZMod F.field.p) (F.field.extensionSubfield n hn) _ _
        (((F.field.extensionEmbedding n hn).comp
          (@algebraMap (ZMod F.field.p) F.field.k₀ _ _ (fourierPrimeAlgebra F))).toAlgebra)
        ((F.field.extensionEmbedding n hn) a *
          (Scheme.ΓSpecIso (.of _)).hom.hom
            (x.left.appTop (AffineSpace.coord (Spec (.of F.field.k₀)) PUnit.unit)))) := by
  sorry

/-- Ordinary cohomology of every linear character on the geometric affine line,
including the zero parameter, and the separate constant-coefficient assertion.
Source: Step 8 (blueprint: sk-lem-as-properties).
Proof: lem-fd-cohomology-affine-line-character computes the prime-degree character
at finite coefficient levels. Steps 4--5 identify it with the current degree-q
sheaf, compatibly with reduction. Finite-etale adic cohomology realizes this result
in ordinary adic cohomology. For a=0 use lem-fd-affine-line-constant-cohomology;
its H0 isomorphism is induced by constant sections. All degrees here are nonnegative. -/
theorem fourierCharacter_affine_cohomology (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    :
    (∀ (a : F.field.k₀) (i : ℕ), i ≠ 0 ∨ a ≠ 0 →
      IsZero (fourierCharacterCohomology F (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
          Spec (.of F.field.k₀)))
        (fourierCharacterWeil F (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
          Spec (.of F.field.k₀))) Ψ
          (artinSchreierBaseConstants F.field.k₀ _ a *
            AffineSpace.coord (Spec (.of F.field.k₀)) PUnit.unit)).carrier i)) ∧
    Nonempty (fourierCharacterCohomology F (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
          Spec (.of F.field.k₀)))
      (@pullbackTensorCommonUnit F.coefficients.l _ F.coefficients.Qbar _ _ _
        (F.field.geometricFiber (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
          Spec (.of F.field.k₀)))).left
        (sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different _)) 0 ≅
      ModuleCat.of F.coefficients.Qbar (ULift.{u + 2} F.coefficients.Qbar)) ∧
    (∀ i : ℕ, 0 < i → IsZero (fourierCharacterCohomology F
      (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀)))
      (@pullbackTensorCommonUnit F.coefficients.l _ F.coefficients.Qbar _ _ _
        (F.field.geometricFiber (Over.mk (AffineSpace PUnit (Spec (.of F.field.k₀)) ↘
          Spec (.of F.field.k₀)))).left
        (sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different _)) i)) := by
  sorry

end WeilConjectures
