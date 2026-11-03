/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.CoefficientHeartIntegralMorphismCharts
import WeilConjectures.AlgebraicGeometry.CoefficientHeartRationalizedTowerKernels
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import all WeilConjectures.AlgebraicGeometry.LisseFiniteDescent
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-!
# Constructible coefficient sheaves over finite or algebraically closed fields

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3), with the standing finite-or-algebraically-closed base-field
convention of `part-six-operations/prose-P1-01.md` (blueprint: sk-lem-coefficient-heart).

The coefficient ring is the condensed ring pulled back from the point.  The statement
uses the existing constructible full subcategory, the existing lisse predicate, and the
canonical locally closed extension from the dependency nodes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Kernel and cokernel closure over a finite extension, with the specified
rational morphism identified on each integral chart. -/
private theorem heartFiniteKernels (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) (f : M ⟶ N)
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) M)
    (hN : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) N) :
    IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) (kernel f) ∧
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) (cokernel f) := by
  obtain ⟨C, hC⟩ := coefficientHeart_integralMorphismCharts ℓ E X M N f hM hN
  have hlocal (i : C.I₀) :
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1)
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) (C.f i)).obj
          (kernel f)) ∧
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1)
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) (C.f i)).obj
          (cokernel f)) := by
    obtain ⟨ha, hn, hc, P, Q, g, hP, hQ, eP, eQ, hs⟩ := hC i
    have := ha
    have := hn
    have := hc
    let H := CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) (C.f i)
    let T := Mod.extendScalars (padicIntegersToPadicSubfield (C.X i) ℓ E)
    have h := coefficientHeart_rationalizedTowerKernels ℓ E (C.X i) P Q g hP hQ
    exact ⟨CondensedRing.locFree_iso (PreservesKernel.iso H f)
        (CondensedRing.locFree_iso (kernel.mapIso (T.map g) (H.map f) eP eQ hs).symm h.1),
      CondensedRing.locFree_iso (PreservesCokernel.iso H f)
        (CondensedRing.locFree_iso (cokernel.mapIso (T.map g) (H.map f) eP eQ hs).symm h.2)⟩
  exact ⟨CondensedRing.locFree_of_cover _ C (fun i ↦ (hlocal i).1),
    CondensedRing.locFree_of_cover _ C (fun i ↦ (hlocal i).2)⟩

/-- Finite descent of the specified arrow, followed by the canonical kernel and
cokernel comparisons of the exact scalar extension. -/
private theorem heartAlgClKernels (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (f : M ⟶ N)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) M)
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) N) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) (kernel f) ∧
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) (cokernel f) := by
  classical
  let F := Paths.lift (parallelPair f f).toPrefunctor
  have hF : ∀ a : Paths WalkingParallelPair,
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) (F.obj a) := by
    intro a
    cases a
    · exact hM
    · exact hN
  let s : Fin 0 → Paths WalkingParallelPair := Fin.elim0
  let p : ∀ r : Fin 0, FreeAbelianGroup (s r ⟶ s r) := fun r ↦ r.elim0
  obtain ⟨E, G, hG, ⟨e⟩, _⟩ := lisse_finite_descent X ℓ WalkingParallelPair
    F hF (Fin 0) s s p p (fun r ↦ r.elim0)
  let U := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)
  let g := G.map ((Paths.of WalkingParallelPair).map WalkingParallelPairHom.left)
  have hg := heartFiniteKernels ℓ E X (G.obj WalkingParallelPair.zero)
    (G.obj WalkingParallelPair.one) g (hG _) (hG _)
  let eM : U.obj (G.obj WalkingParallelPair.zero) ≅ M := e.app WalkingParallelPair.zero
  let eN : U.obj (G.obj WalkingParallelPair.one) ≅ N := e.app WalkingParallelPair.one
  have hs : U.map g ≫ eN.hom = eM.hom ≫ f := by
    have hn := e.hom.naturality
      ((Paths.of WalkingParallelPair).map WalkingParallelPairHom.left)
    change U.map g ≫ eN.hom = eM.hom ≫
      F.map ((Paths.of WalkingParallelPair).map WalkingParallelPairHom.left) at hn
    simpa [F, Paths.lift_toPath, Functor.toPrefunctor] using hn
  have hK := lisse_coefficient_extend (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    (kernel g) hg.1
  have hQ := lisse_coefficient_extend (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    (cokernel g) hg.2
  exact ⟨CondensedRing.locFree_iso
      ((PreservesKernel.iso U g) ≪≫ kernel.mapIso (U.map g) f eM eN hs).symm hK,
    CondensedRing.locFree_iso
      ((PreservesCokernel.iso U g) ≪≫ cokernel.mapIso (U.map g) f eM eN hs).symm hQ⟩

/-- Local basis lifts split an extension of lisse modules. This argument works
for any commutative condensed ring. -/
private theorem heartLisseExtension
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (X : Scheme.{u})
    (Q : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj A X))) (hQ : Q.ShortExact)
    (h₁ : IsLisseCoefficientModule A Q.X₁) (h₃ : IsLisseCoefficientModule A Q.X₃) :
    IsLisseCoefficientModule A Q.X₂ := by
  classical
  have raw (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
      (h : IsLisseCoefficientModule A M) :
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f i)).obj (condensedRingObj A X))
          (((upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj A X)).obj M) := by
    obtain ⟨C, hC⟩ := h
    refine ⟨C, fun i ↦ ?_⟩
    let a := condensedPullbackHom A (C.f i)
    let F := (upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj A X)
    exact free_of_comap (inv a) (free_of_iso (hC i)
      ((Mod.extendScalarsIsoComapInv a).app (F.obj M)))
  have : Epi Q.g := hQ.epi_g
  obtain ⟨C, hC⟩ := common_free_cover (raw _ h₁) (raw _ h₃)
  have hv (i : C.I₀) := freeEpiLocalSplitting (C.X i) _ _ _
    (((upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj A X)).map Q.g) (hC i).2
  choose V hV using hv
  apply heart_lisse_of_free A
  refine ⟨C.bind V, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  let F := (upperStar Ab.{u + 1} (C.f i)).mapMod (condensedRingObj A X)
  let G := (upperStar Ab.{u + 1} ((V i).f j)).mapMod
    ((upperStar Ab.{u + 1} (C.f i)).obj (condensedRingObj A X))
  have : IsSplitEpi (G.map (F.map Q.g)) := hV i j
  have hQ' := hQ.map_of_exact (F ⋙ G)
  let t := ShortComplex.Splitting.ofExactOfSection (Q.map (F ⋙ G)) hQ'.exact
    (section_ (G.map (F.map Q.g))) (IsSplitEpi.id _) hQ'.mono_f
  apply (free_pullback_comp_iff ((V i).f j) (C.f i) Q.X₂).mpr
  exact free_of_iso (free_biprod (free_pullback ((V i).f j) (hC i).1)
    (free_pullback ((V i).f j) (hC i).2)) t.isoBinaryBiproduct.symm

/-- The finite constant local models are lisse on each stratum; conversely a
finite free chart is pulled back from its finite free scalar model. -/
private theorem heartStrata (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) X)) :
    IsConstantModelConstructible (coefficientHeartRingObj L) X M ↔
      ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
        IsLisseCoefficientModule (coefficientHeartRingObj L)
          ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj M) := by
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  constructor
  · intro h
    obtain ⟨R, hR⟩ := (heart_strata (fun Y f ↦
      HasFiniteConstantLocalModel (coefficientHeartRingObj L) Y
        ((CondensedRing.upperStar (coefficientHeartRingObj L) f).obj M))).mp h
    exact ⟨R, (coefficientHeart_commonStratification ℓ L X hL).2.1.2 R R M hR
      (fun a ↦ ⟨a, Set.Subset.rfl⟩)⟩
  · rintro ⟨R, hR⟩
    apply (heart_strata (fun Y f ↦
      HasFiniteConstantLocalModel (coefficientHeartRingObj L) Y
        ((CondensedRing.upperStar (coefficientHeartRingObj L) f).obj M))).mpr
    exact ⟨R, fun a ↦ heart_free_model (coefficientHeartRingObj L) _ (hR a)⟩

/-- Simultaneously adapt two constructible objects and retain their lisse restrictions. -/
private theorem heartCommonLisse (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) X))
    (hM : IsConstantModelConstructible (coefficientHeartRingObj L) X M)
    (hN : IsConstantModelConstructible (coefficientHeartRingObj L) X N) :
    ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
      IsLisseCoefficientModule (coefficientHeartRingObj L)
        ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj M) ∧
      IsLisseCoefficientModule (coefficientHeartRingObj L)
        ((CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj N) := by
  obtain ⟨S, hS⟩ := (heartStrata ℓ L hL X M).mp hM
  obtain ⟨T, hT⟩ := (heartStrata ℓ L hL X N).mp hN
  let D : Fin 2 → X.FiniteLocallyClosedStratification := ![S, T]
  have h := coefficientHeart_commonStratification ℓ L X hL
  obtain ⟨R, hR, _⟩ := h.1 2 D
  refine ⟨R, fun a ↦ ⟨?_, ?_⟩⟩
  · exact h.2.1.2 S R M
      (fun a ↦ heart_free_model (coefficientHeartRingObj L) _ (hS a)) (hR 0) a
  · exact h.2.1.2 T R N
      (fun a ↦ heart_free_model (coefficientHeartRingObj L) _ (hT a)) (hR 1) a

/-- Restriction to adapted strata transfers the lisse closure results to Cons. -/
private theorem heartClosure (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsNoetherian X] :
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (coefficientHeartRingObj L) X) := by
  have hk (Y : Scheme.{u}) [IsNoetherian Y]
      (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj L) Y)) (f : M ⟶ N)
      (hM : IsLisseCoefficientModule (coefficientHeartRingObj L) M)
      (hN : IsLisseCoefficientModule (coefficientHeartRingObj L) N) :
      IsLisseCoefficientModule (coefficientHeartRingObj L) (kernel f) ∧
        IsLisseCoefficientModule (coefficientHeartRingObj L) (cokernel f) := by
    rcases hL with ⟨E, hE, rfl⟩ | rfl
    · exact heartFiniteKernels ℓ ⟨E, hE⟩ Y M N f hM hN
    · exact heartAlgClKernels ℓ Y M N f hM hN
  let P : ObjectProperty _ := IsConstantModelConstructible (coefficientHeartRingObj L) X
  have hi : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (coefficientHeartRingObj L) X).1
  have hstratum (R : X.FiniteLocallyClosedStratification) (a : Fin R.n) :
      IsNoetherian (R.domain a) := by
    have : IsImmersion (R.immersion a) := R.isImmersion a
    have : IsLocallyNoetherian (R.domain a) :=
      LocallyOfFiniteType.isLocallyNoetherian (R.immersion a)
    have : TopologicalSpace.NoetherianSpace (R.domain a) :=
      (R.immersion a).isEmbedding.isInducing.noetherianSpace
    exact ⟨⟩
  have hkc (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj L) X)) (f : M ⟶ N)
      (hM : P M) (hN : P N) : P (kernel f) ∧ P (cokernel f) := by
    obtain ⟨R, hR⟩ := heartCommonLisse ℓ L hL X M N hM hN
    constructor
    · apply (heartStrata ℓ L hL X _).mpr
      refine ⟨R, fun a ↦ ?_⟩
      have := hstratum R a
      let F := CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)
      exact CondensedRing.locFree_iso (PreservesKernel.iso F f)
        (hk (R.domain a) (F.obj M) (F.obj N) (F.map f) (hR a).1 (hR a).2).1
    · apply (heartStrata ℓ L hL X _).mpr
      refine ⟨R, fun a ↦ ?_⟩
      have := hstratum R a
      let F := CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)
      exact CondensedRing.locFree_iso (PreservesCokernel.iso F f)
        (hk (R.domain a) (F.obj M) (F.obj N) (F.map f) (hR a).1 (hR a).2).2
  obtain ⟨he, hk, hc⟩ := heart_closure_classes P
    (fun e h ↦ P.prop_of_iso e h) (fun f hM hN ↦ (hkc _ _ f hM hN).1)
    (fun f hM hN ↦ (hkc _ _ f hM hN).2) (by
      intro Q hQ h₁ h₃
      obtain ⟨R, hR⟩ := heartCommonLisse ℓ L hL X Q.X₁ Q.X₃ h₁ h₃
      apply (heartStrata ℓ L hL X _).mpr
      refine ⟨R, fun a ↦ ?_⟩
      let F := CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)
      exact heartLisseExtension (coefficientHeartRingObj L) (R.domain a)
        (Q.map F) (hQ.map_of_exact F) (hR a).1 (hR a).2)
  exact ⟨hk, hc, he⟩

/-- Keep the counit-image subobjects abstract while assembling their quotients. -/
private def heartImage
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
    (V : Y.Opens) : Subobject M := imageSubobject (coefficientHeartOpenCounit A M V)

private theorem heartImage_eq
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
    (V : Y.Opens) : heartImage A M V = coefficientHeartFiltrationStep A M V := rfl

attribute [local irreducible] heartImage
  CondensedRing.upperStarLowerStarAdjunction coefficientHeartLocallyClosedExtension
  CondensedRing.openImmersionLowerShriekUpperStarAdjunction Subobject.ofLE Subobject.mk
  CondensedRing.openImmersionLowerShriek CondensedRing.lowerStar
  _root_.DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

/-- Constructible coefficient sheaves form an exact essentially small abelian heart and
admit finite filtrations by canonical locally closed extensions of lisse sheaves,
over a finite or algebraically closed field of characteristic different from `ℓ`.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3), and
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/`
`sk-lem-coefficient-heart.proof.md`,
steps (1)--(3)
(blueprint: sk-lem-coefficient-heart).

The closure conjuncts render clause (1)'s closure under kernels, cokernels and extensions.
The `Abelian` witness and finite-limit/finite-colimit preservation render its abelian and
exact-inclusion conclusions.  The `EssentiallySmall` conjunct is clause (2).  The final
conjunct is clause (3): its filtration terms are subobjects, successive quotients are
cokernels of the inclusions, and each quotient is the canonical `a_!` of a lisse module.

Proof plan, following the node's eight steps:
1. Finite type over k makes X Noetherian. Finite scalar presentations are finite free;
   choose common adapted strata and use exact restriction to check closure on strata.
2. For extensions, trivialize the ends and locally lift the quotient basis. The resulting
   local splitting identifies the middle term with a finite free direct sum.
3. Over E use the lattice atlas on connected affine etale neighborhoods. The qcqs
   finitely presented Hom/filtered-colimit calculation clears one common denominator.
4. Recover the lattices as limits of their finite reductions. The connected pro-etale
   tower identifies the map with its completed-fibre matrix, whose kernel and cokernel
   become finite free after inverting the uniformizer and choosing linear algebra bases.
5. Over Qbar_l descend the two lisse objects and their map to a finite E. Flat scalar
   extension preserves kernels, and the left adjoint preserves cokernels. Return to strata.
6. Zero has rank zero and extensions give finite sums. Closure under ambient kernels and
   cokernels gives the abelian full subcategory and its exact inclusion.
7. In the fixed universe encode finite stratifications and finite-rank descent/gluing
   data by a set of representatives, giving essential smallness.
8. Refine to ordered open prefixes. Their open-extension counit images form a filtration
   from zero to F, with quotients the canonical locally closed extensions of lisse
   restrictions. Repeated terms, rank zero and empty schemes are allowed.
-/
theorem coefficientHeartFiniteOrAlgebraicallyClosed (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      EssentiallySmall.{u + 1} (ConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      @CoefficientHeartFiltrationAssertions (coefficientHeartRingObj Λ) _ _ X
        { toIsLocallyNoetherian :=
            LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
          toCompactSpace :=
            QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  classical
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  let P : ObjectProperty _ := IsConstantModelConstructible (coefficientHeartRingObj Λ) X
  obtain ⟨hk, hc, he⟩ := heartClosure ℓ Λ hΛ X
  have : P.IsClosedUnderKernels := hk
  have : P.IsClosedUnderCokernels := hc
  have : P.IsClosedUnderExtensions := he
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (coefficientHeartRingObj Λ) X).1
  have : P.ContainsZero := by
    obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X))).zero
    refine ⟨⟨Z, hZ, ?_⟩⟩
    apply (heartStrata ℓ Λ hΛ X Z).mpr
    let S : X.FiniteLocallyClosedStratification :=
      { n := 1
        stratum := fun _ ↦ Set.univ
        isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
        iUnion_stratum_eq_univ := Set.iUnion_const _
        pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
        domain := fun _ ↦ X
        immersion := fun _ ↦ 𝟙 X
        isImmersion := fun _ ↦ inferInstance
        range_immersion := fun _ ↦ Set.range_id' }
    refine ⟨S, fun a ↦ ?_⟩
    let F := CondensedRing.upperStar (coefficientHeartRingObj Λ) (S.immersion a)
    apply heart_lisse_of_free (coefficientHeartRingObj Λ)
    let C : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
      .singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _)
    refine ⟨C, fun i ↦ ?_⟩
    let G := (upperStar Ab.{u + 1} (C.f i)).mapMod
      (condensedRingObj (coefficientHeartRingObj Λ) X)
    have hzero : IsZero (Mod.finiteFree
        ((upperStar Ab.{u + 1} (C.f i)).obj (condensedRingObj (coefficientHeartRingObj Λ) X))
        0) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply biproduct.hom_ext
      intro a
      exact a.elim0
    exact ⟨0, ⟨(G.map_isZero (F.map_isZero hZ)).iso hzero⟩⟩
  obtain ⟨hab, hlim, hcolim⟩ := heart_abelian P
  refine ⟨hk, hc, he, hab, hlim, hcolim,
    coefficientHeart_essentiallySmall ℓ Λ hΛ X, ?_⟩
  intro F
  obtain ⟨S, hS⟩ := (heartStrata ℓ Λ hΛ X F.obj).mp F.property
  have hcommon := coefficientHeart_commonStratification ℓ Λ X hΛ
  obtain ⟨R, hRall⟩ := hcommon.1 1 (fun _ ↦ S)
  have hR := hRall.1
  have hopen := hRall.2.2
  have hRfree := hcommon.2.1.2 S R F.obj
    (fun a ↦ heart_free_model (coefficientHeartRingObj Λ) _ (hS a)) (hR 0)
  let V (a : Fin (R.n + 1)) : X.Opens := ⟨_, hopen a⟩
  have hfil := coefficientHeart_filtration ℓ Λ hΛ X F.obj F.property R
    (fun a ↦ heart_free_model (coefficientHeartRingObj Λ) _ (hRfree a)) V (fun _ ↦ rfl)
  simp only [← heartImage_eq] at hfil
  obtain ⟨h, hquot⟩ := hfil.2.2.2
  refine ⟨R.n, fun a ↦ heartImage (coefficientHeartRingObj Λ) F.obj (V a),
    hfil.2.1, hfil.2.2.1, h, fun a ↦ ?_⟩
  exact ⟨R.domain a, R.immersion a, R.isImmersion a,
    (CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a)).obj F.obj,
    (hquot a).2, (hquot a).1⟩

end AlgebraicGeometry.ProEtale
