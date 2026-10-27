/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.NodalDualizingDatum
public import Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees
public import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.TraceFormula.SmoothCurveSectionCartier
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Logarithmic section algebras and elementary stabilization

Source: Knudsen, The projectivity of the moduli space of stable curves II (1983),
Theorem 1.8, Corollaries 1.9 and 1.11, and Proposition 2.1, pp. 172--175
(blueprint: lem-sfb-log-canonical-deletion-algebra).

All auxiliary predicates unpack clauses of this single theorem. The marking ideal is
constructed from the finite disjoint-union map. Section algebras, evaluation and relative
Proj use the existing canonical interfaces; no contraction map is assumed as input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The map from the disjoint union of labelled markings, including the empty union.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def nodalDeletionMarking {Y T : Scheme.{u}} {r : ℕ} (a : Fin r → (T ⟶ Y)) :
    (∐ fun _ : Fin r ↦ T) ⟶ Y := Sigma.desc a

/-- The logarithmic line, using the dual of the actual marking ideal.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def nodalDeletionLine {Y T : Scheme.{u}} {r : ℕ} (a : Fin r → (T ⟶ Y))
    (omega : Y.Modules) : Y.Modules :=
  omega ⊗ₘ (nodalDeletionMarking a).ker.toModulesᵛ

/-- Cohomological degree on the canonical normalization of a geometric component.
Source: Knudsen II, Theorem 1.8 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def nodalDeletionDegree {Y T : Scheme.{u}} (f : Y ⟶ T) (L : Y.Modules)
    (Ω : Type u) [Field Ω] (t : Spec (.of Ω) ⟶ T)
    (Z : irreducibleComponents (pullback (C := Scheme.{u}) f t)) : ℤ :=
  markedNodalComponentDegree Ω ((pullback f t).reducedNormalizationComponent Z)
    ((Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫ pullback.fst f t)
    ((Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫ pullback.snd f t) L

/-- The geometric component conditions, with the two branches of a self-node counted
separately on its normalization. Smooth genus-zero components over the algebraically
closed geometric field are precisely smooth rational components.
Source: Knudsen II, Theorem 1.8 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def NodalDeletionNumerics {Y T : Scheme.{u}} (f : Y ⟶ T)
    [LocallyOfFinitePresentation f] {r : ℕ}
    (a : Fin r → (T ⟶ Y)) (ha : ∀ i, a i ≫ f = 𝟙 T) (L : Y.Modules) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
    (∀ Z, 0 ≤ nodalDeletionDegree f L Ω t Z) ∧
    Set.Subsingleton {Z | nodalDeletionDegree f L Ω t Z = 0} ∧
    ∀ Z, nodalDeletionDegree f L Ω t Z = 0 →
      Smooth ((Scheme.IdealSheafData.vanishingIdeal
        ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫ pullback.snd f t) ∧
      (pullback f t).normalizedComponentGenus (pullback.snd f t) Z = 0 ∧
      ((pullback f t).normalizedComponentMap Z ⁻¹'
        ({x | x ∉ (pullback.snd f t).smoothLocus} ∪
          ⋃ i : Fin r, Set.range (f.baseChangeSection (a i) (ha i) t))).encard = 2

/-- The induced map on geometric fibres, using the given equation over the base.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def nodalDeletionFibreMap {Y X T : Scheme.{u}} (f : Y ⟶ T) (p : X ⟶ T)
    (q : Y ⟶ X) (hq : q ≫ p = f) (Ω : Type u) [Field Ω]
    (t : Spec (.of Ω) ⟶ T) : pullback f t ⟶ pullback p t :=
  pullback.map f t p t q (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hq.symm) (by simp)

/-- The exact fibrewise contraction requirement. A zero-degree component maps as a scheme
to a rational point, and the complements are isomorphic. If there is no such component,
the whole fibre map is an isomorphism.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def NodalDeletionContracts {Y X T : Scheme.{u}} (f : Y ⟶ T) (L : Y.Modules)
    (p : X ⟶ T) (q : Y ⟶ X) (hq : q ≫ p = f) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
    (∀ Z, nodalDeletionDegree f L Ω t Z = 0 →
      ∃ z : Spec (.of Ω) ⟶ pullback p t,
        z ≫ pullback.snd p t = 𝟙 _ ∧
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
            nodalDeletionFibreMap f p q hq Ω t =
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι ≫
              pullback.snd f t) ≫ z ∧
        ∃ (U : (pullback f t).Opens) (V : (pullback p t).Opens)
          (e : U.toScheme ≅ V.toScheme),
          (U : Set ↥(pullback (C := Scheme.{u}) f t)) = Z.1ᶜ ∧
          (V : Set ↥(pullback (C := Scheme.{u}) p t)) = (Set.range z)ᶜ ∧
          U.ι ≫ nodalDeletionFibreMap f p q hq Ω t = e.hom ≫ V.ι) ∧
    ((∀ Z, nodalDeletionDegree f L Ω t Z ≠ 0) →
      IsIso (nodalDeletionFibreMap f p q hq Ω t))

/-- Pull back an actual homogeneous section and restrict to the specified base chart.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def nodalDeletionBaseChangeSection {Y T T' : Scheme.{u}} (f : Y ⟶ T) (u : T' ⟶ T)
    (M : Y.Modules) (V : T.affineOpens) (W : T'.affineOpens)
    (h : W.1 ≤ u ⁻¹ᵁ V.1) (n : ℕ) (s : Γ(M.tensorPow n, f ⁻¹ᵁ V.1)) :
    Γ(((Scheme.Modules.tensorPullback (pullback.fst f u)).obj M).tensorPow n,
      pullback.snd f u ⁻¹ᵁ W.1) :=
  (((Scheme.Modules.tensorPullback (pullback.fst f u)).obj M).tensorPow n).presheaf.map
    (homOfLE (by
      intro x hx
      change f (pullback.fst f u x) ∈ V.1
      rw [← Scheme.Hom.comp_apply, pullback.condition]
      exact h hx)).op
    ((Scheme.Modules.boundaryPullbackPowIso (pullback.fst f u) M n).hom.app
      (pullback.fst f u ⁻¹ᵁ (f ⁻¹ᵁ V.1))
      (Scheme.Modules.tensorPullbackSection (pullback.fst f u)
        (M.tensorPow n) (f ⁻¹ᵁ V.1) s))

/-- Arbitrary base change of the algebra and evaluation. The graded coefficient maps are
specified on every section, including degree zero, by actual pullback. The relative-Proj
comparison of this PullbackData is cartesian by its existing construction.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def NodalDeletionBaseChange {Y T : Scheme.{u}} (f : Y ⟶ T) (M : Y.Modules)
    (A : Scheme.Modules.RelativeSectionAlgebra f M) (q : Y ⟶ A.data.relProj) : Prop :=
  ∀ (T' : Scheme.{u}) (u : T' ⟶ T),
    ∃ (B : Scheme.Modules.RelativeSectionAlgebra (pullback.snd f u)
        ((Scheme.Modules.tensorPullback (pullback.fst f u)).obj M))
      (b : Scheme.GradedAlgebraData.PullbackData u A.data B.data)
      (q' : pullback f u ⟶ B.data.relProj),
      B.IsCanonicalMap q' ∧ q' ≫ b.relProjComparison = pullback.fst f u ≫ q ∧
      ∀ (V : T.affineOpens) (W : T'.affineOpens) (h : W.1 ≤ u ⁻¹ᵁ V.1)
        (n : ℕ) (s : A.data.grading V n),
        B.sectionEquiv W n ⟨b.map h s, (b.map h).map_mem s.property⟩ =
          nodalDeletionBaseChangeSection f u M V W h n (A.sectionEquiv V n s)

/-- Naturality under every isomorphism preserving the individual labels. The section
formula fixes the graded isomorphism; its Proj isomorphism commutes with evaluation.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def NodalDeletionIsomorphisms {Y T : Scheme.{u}} (f : Y ⟶ T) {r : ℕ}
    (a : Fin r → (T ⟶ Y)) (M : Y.Modules)
    (A : Scheme.Modules.RelativeSectionAlgebra f M) (q : Y ⟶ A.data.relProj) : Prop :=
  ∀ (Y' : Scheme.{u}) (f' : Y' ⟶ T) (a' : Fin r → (T ⟶ Y'))
    (e : Y' ≅ Y) (he : e.hom ≫ f = f'),
    (∀ i, a' i ≫ e.hom = a i) →
    ∃ (B : Scheme.Modules.RelativeSectionAlgebra f'
        ((Scheme.Modules.tensorPullback e.hom).obj M))
      (b : A.data ≅ B.data) (q' : Y' ⟶ B.data.relProj),
      B.IsCanonicalMap q' ∧
      q' ≫ (Scheme.GradedAlgebraData.relProjIsoOfIso b).hom = e.hom ≫ q ∧
      ∀ (V : T.affineOpens) (n : ℕ) (s : A.data.grading V n),
        (((Scheme.Modules.tensorPullback e.hom).obj M).tensorPow n).presheaf.map
          (eqToHom (congrArg (fun k : Y' ⟶ T ↦ k ⁻¹ᵁ V.1) he)).op
          (B.sectionEquiv V n ⟨b.hom.app V s, (b.hom.app V).map_mem s.property⟩) =
        (Scheme.Modules.boundaryPullbackPowIso e.hom M n).hom.app
          (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V.1))
          (Scheme.Modules.tensorPullbackSection e.hom (M.tensorPow n)
            (f ⁻¹ᵁ V.1) (A.sectionEquiv V n s))

/-- The closed embedding induced by the degree-one section quotient. Its symmetric
algebra map is fixed on each generator by the actual section equivalence; its relative
Proj map is therefore the embedding associated to cubic evaluation.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def NodalDeletionProjectiveEmbedding {Y T : Scheme.{u}} (f : Y ⟶ T) (M : Y.Modules)
    (A : Scheme.Modules.RelativeSectionAlgebra f M) : Prop :=
  ∃ hqc : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent,
    ∃ phi : (@SymmetricAlgebraSheaf.gradedAlgebraData T
        ((Scheme.Modules.pushforward f).obj M) hqc) ⟶ A.data,
      (∀ (V : T.affineOpens) (s : A.data.grading V 1),
        phi.app V (SymmetricAlgebra.ι Γ(T, V.1)
          (((Scheme.Modules.pushforward f).obj M).val.obj (op V.1))
          ((ρ_ M).hom.app (f ⁻¹ᵁ V.1) (A.sectionEquiv V 1 s))) = s.val) ∧
      ∃ hsurj : ∀ V : T.affineOpens, Function.Surjective (phi.app V),
        IsClosedImmersion (Scheme.GradedAlgebraData.relProjMap phi
          (Scheme.GradedAlgebraData.irrelevantLE_of_surjective phi hsurj))

/-- The adjunction-normalized line and its marking twist under a labelled isomorphism.
The fundamental-class formula fixes the dualizing comparison, and the twist is the dual
of the actual marking ideal, just as under base change.
Source: Knudsen II, Proposition 2.1 (blueprint: lem-sfb-log-canonical-deletion-algebra). -/
def NodalDeletionDualizingIsomorphisms {Y T : Scheme.{u}} (f : Y ⟶ T) {r : ℕ}
    (a : Fin r → (T ⟶ Y)) (omega : Y.Modules) (d : NodalDualizingDatum f omega) : Prop :=
  ∀ (Y' : Scheme.{u}) (f' : Y' ⟶ T) (a' : Fin r → (T ⟶ Y'))
    (e : Y' ≅ Y), e.hom ≫ f = f' → (∀ i, a' i ≫ e.hom = a i) →
    ∃ d' : NodalDualizingDatum f' ((Scheme.Modules.tensorPullback e.hom).obj omega),
      (∀ (U : Y.Opens) (s : Γ(Y, U)),
        ((Scheme.Modules.tensorPullback e.hom).map d.fundamental).app (e.hom ⁻¹ᵁ U)
          (f.relativeDifferentialsPullbackGenerator e.hom U s) =
        d'.fundamental.app (e.hom ⁻¹ᵁ U)
          (f'.relativeDifferentialsDerivation.d (X := op (e.hom ⁻¹ᵁ U)) (e.hom.app U s))) ∧
      Nonempty ((Scheme.Modules.tensorPullback e.hom).obj (nodalDeletionLine a omega) ≅
        nodalDeletionLine a' ((Scheme.Modules.tensorPullback e.hom).obj omega))

/-- The logarithmic section algebra contracts the possible single degree-zero component.
The canonical dualizing datum is supplied first; the numerical assumptions concern its
marking twist. No assumption on the base beyond being a scheme is imposed.

Source: Knudsen II, Theorem 1.8, Corollaries 1.9 and 1.11, Proposition 2.1, pp. 172--175
(blueprint: lem-sfb-log-canonical-deletion-algebra).

Proof, following the node's twelve steps:
1. Proper nodal dualizing base change gives the Jacobian-normalized adjunction line.
   Separated sections are closed and smooth curve sections are Cartier. Their disjoint
   union gives the Cartier sum, with the unit ideal for no markings. Relative Cartier
   pullback and dualizing base change identify the logarithmic line after any base change.
2. Nodal normalization adjunction gives degree 2g(V)-2 plus the node branches.
   The effective-divisor degree formula adds the markings, counting both self-node branches.
3. On a geometric fibre, a possible exceptional component is a rational tail or bridge.
   Pinch its one or two boundary points on the reduced complement, and use the closed-union
   pushout to glue the constant exceptional map. The quotient is proper and nodal.
4. Elementary nodal contraction direct image preserves H1(O) and the logarithmic line.
   A tail replaces one branch by a marking; a bridge replaces two branches by a node.
   Thus remaining logarithmic degrees stay positive and the resulting markings are stable.
5. Stable-pointed field linear series gives acyclicity for m>=2 and very ampleness and
   normal generation for the cubic. Contraction direct image transfers these to the source.
6. Perfect direct image and arbitrary derived base change, followed by the degree-zero
   perfect locus on a bounded finite-free representative, give finite local freeness and
   canonical ordinary base change for every m>=2, over an arbitrary base.
7. Proper flat connected reduced fibres give A0=O universally. Fibrewise generation and
   Nakayama on finite cokernels give surjective cubic evaluation and degree-one generation.
8. The relative-section-image flat-fp lemma identifies Proj with the scheme-theoretic image,
   flat and finitely presented and closed in the projective bundle of the cubic direct image.
   Its geometric maps are the explicit contractions above. The fibre smoothness criterion
   gives disjoint smooth image markings and the stable pointed family.
9. With no exceptional component all fibre maps are isomorphisms. The universal isomorphism
   open is the whole base, including for nonreduced bases, so the original map is an isomorphism.
10. Actual section pullback respects products. Arbitrary relative-Proj base change and
    the fraction formula for evaluation give the base-change and labelled-isomorphism squares.
11. A competing labelled contraction is proper. Elementary contraction direct image identifies
    its logarithmic section algebra with A. Stable-field linear series and the relative image
    lemma reconstruct its target by this Proj. The evaluation fraction formula gives the
    isomorphism commuting with q, and hence preserving each marking.
12. The structure-pushforward isomorphism makes the competing proper surjection a
    quotient on spaces and injective on sections. Two maps agreeing after that
    surjection therefore agree on spaces and sheaves, proving uniqueness universally.
-/
theorem exists_logCanonicalDeletionAlgebra {Y T : Scheme.{u}} (f : Y ⟶ T)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (g : ℕ) (hg : 2 ≤ g) (r : ℕ) (a : Fin r → (T ⟶ Y))
    (ha : ∀ i, a i ≫ f = 𝟙 T)
    (hdisjoint : Pairwise (fun i j : Fin r ↦ Disjoint (Set.range (a i)) (Set.range (a j))))
    (hsmooth : ∀ i, Set.range (a i) ⊆ (f.smoothLocus : Set Y))
    (hnodal : HasNodalGeometricFibres f)
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      IsReduced (pullback f t) ∧ (pullback f t).IsPureDimension 1 ∧
      @Scheme.arithmeticGenus Ω _ (pullback f t) ⟨pullback.snd f t⟩ = g) :
    IsEffectiveCartierCenter (nodalDeletionMarking a) ∧
    ∃ (omega : Y.Modules) (d : NodalDualizingDatum f omega),
      (∀ (omega' : Y.Modules) (d' : NodalDualizingDatum f omega'),
        ∃! e : omega ≅ omega', d.fundamental ≫ e.hom = d'.fundamental) ∧
      (∀ (T' : Scheme.{u}) (u : T' ⟶ T),
        ∃ d' : NodalDualizingDatum (pullback.snd f u)
          ((Scheme.Modules.tensorPullback (pullback.fst f u)).obj omega),
          (∀ (U : Y.Opens) (s : Γ(Y, U)),
            ((Scheme.Modules.tensorPullback (pullback.fst f u)).map d.fundamental).app
              (pullback.fst f u ⁻¹ᵁ U)
              (f.relativeDifferentialsPullbackGenerator (pullback.fst f u) U s) =
            d'.fundamental.app (pullback.fst f u ⁻¹ᵁ U)
              ((pullback.snd f u).relativeDifferentialsDerivation.d
                (X := op (pullback.fst f u ⁻¹ᵁ U)) ((pullback.fst f u).app U s))) ∧
          Nonempty ((Scheme.Modules.tensorPullback (pullback.fst f u)).obj
            (nodalDeletionLine a omega) ≅
              nodalDeletionLine (fun i ↦ f.baseChangeSection (a i) (ha i) u)
                ((Scheme.Modules.tensorPullback (pullback.fst f u)).obj omega))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
        (Z : irreducibleComponents (pullback (C := Scheme.{u}) f t)),
        nodalDeletionDegree f (nodalDeletionLine a omega) Ω t Z =
          (2 * (pullback f t).normalizedComponentGenus (pullback.snd f t) Z : ℤ) - 2 +
          (((pullback f t).normalizedComponentMap Z ⁻¹'
            {x | x ∉ (pullback.snd f t).smoothLocus}).ncard : ℤ) +
          (((pullback f t).normalizedComponentMap Z ⁻¹'
            (⋃ i : Fin r, Set.range (f.baseChangeSection (a i) (ha i) t))).ncard : ℤ)) ∧
      (nodalDeletionLine a omega).IsInvertible ∧
      NodalDeletionDualizingIsomorphisms f a omega d ∧
      (NodalDeletionNumerics f a ha (nodalDeletionLine a omega) →
        (∀ m : ℕ, 2 ≤ m →
          ((Scheme.Modules.pushforward f).obj
            ((nodalDeletionLine a omega).tensorPow m)).IsFiniteLocallyFree ∧
          ∀ (T' : Scheme.{u}) (u : T' ⟶ T),
            IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.snd f u) u
              (pullback.fst f u) pullback.condition
              ((nodalDeletionLine a omega).tensorPow m))) ∧
        Epi ((Scheme.Modules.tensorPullbackSectionAdjunction f).counit.app
          ((nodalDeletionLine a omega).tensorPow 3)) ∧
        ∃ (A : Scheme.Modules.RelativeSectionAlgebra f ((nodalDeletionLine a omega).tensorPow 3))
          (q : Y ⟶ A.data.relProj) (hq : q ≫ A.data.relProjHom = f),
          A.IsCanonicalMap q ∧
          (∀ V : T.affineOpens,
            Algebra.adjoin Γ(T, V.1) (A.data.grading V 1 : Set (A.data.obj V)) = ⊤) ∧
          (∃ G : GradedSheafAlgebra (fun j ↦ (Scheme.Modules.pushforward f).obj
              (((nodalDeletionLine a omega).tensorPow 3).tensorPow j)),
            (∀ (U : T.Opens) (c : Γ(T, U)),
              G.unit.val.app (op U) c = Scheme.Modules.unitSectionsEquiv (f ⁻¹ᵁ U) (f.app U c)) ∧
            ∀ (m n : ℕ) (U : T.Opens)
              (s : Γ(((nodalDeletionLine a omega).tensorPow 3).tensorPow m, f ⁻¹ᵁ U))
              (t : Γ(((nodalDeletionLine a omega).tensorPow 3).tensorPow n, f ⁻¹ᵁ U)),
              G.mul m n U s t =
                (((nodalDeletionLine a omega).tensorPow 3).tensorPowAddIso m n).inv.app
                  (f ⁻¹ᵁ U) (Scheme.Modules.tmulSection s t)) ∧
          Flat A.data.relProjHom ∧ LocallyOfFinitePresentation A.data.relProjHom ∧
          NodalDeletionProjectiveEmbedding f ((nodalDeletionLine a omega).tensorPow 3) A ∧
          IsStablePointedCurve A.data.relProjHom (fun i ↦ a i ≫ q)
            (by intro i; simp only [Category.assoc, hq, ha]) ∧
          (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
            @Scheme.arithmeticGenus Ω _ (pullback A.data.relProjHom t)
              ⟨pullback.snd A.data.relProjHom t⟩ = g) ∧
          NodalDeletionContracts f (nodalDeletionLine a omega) A.data.relProjHom q hq ∧
          ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
              (Z : irreducibleComponents (pullback (C := Scheme.{u}) f t)),
              nodalDeletionDegree f (nodalDeletionLine a omega) Ω t Z ≠ 0) → IsIso q) ∧
          NodalDeletionBaseChange f ((nodalDeletionLine a omega).tensorPow 3) A q ∧
          NodalDeletionIsomorphisms f a ((nodalDeletionLine a omega).tensorPow 3) A q ∧
          ∀ (Z : Scheme.{u}) (p : Z ⟶ T) (b : Fin r → (T ⟶ Z))
            (hb : ∀ i, b i ≫ p = 𝟙 T), IsStablePointedCurve p b hb →
            ∀ (c : Y ⟶ Z) (hc : c ≫ p = f), (∀ i, a i ≫ c = b i) →
              NodalDeletionContracts f (nodalDeletionLine a omega) p c hc →
              ∃! e : A.data.relProj ≅ Z, q ≫ e.hom = c ∧ e.hom ≫ p = A.data.relProjHom) := by
  sorry

end AlgebraicGeometry
