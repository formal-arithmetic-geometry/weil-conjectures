/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.DerivedNakayamaResolution
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Sheaf.Paper.BoundedClassicalAbelianCounit
import Sheaf.Paper.IntegralImageKoszulClassical
import Sheaf.Paper.SupportPullbackKoszulClassical

/-! # Relative nonpositivity of supported integral-image Koszul complexes

Source: the agent-created local comparison prerequisite motivated by Hemo--Richarz--Scholbach,
Section 8, (8.1) and Lemma 8.6; its reviewed proof uses Theorem 6.2(3), Section 7.1.1,
and Stacks Tags 09BM, 09BN, 099V.
(blueprint: lem-sfb-supported-image-koszul-comparison-nonpositive).

The local assertion itself is not quoted from Lemma 8.6; its independent reference is WANTED
in the DAG. The source scheme of the support chain is Noetherian. The ambient affine scheme
and its affine pro-etale test objects need not be Noetherian.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The literal underlying abelian two-term complex `[N -- pi^n --> N]` in degrees -1,0.
The scalar endomorphism is selected from the published resolution theorem, whose sectionwise
formula uniquely determines it as multiplication by the specified uniformizer; no unspecified
existence choice of an object or differential is made. `double` has zero terms elsewhere.
Source: the local comparison node's definition of C_n(N), and the scalar construction of
HRS Section 7.1.1, as recorded in det-pe-derived-nakayama-resolution.
(blueprint: lem-sfb-supported-image-koszul-comparison-nonpositive). -/
def supportedImageKoszulComplex
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (U : Scheme.{u}) (n : ℕ)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) U)) :
    CochainComplex (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) ℤ :=
  HomologicalComplex.double
    (((DerivedNakayama.scalarOnModules ℓ E U
      ((DerivedNakayama.derived_nakayama_resolution ℓ E).choose ^ n)).app N).hom)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- Ordinary derived abelian direct image of the literal Koszul complex of the actual image,
after the specified support chain and module pullback. The path functor is the composite
of the published open extension by zero and closed direct image, with identity at the root.
Source: the local comparison node's displayed R nu_* C_n(N); Stacks Tag 099V.
(blueprint: lem-sfb-supported-image-koszul-comparison-nonpositive). -/
def supportedImageKoszulComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    {X S : Scheme.{u}} {tree : QcqsOpenClosedTree X} (p : tree.Path S)
    {L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) S)} (f : L ⟶ M)
    {U : Scheme.{u}} (v : U ⟶ X) (n : ℕ) :
    DerivedCategory (Sheaf U.smallEtaleTopology Ab.{u + 1}) :=
  (comparisonLowerStar Ab.{u + 1} U).rightDerivedFunctor.obj
    (DerivedCategory.Q.obj (supportedImageKoszulComplex ℓ E U n
      ((CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E) v).obj
        ((p.extension (DerivedNakayama.integerRing ℓ E)).obj (image f)))))

/-- Positive relative comparison cohomology vanishes for actual supported integral images
of maps between separately locally finite scalar models, when the source is Noetherian.
Source: agent-created comparison obligation motivated by HRS Section 8, (8.1), Lemma 8.6;
HRS Theorem 6.2(3), Section 7.1.1, and Stacks Tag 099V supply the reviewed proof route.
An independent reference for this exact local theorem is WANTED in the node.
(blueprint: lem-sfb-supported-image-koszul-comparison-nonpositive).

Proof plan, following the six steps of the reviewed DAG:
1. L and M are constructible on the single stratum S by sk-def-sfb-constructible.
   Apply lem-sfb-noetherian-scalar-constructible-heart first to f, then to the map
   M -> coker f. Thus the actual image ker(M -> coker f) is constructible. This does not
   replace the image by a topological closure or assume that the entries of f are constant.
2. S is qcqs by lem-weil-pbc-locally-noetherian-quasi-separated. The theorem
   lem-sfb-finite-model-sheaf-quotient-constructible gives finite constructible ordinary
   B/pi^n-module cohomology in degrees -1,0 for its derived reduction. The principal calculus
   lem-pe-principal-reduction-cone-calculus identifies the underlying complex with C_n(I).
   Apply sk-thm-pe-constructible-comparison: its two cohomology sheaves are classical.
3. Induct down the support chain. At open arrows apply
   lem-cbc-proetale-extension-zero-comparison. Closed immersions are qcqs by their affine
   quotient presentation (def-weil-closed-immersion, lem-weil-pbc-affine-scheme-qcqs and
   def-weil-quasi-separated-morphism); degree zero of sk-thm-pe-direct-image-comparison
   gives classicality for their ordinary pushforwards. Both operations are exact by
   lem-weil-pbc-proetale-ringed-open-closed, with the specified quasi-compact open complement.
   Use lem-sfb-internal-module-operations-transport to identify internal and ordinary
   operations. Induction starts with the identity for the root path.
4. Pullback is exact by det-prop-sfb-module-pullback-exact-main. The inverse-image square
   in sk-thm-pe-direct-image-comparison needs no qcqs hypothesis on v. Together with
   lem-weil-pbc-exact-functor-complex-cohomology and B-linearity, it gives
   H^t C_n(v^*J(I)) = v^*J H^t C_n(I). These sheaves are classical and vanish outside -1,0.
   Forgetting the finite scalar action retains classicality of their underlying abelian sheaves.
5. C_n(N) is bounded below with classical abelian cohomology. The bounded-below unit of
   sk-prop-sf-comparison and counit of det-pe-classical-derived-equivalence identify
   nu_U^* R nu_{U,*} C_n(N) with C_n(N). By sk-thm-pe-classical-sheaves, inverse image on
   abelian sheaves is exact and faithful (apply its discrete-integer coefficient case).
   Exact-functor cohomology gives zero pullback of H^q R nu_* for q>0; faithfulness reflects
   zero, since the pulled-back identity endomorphism is zero. All direct images in this
   step are ordinary abelian derived functors, without any completion operation.
6. The vanishing is precisely membership in D^{<=0}. Zero maps and empty schemes give
   the zero complex. Empty chains give the identity, and torsion modules and n=1 are allowed.
   No cohomological-dimension bound is used; U need not be Noetherian. The formerly
   unrestricted parent's application still has to establish the new Noetherian hypothesis
   on S, as the reviewed DAG already records.
-/
theorem supported_image_koszul_comparison_nonpositive
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [IsAffine X]
    {S : Scheme.{u}} [CompactSpace S] [IsLocallyNoetherian S]
    (tree : QcqsOpenClosedTree X) (p : tree.Path S)
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (DerivedNakayama.integerRing ℓ E) S)) (f : L ⟶ M)
    (_hL : HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S L)
    (_hM : HasFiniteConstantLocalModel (DerivedNakayama.integerRing ℓ E) S M)
    (U : Scheme.{u}) (v : U ⟶ X) (_hv : proAffineEtale v)
    (n : ℕ) (_hn : 1 ≤ n) :
    (supportedImageKoszulComparison ℓ E p f v n).IsLE 0 ∧
      ∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (supportedImageKoszulComparison ℓ E p f v n)) := by
  let N := (CondensedRing.upperStar (DerivedNakayama.integerRing ℓ E) v).obj
    ((p.extension (DerivedNakayama.integerRing ℓ E)).obj (image f))
  let C := supportedImageKoszulComplex ℓ E U n N
  have hclassical : ∀ q : ℤ, (comparisonUpperStar Ab.{u + 1} U).essImage (C.homology q) :=
    support_pullback_koszul_classical ℓ E p (image f) n
      (integral_image_koszul_classical ℓ E S L M f _hL _hM n _hn) v
  have hge : C.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    exact HomologicalComplex.isZero_double_X _ _ q (by omega) (by omega)
  have hle : C.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    exact HomologicalComplex.isZero_double_X _ _ q (by omega) (by omega)
  have hKge : (DerivedCategory.Q.obj C).IsGE (-1) :=
    (DerivedCategory.isGE_Q_obj_iff C (-1)).2 inferInstance
  have hKle : (DerivedCategory.Q.obj C).IsLE 0 :=
    (DerivedCategory.isLE_Q_obj_iff C 0).2 inferInstance
  let K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :=
    ⟨DerivedCategory.Q.obj C, ⟨-1, hKge⟩⟩
  have : K.IsGE (-1) := ⟨hKge.1⟩
  have : K.IsLE 0 := ⟨hKle.1⟩
  have hclassicalK : ∀ q : ℤ, (comparisonUpperStar Ab.{u + 1} U).essImage
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K) := by
    intro q
    exact Functor.essImage.ofIso ((DerivedCategory.homologyFunctorFactors _ q).app C).symm
      (hclassical q)
  obtain ⟨e⟩ := bounded_classical_abelian_counit U K (-1) 0 hclassicalK
  have hv : ∀ q : ℤ, 0 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (supportedImageKoszulComparison ℓ E p f v n)) := by
    intro q hq
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj K.obj) :=
      (C.exactAt_of_isLE 0 q hq).isZero_homology.of_iso
        ((DerivedCategory.homologyFunctorFactors _ q).app C)
    exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (comparisonUpperStar Ab.{u + 1} U)
        (hz.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e))
  exact ⟨(DerivedCategory.isLE_iff _ 0).mpr hv, hv⟩

end AlgebraicGeometry.ProEtale
