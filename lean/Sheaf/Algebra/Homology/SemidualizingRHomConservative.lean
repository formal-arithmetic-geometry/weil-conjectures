/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.SecTraceFormula.LocalDerivedTensorNonvanishing
import Sheaf.Algebra.Homology.CompleteLocalCoherentDuality

/-! # Derived Hom from a semidualizing complex is conservative

Source: Stacks Project, dualizing.tex, Tags 0BFR and 0A7C, and the localization,
completion and cone argument recorded in the DAG
(blueprint: lem-trf-semidualizing-rhom-conservative).

The ordinary module category is encoded by the existing one-object bottom-topology
ringed site. Scalar action is the transpose of its left unitor under the existing
representative-normalized tensor--Hom adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace DerivedCategory

/-- Derived Hom from a bounded coherent semidualizing complex detects zero objects
and isomorphisms between bounded coherent objects. No finite projective or injective
dimension is assumed.
Source: Stacks Project, dualizing.tex, Tags 0BFR and 0A7C; more-algebra.tex,
Tags 0A6A and 0A65 (blueprint: lem-trf-semidualizing-rhom-conservative).

Proof:

1. First record how the hypotheses pass through a flat map $A\to B$ with $B$ Noetherian. Exactness
of tensor [lem-weil-pbc-flat-tensor-exact], applied to the cycle, boundary and cohomology exact
sequences of a representative complex, gives $H^i(K\otimes_A^{\mathbf L}B)=H^i(K)\otimes_A B$:
termwise tensor preserves acyclic complexes, so computes its derived functor. A finite generating
family tensored with $1$ still generates. Hence $C_B,Z_B$ have bounded finite cohomology. The
Noetherian pseudo-coherence criterion applies to $C$. The flat RHom comparison, with $E=C$ and
respectively $L=Z,C$, therefore gives $R\operatorname{Hom}_B(C_B,Z_B)=0$ and an isomorphism
$R\operatorname{Hom}_A(C,C)\otimes_A^{\mathbf L}B\cong R\operatorname{Hom}_B(C_B,C_B)$. Both
targets $Z,C$ are bounded below as required.

2. The latter comparison carries the scalar-action morphism to scalar action on $C_B$. To check
the actual map, choose a bounded-above finite free model $P$ of $C$ using the pseudo-coherence
criterion. The projective Hom model [lem-pod-projective-hom-evaluation-model] represents its
derived endomorphisms by $\operatorname{Hom}^{\bullet}_A(P,P)$. Scalar action sends $a$ to the
chain endomorphism $p\mapsto ap$. By the stated construction of flat RHom comparison, after scalar
extension this map is sent to the endomorphism $p\otimes b\mapsto ap\otimes b$. Extending
$B$-linearly gives exactly $p\otimes b\mapsto p\otimes sb$ for a scalar $s\in B$. Since
$P\otimes_A B$ models $C_B$, this is its scalar-action map $B\to R\operatorname{Hom}_B(C_B,C_B)$.
Thus the scalar-action isomorphism persists under the flat change of rings.

3. Now suppose $(A,\mathfrak m)$ itself is complete local. Choose $\Omega$ from coherent duality
[lem-trf-complete-local-coherent-duality], and set $W=R\operatorname{Hom}_A(Z,\Omega)$. The
bounded clause gives $W\in D^b_{\mathrm{fg}}(A)$, and canonical biduality gives $Z\cong
R\operatorname{Hom}_A(W,\Omega)$. The tensor lemma gives $T=C\otimes_A^{\mathbf L}W\in
D^-_{\mathrm{fg}}(A)$. In particular $T$ is in the unbounded coherent category on which this
duality applies; no lower bound on its cohomology has been asserted.

4. On the one-object ringed site, tensor-Hom adjunction [lem-weil-pbc-ringed-internal-hom-exact-
restriction] identifies $R\operatorname{Hom}_A(T,\Omega)$ with
$R\operatorname{Hom}_A(C,R\operatorname{Hom}_A(W,\Omega))\cong R\operatorname{Hom}_A(C,Z)=0$.
Biduality for $T\in D_{\mathrm{fg}}(A)$ gives $T\cong R\operatorname{Hom}_A(0,\Omega)=0$. A local
ring with a maximal ideal is nonzero. If $C=0$, its derived endomorphism object is zero,
contradicting the homothety isomorphism $A\cong R\operatorname{Hom}_A(C,C)$. Hence $C\ne0$. Tensor
nonvanishing then gives $W=0$, and biduality for $Z$ gives $Z\cong
R\operatorname{Hom}_A(0,\Omega)=0$. This proves the complete-local case.

5. For an arbitrary Noetherian local ring $(A,\mathfrak m)$ form $\widehat A=\varprojlim
A/\mathfrak m^n$. It is Noetherian by [lem-weil-pbc-adic-completion-noetherian] and local with
maximal ideal $\mathfrak m\widehat A$ by [lem-weil-pbc-local-completion-local-ring]. Since the
Noetherian ideal $\mathfrak m$ is finitely generated, [lem-weil-pbc-adic-completion-mod-ideal]
says $\widehat A$ is complete for that maximal ideal. The map $A\to\widehat A$ is faithfully flat
by [lem-weil-pbc-local-completion-faithfully-flat]. Steps 1--2 transport both hypotheses and both
bounded-coherent objects to $\widehat A$, so steps 3--4 give $Z\otimes_A^{\mathbf L}\widehat A=0$.

6. By the cycle calculation of step 1, $H^i(Z)\otimes_A\widehat A=0$ for every $i$. Faithfully
flat tensor detection [lem-sc-faithfully-flat-tensor-zero] implies $H^i(Z)=0$ for all $i$. Apply
[lem-weil-pbc-unbounded-derived-iso-cohomology] to $Z\to0$ to conclude $Z=0$. This proves the
assertion for every Noetherian local ring.

7. For a general $A$ and every maximal ideal $\mathfrak m$, the localization $A_{\mathfrak m}$ is
flat over $A$ and Noetherian by [lem-weil-pbc-localization-flat] and [lem-weil-pbc-localization-
noetherian]. It is local: a fraction with numerator outside $\mathfrak m$ is a unit, and all other
fractions form the proper ideal $\mathfrak mA_{\mathfrak m}$. Steps 1--2 transport the hypotheses,
and the local result gives $Z\otimes_A^{\mathbf L}A_{\mathfrak m}=0$. The same flat cohomology
calculation says $H^i(Z)_{\mathfrak m}=0$. For each $i$ apply [lem-weil-pbc-linear-map-bijective-
at-maximal-localizations] to $H^i(Z)\to0$: all its maximal localizations are bijective, so
$H^i(Z)=0$. The cohomological isomorphism criterion gives $Z=0$. This also covers the zero ring,
since the cited maximal-localization criterion allows an empty set of maximal ideals.

8. Finally let $f:X\to Y$ be as in the statement and choose its distinguished cone triangle $X\to
Y\to T\to X[1]$ in the ordinary derived category [def-weil-abstract-derived-category]. The long
exact cohomology sequence [lem-sf-derived-homology-long-exact] gives short exact sequences
$0\to\operatorname{coker}H^i(f)\to H^i(T)\to\ker H^{i+1}(f)\to0$. The kernel is finite by [lem-
weil-pbc-noetherian-submodule-finite]; the cokernel is generated by the images of generators of
$H^i(Y)$. Lift generators of the kernel to $H^i(T)$ and adjoin generators of the cokernel to
obtain a finite generating set. The same sequence makes $H^i(T)$ zero outside a finite interval.
Thus $T\in D^b_{\mathrm{fg}}(A)$.

9. Exactness in the second variable of [lem-weil-pbc-ringed-internal-hom-exact-restriction] sends
the cone triangle to a distinguished triangle whose first arrow is $R\operatorname{Hom}_A(C,f)$.
Since that arrow is an isomorphism, [lem-kun-distinguished-cone-zero] gives
$R\operatorname{Hom}_A(C,T)=0$. The object-detection result just proved applies to this bounded-
coherent $T$, hence $T=0$. Applying the same cone criterion to the original triangle gives that
$f$ is an isomorphism.
-/
theorem semidualizing_rhom_conservative
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{u} (RingSiteModules A)]
    (C : DerivedCategory (RingSiteModules A))
    (hCbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologyFunctor (RingSiteModules A) i).obj C))
    (hCfinite : ∀ i : ℤ, Module.Finite A
      (((homologyFunctor (RingSiteModules A) i).obj C).val.obj (op ⟨PUnit.unit⟩)))
    (hscalar : IsIso ((SignedRingedHom.adjunction ⊥
      (CochainComplex.onePointRingSheaf A) C).homEquiv _ _ (λ_ C).hom)) :
    (∀ (Z : DerivedCategory (RingSiteModules A)),
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (RingSiteModules A) i).obj Z)) →
      (∀ i : ℤ, Module.Finite A
        (((homologyFunctor (RingSiteModules A) i).obj Z).val.obj (op ⟨PUnit.unit⟩))) →
      IsZero ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf A) C).obj Z) →
      IsZero Z) ∧
    (∀ (X Y : DerivedCategory (RingSiteModules A)) (f : X ⟶ Y),
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (RingSiteModules A) i).obj X)) →
      (∀ i : ℤ, Module.Finite A
        (((homologyFunctor (RingSiteModules A) i).obj X).val.obj (op ⟨PUnit.unit⟩))) →
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
        IsZero ((homologyFunctor (RingSiteModules A) i).obj Y)) →
      (∀ i : ℤ, Module.Finite A
        (((homologyFunctor (RingSiteModules A) i).obj Y).val.obj (op ⟨PUnit.unit⟩))) →
      IsIso ((SignedRingedHom.hom ⊥ (CochainComplex.onePointRingSheaf A) C).map f) →
      IsIso f) := by
  sorry

end DerivedCategory
