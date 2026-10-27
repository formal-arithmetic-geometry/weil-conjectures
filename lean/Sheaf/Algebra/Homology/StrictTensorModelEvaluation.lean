module

public import Sheaf.Algebra.Homology.StrictTensorDerivedData
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Strict tensor models and normalized evaluation

Source: Stacks Project, sites-cohomology.tex, Tag 06YU, definition-derived-tor;
derived.tex, Tag 015F, lemma-right-derived-exact-functor.
(blueprint: lem-sf-cbc-strict-tensor-model-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor
open SheafOfModules.KFlatFixedTensor
namespace SheafOfModules.StrictTensorEvaluation

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

section Slice
variable (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The first requested extension computation: apply the exact-extension localization
comparison inside reduction, then the specified strict computation on the base.
Source: Stacks 015F, 06YU (blueprint: lem-sf-cbc-strict-tensor-model-evaluation). -/
def extensionFirst (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R)
    (m : Computation.{c, v, r} R t b) (S : AlgebraTowers.{c, v, r} R)
    (P : HomotopyCategory (LocalizedStrictTensor.Modules.{max c v, v, r} (R.over V)) (.up ℤ))
    (h : Good.{c, v, r} R
      (((localizedSystemExtension.{c, v, r} R V).mapHomotopyCategory (.up ℤ)).obj P)) :
    (derivedReduction.{c, v, r} R t S).obj
        ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.obj
          (DerivedCategory.Qh.obj P)) ≅
      DerivedCategory.Qh.obj ((strictHomotopy.{c, v, r} R S).obj
        (((localizedSystemExtension.{c, v, r} R V).mapHomotopyCategory (.up ℤ)).obj P)) :=
  (derivedReduction.{c, v, r} R t S).mapIso
    ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategoryFactorsh.app P) ≪≫
      comparison.{c, v, r} R t m.towerOne S (m.theta S) _ h.2

/-- The second requested extension computation: apply exact termwise extension to
the slice computation, then use its exact-localization comparison. Evaluation of
this composite uses `evaluationExtensionDerived`, the localization of the ordinary
termwise identity, together with `Computation.evaluation_normalized` on the slice.
Source: Stacks 015F, 06YU (blueprint: lem-sf-cbc-strict-tensor-model-evaluation). -/
def extensionSecond
    (t : TowerTensor.{max c v, v, r} (R.over V))
    (b : BaseTensor.{max c v, v, r} (R.over V))
    (m : Computation.{max c v, v, r} (R.over V) t b)
    (S : AlgebraTowers.{c, v, r} R)
    (P : HomotopyCategory (LocalizedStrictTensor.Modules.{max c v, v, r} (R.over V)) (.up ℤ))
    (h : Good.{max c v, v, r} (R.over V) P) :
    (towerExtension.{c, v, r} R V).mapDerivedCategory.obj
        ((derivedReduction.{max c v, v, r} (R.over V) t
          (S ⋙ sliceAlgebras.{c, v, r} R V)).obj (DerivedCategory.Qh.obj P)) ≅
      DerivedCategory.Qh.obj
        (((towerExtension.{c, v, r} R V).mapHomotopyCategory (.up ℤ)).obj
          ((strictHomotopy.{max c v, v, r} (R.over V)
            (S ⋙ sliceAlgebras.{c, v, r} R V)).obj P)) :=
  (towerExtension.{c, v, r} R V).mapDerivedCategory.mapIso
    (comparison.{max c v, v, r} (R.over V) t m.towerOne
      (S ⋙ sliceAlgebras.{c, v, r} R V) (m.theta _) P h.2) ≪≫
    (towerExtension.{c, v, r} R V).mapDerivedCategoryFactorsh.app _

end Slice

/-- Strict tensor towers compute the fixed diagram-derived tensor, with homotopy and
coefficient naturality, normalized evaluation, and both exact slice-extension formulas.
The supplied presentations retain the specified two-sided derived comparisons.
`comparison`, `extensionFirst` and `extensionSecond` give the displayed isomorphisms
by their explicit normalized composites; `Computation` records their naturality and
local generator equations. Flat-term K-flat hypotheses occur only as `Good` on the
resolving input and its extension, hence on their two constant diagrams. Coefficients
and transitions are unrestricted.

Source: Stacks Project, sites-cohomology.tex, Tag 06YU, definition-derived-tor and
preceding one-sided construction; derived.tex, Tag 015F, lemma-right-derived-exact-functor.
(blueprint: lem-sf-cbc-strict-tensor-model-evaluation).

Proof:
1. Identify strict towers with modules on the ringed diagram site using
lem-weil-pbc-diagram-site-realization. Kernels and cokernels are levelwise, so exact
diagonal and evaluation have the localization comparisons of
lem-weil-pbc-exact-functor-derived-factorization.
2. Tensor on the diagram site is sheafified sectionwise tensor. Its evaluation
comparison is identity on local pure tensors by lem-pur-cochain-pullback-tensor-coherence.
For a degree-zero coefficient only (i,0) survives in degree i. The differential is
d_P tensor 1, transitions are 1 tensor s_n, and coefficient maps are 1 tensor a_n.
Sheafification uniqueness extends these equations to the entire module sheaves.
3. Apply lem-trf-site-one-sided-tensor-normalization on the diagram site to Delta P
and the arbitrary degree-zero coefficient. Compose with exact diagonal localization
and the ordinary comparison, obtaining precisely `comparison`. Naturality in both
homotopy variables of that lemma gives `natural_first` and `natural_coefficient`.
4. Exact evaluation is a ringed inverse image and preserves flat-term K-flat objects
by lem-weil-pbc-ringed-pullback-preserves-kflat. Apply
lem-weil-pbc-tensor-comparison-descent-representatives with the ordinary evaluation
comparison and the fixed two-sided tensor comparisons. This gives `Evaluation.derived`
and its normalized representative square, using full faithfulness in
lem-weil-pbc-site-derived-tensor-descent.
5. Resolve the arbitrary coefficient by a flat-term K-flat quasi-isomorphism, using
lem-pc-kflat-resolution. Evaluate that resolution and apply one-sided naturality on
both sites. The representative square gives equality on the resolution; cancellation
of its invertible derived image gives `evaluation_normalized` for the original tower.
6. At a strict transition both ordinary routes send p tensor s to p tensor s_n(s).
The coefficient square is the algebra-tower naturality square tensored with 1_P.
Tensor homotopies with the degree-zero factor. These equations hold before localization
and thus also after it, without any faithfulness claim for derived evaluations.
7. Apply the same construction on the slice and the base, using exactly the four
stated resolving hypotheses. Exact extension gives the localization comparisons.
Their composites are `extensionFirst` and `extensionSecond`. Extension and evaluation
commute termwise; localization uniqueness identifies the comparisons under that
ordinary identity, as in `evaluationExtensionDerived`. Thus the evaluated
normalizations and naturality persist. No coefficient flatness, K-flatness, boundedness
or transition surjectivity is used.
-/
theorem strict_tensor_model_evaluation
    (t : TowerTensor.{c, v, r} R) (b : BaseTensor.{c, v, r} R) :
    Nonempty (Computation.{c, v, r} R t b) ∧
      ∀ (V : C) [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
        [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
        (tV : TowerTensor.{max c v, v, r} (R.over V))
        (bV : BaseTensor.{max c v, v, r} (R.over V)),
        Nonempty (Computation.{max c v, v, r} (R.over V) tV bV) := by
  sorry

end SheafOfModules.StrictTensorEvaluation
