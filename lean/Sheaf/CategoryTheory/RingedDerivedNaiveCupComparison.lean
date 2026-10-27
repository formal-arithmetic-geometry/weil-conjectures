module

public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.Algebra.Homology.RingedDerivedTensorAugmentationNaturality
public import Sheaf.Paper.RingedComparisonTensorAdjunction
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction

/-! # Derived and naive cup products for arbitrary unbounded complexes

Source: Stacks Project, Tag 0FPK, lemma-cup-compatible-with-naive, entire diagram;
Tag 0FPJ, section-cup-product, for the global specialization.
(blueprint: lem-sfb-ringed-derived-naive-cup-comparison).

All tensor augmentations retain their actual direction. Neither ordinary tensor
nor direct image is assumed to preserve quasi-isomorphisms or infinite direct sums.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules.RingedSiteCup

/-- Componentwise direct image of complexes for the given ringed-topos morphism.
Source: Stacks Project, Tag 0FPK
(blueprint: lem-sfb-ringed-derived-naive-cup-comparison). -/
abbrev complexDirectImage {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    [RingedPathRightDerived e] :=
  e.pushforward.mapHomologicalComplex (.up ℤ)

/-- The naive cup cochain map is the adjunct of the ordinary tensor constraint
followed by the tensor of the ordinary counits. Its restriction to each (i,j)
summand is the ordinary section tensor map followed by the image of that summand
inclusion. This construction uses the coproduct property in the source only.
Source: Stacks Project, Tag 0FPK, naive cup before the lemma and its final square
(blueprint: lem-sfb-ringed-derived-naive-cup-comparison). -/
def naive {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    [RingedPathRightDerived e] (M N : CochainComplex X.mateModules ℤ) :
    ((KFlatFixedTensor.totalTensor Y.ring).obj ((complexDirectImage e).obj M)).obj
        ((complexDirectImage e).obj N) ⟶
      (complexDirectImage e).obj (((KFlatFixedTensor.totalTensor X.ring).obj M).obj N) :=
  (e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _
    ((e.ordinaryTensor.totalIso Y.ring X.ring e.inverseRing e.inverse e.algebraic
      e.ringMap e.pullback e.object_eq e.pushforward e.moduleAdjunction
      ((complexDirectImage e).obj M) ((complexDirectImage e).obj N)).inv ≫
      HomologicalComplex.mapBifunctorMap
        ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app M)
        ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app N)
        X.mateTensor (.up ℤ))

/-- The entire six-object square for arbitrary unbounded complexes. The right-derived
comparison β is the canonical unit with the normalized derived adjunction, as supplied
by `RingedPathRightDerived`; ρ is fixed by all K-flat resolution augmentations.
Source: Stacks Project, Tag 0FPK, lemma-cup-compatible-with-naive
(blueprint: lem-sfb-ringed-derived-naive-cup-comparison).

Proof:
1. Put A=f_*M, B=f_*N, V=Tot(A tensor B), T=Tot(M tensor N). The ordinary
adjunction constructs the naive chain map summand by summand, with the same
(-1)^i sign in both totals; direct image need not commute with sums.
2. The representative derived-adjunction formula (preDerivedAdjunctionGeneral,
Tag 0FPI) at identity representatives says ε_[I] composed with Lβ_I equals
[e_I] composed with α_(f_*I). These are the canonical resolving comparisons.
3. By the cup definition, the adjunct of the clockwise composite is ρ_(M,N)
composed with ((ε_[M] Lβ_M) tensor (ε_[N] Lβ_N)) composed with μ_(A,B).
Insert step 2 and naturality of ρ for the two ordinary counits.
4. Apply lem-sfb-ringed-pullback-derived-ordinary-tensor (Tag 0FPH) to A,B.
The result is [Tot(e_M tensor e_N) δ_(A,B)] α_V Lρ_(A,B).
5. On every generalized pure tensor the ordinary adjunction and its normalized
tensor constraint give Tot(e_M tensor e_N) δ_(A,B)=e_T f^*(ν). Both maps send
r tensor (x tensor y) to r(e_M(1 tensor x) tensor e_N(1 tensor y)).
Sheafification and the coproduct property give equality of cochain maps; no
factor is interchanged, hence no additional sign occurs.
6. Naturality of α for ν and step 2 at T give ε_[T] L(β_T [ν] ρ_(A,B)),
the adjunct of the counterclockwise composite. The adjunction bijection is
injective, proving the equality. The same proof for the point topos is the
global-sections assertion below; compatible families require no final object. -/
theorem derived_naive_cup_comparison
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    [d : RingedPathRightDerived e] (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (M N : CochainComplex X.mateModules ℤ) :
    Y.tensor.map (Prod.mkHom (d.eta.app M) (d.eta.app N)) ≫
        relative e a b (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N) ≫
        e.right.map ((modelTensorAugmentation X b).app (M, N)) =
      (modelTensorAugmentation Y a).app
          ((complexDirectImage e).obj M, (complexDirectImage e).obj N) ≫
        DerivedCategory.Q.map (naive e M N) ≫
        d.eta.app (((KFlatFixedTensor.totalTensor X.ring).obj M).obj N) := by
  sorry

/-- The naive map for compatible-family module sections. The ordinary adjunction
with extension of scalars from A=Γ(R) supplies the same tensor of counits.
Source: Stacks Project, Tags 0FPJ and 0FPK
(blueprint: lem-sfb-ringed-derived-naive-cup-comparison). -/
def globalNaive (X : RingedTensorCorner.{u, w}) (M N : CochainComplex X.mateModules ℤ) :
    (((globalSections X).mapHomologicalComplex (.up ℤ)).obj M) ⊗
        (((globalSections X).mapHomologicalComplex (.up ℤ)).obj N) ⟶
      ((globalSections X).mapHomologicalComplex (.up ℤ)).obj
        (((KFlatFixedTensor.totalTensor X.ring).obj M).obj N) :=
  ((globalModuleAdjunction X).mapHomologicalComplex (.up ℤ)).homEquiv _ _
    (HomologicalComplex.mapBifunctorComparison (globalPullbackTensor X) (.up ℤ)
        (((globalSections X).mapHomologicalComplex (.up ℤ)).obj M)
        (((globalSections X).mapHomologicalComplex (.up ℤ)).obj N) ≫
      HomologicalComplex.mapBifunctorMap
        (((globalModuleAdjunction X).mapHomologicalComplex (.up ℤ)).counit.app M)
        (((globalModuleAdjunction X).mapHomologicalComplex (.up ℤ)).counit.app N)
        X.mateTensor (.up ℤ))

/-- The same square for f_*=Γ(C,-), in D(Γ(C,R)), without a final object of C.
The scalar tensor augmentation is the canonical lax tensorator of localization.
Source: Stacks Project, Tag 0FPJ and Tag 0FPK
(blueprint: lem-sfb-ringed-derived-naive-cup-comparison).

Proof: specialize the six-object diagram proof to the ringed point with
coefficient ring Γ(C,R). The functor globalSections is compatible families,
by its evaluation-at-one identification, and globalDerivedUnit is the
K-injective comparison β. globalLeftTensor is normalized by the same ordinary
tensor comparison and flat K-flat resolutions. Thus the six adjunct polygons
in derived_naive_cup_comparison apply with globalModuleAdjunction and
globalDerivedAdjunction. The source tensor augmentation is the native scalar
localization tensorator, and the target augmentation is the representative
normalized modelTensorAugmentation. Injectivity of the global derived Hom
bijection gives the displayed equality. No final object enters any construction. -/
theorem global_derived_naive_cup_comparison (X : RingedTensorCorner.{u, w})
    (b : RingedTensorModel X) (M N : CochainComplex X.mateModules ℤ) :
    ((globalDerivedUnit X).app M ⊗ₘ (globalDerivedUnit X).app N) ≫
        global X b (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N) ≫
        (derivedGlobalSections X).map ((modelTensorAugmentation X b).app (M, N)) =
      Functor.LaxMonoidal.μ DerivedCategory.Q
          (((globalSections X).mapHomologicalComplex (.up ℤ)).obj M)
          (((globalSections X).mapHomologicalComplex (.up ℤ)).obj N) ≫
        DerivedCategory.Q.map (globalNaive X M N) ≫
        (globalDerivedUnit X).app (((KFlatFixedTensor.totalTensor X.ring).obj M).obj N) := by
  sorry

end SheafOfModules.RingedSiteCup
