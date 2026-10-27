module

public import Sheaf.Topology.RelativeFiniteBundleModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Sheaf.Topology.RelativeFiniteBundleRoosEpi
import Sheaf.Topology.RelativeModuleStoneanEpi

/-! # Roos exactness for finite continuous bundles on a profinite slice

Source: Ruimy--Tubach--Wolf, Lemma 1.2.7, and the relative compactness argument of
lem-sfb-relative-finite-bundle-roos; Stacks Tags 08TC, 08YN, 08ZU, 005D and 0BK6
(blueprint: lem-sfb-relative-finite-bundle-roos).

We use the ordinary sectionwise module encoding, equivalent to internal abelian-sheaf
modules by InternalAbelianSheafModule.sectionModuleEquivalence. The ring is the actual
restriction of C(-,T). There is no completion. Natural additive bundle section
presentations also specify the continuous fibrewise additive transitions: by Yoneda,
a natural transformation of these represented section presheaves is a bundle map.
The index n : Nat corresponds to k = n+1 in the node.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Profinite

/-- Small products of ordinary modules on Prof/P are exact.
Source: relative finite-bundle Roos argument, steps 1--3; Stacks Tags 03DA, 03DB, 03CN,
08YN (blueprint: lem-sfb-relative-finite-bundle-roos).

Proof: (1) Restrict the continuous-function ring to the slice. The internal/sectionwise
module equivalence identifies underlying sections and restrictions. Exact forgetting to
abelian sheaves reflects exactness and computes products sectionwise.
(2) On a Stonean test object S, lift a section of an epimorphism over a finite covering.
The finite coproduct of the covering domains surjects onto S. The local lifts give one
section on that coproduct; Stonean projectivity supplies a section of its projection,
so the section lifts on S itself. Every test object admits a Stonean surjective cover.
(3) Choose such lifts simultaneously for all components of a small product. Thus the
product of epimorphisms is epic. Products preserve kernels, and hence are exact.
The empty product is included. No hypothesis on finite bundles enters this assertion. -/
theorem relativeContinuousRing_exact_products
    (P : Profinite.{u}) (T : Type v) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] (I : Type (max u v + 1)) :
    HasExactLimitsOfShape (Discrete I)
      (SheafOfModules.{max u v + 1} (relativeContinuousRing P T)) := by
  classical
  let R := relativeContinuousRing P T
  let A := SheafOfModules.{max u v + 1} R
  have : (lim (J := Discrete I) (C := A)).PreservesEpimorphisms := by
    refine ⟨fun {F G} f hf ↦ ?_⟩
    apply (relativeContinuousRing_epi_iff_stonean P T _).2
    intro Q _
    let ev := SheafOfModules.evaluation.{max u v + 1} R (op Q) ⋙
      forget (ModuleCat.{max u v + 1} (R.obj.obj (op Q)))
    let hF := isLimitOfPreserves ev (limit.isLimit F)
    let hG := isLimitOfPreserves ev (limit.isLimit G)
    intro y
    have hs (j : Discrete I) : Function.Surjective ((f.app j).val.app (op Q)) :=
      (relativeContinuousRing_epi_iff_stonean P T (f.app j)).1 inferInstance Q
    let x : (F ⋙ ev).sections :=
      ⟨fun j ↦ (hs j ((limit.π G j).val.app (op Q) y)).choose, by
        rintro ⟨i⟩ ⟨j⟩ ⟨⟨h⟩⟩
        cases h
        simp⟩
    refine ⟨(Types.isLimitEquivSections hF).symm x, ?_⟩
    apply Concrete.isLimit_ext (G ⋙ ev) hG
    intro j
    have heq := congrArg (fun g ↦ g.val.app (op Q)
      ((Types.isLimitEquivSections hF).symm x)) (limMap_π f j)
    change (limit.π G j).val.app (op Q)
        ((lim.map f).val.app (op Q) ((Types.isLimitEquivSections hF).symm x)) = _
    change (limit.π G j).val.app (op Q)
        ((lim.map f).val.app (op Q) ((Types.isLimitEquivSections hF).symm x)) =
      (f.app j).val.app (op Q)
        ((limit.π F j).val.app (op Q) ((Types.isLimitEquivSections hF).symm x)) at heq
    have hx : (limit.π F j).val.app (op Q) ((Types.isLimitEquivSections hF).symm x) =
        x.val j := Types.isLimitEquivSections_symm_apply hF x j
    exact heq.trans ((congrArg (fun z ↦ (f.app j).val.app (op Q) z) hx).trans
      ((hs j _).choose_spec))
  exact hasExactLimitsOfShape_of_preservesEpi A (Discrete I)

/-- With its actual projections, the termwise product of any small family of unbounded
complexes represents the ordinary derived product.
Source: relative finite-bundle Roos argument, step 4; Stacks Tag 0BK6
(blueprint: lem-sfb-relative-finite-bundle-roos).

Proof: exact products give H^q(product K_i) = product H^q(K_i), since kernels commute
with products and the product of the surjections onto the differential images is epic.
Thus products preserve quasi-isomorphisms. The module category on the small ringed site
is Grothendieck, so choose K-injective resolutions K_i -> I_i. Their product is again a
quasi-isomorphism. By lem-pc-ringed-space-product-kinjective, product I_i represents the
product in the ordinary derived category. Transport this universal property through the
quasi-isomorphism, retaining every projection. The family may be empty or unbounded. -/
theorem relativeContinuousRing_termwise_derived_product
    (P : Profinite.{u}) (T : Type v) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T]
    [HasDerivedCategory.{w} (SheafOfModules.{max u v + 1} (relativeContinuousRing P T))]
    (I : Type (max u v + 1))
    (K : I → CochainComplex
      (SheafOfModules.{max u v + 1} (relativeContinuousRing P T)) ℤ) :
    Nonempty (IsLimit (DerivedCategory.Q.mapCone
      (HomologicalComplex.coneOfHasLimitEval (Discrete.functor K)))) := by
  let A := SheafOfModules.{max u v + 1} (relativeContinuousRing P T)
  have : HasExactLimitsOfShape (Discrete I) A :=
    relativeContinuousRing_exact_products P T I
  have : IsGrothendieckAbelian.{max u v + 1} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses _ (relativeContinuousRing P T)
  exact ⟨isLimitOfPreserves DerivedCategory.Q
    (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K))⟩

/-- The canonical limit injection and 1-s form a short exact sequence for a tower of finite
continuous abelian bundles, and its actual localized arrows extend to a distinguished
triangle. Its product vertex, with the localized projections, is the derived product.
Source: relative finite-bundle Roos argument, steps 5--8; Ruimy--Tubach--Wolf Lemma 1.2.7
and Stacks Tags 08TC, 08ZU, 005C, 005D
(blueprint: lem-sfb-relative-finite-bundle-roos).

Proof: (5) For y in the product on a test Q, pull every bundle to Q. In the product of
their total spaces impose equal-base conditions and x_k-t_k(x_{k+1})=y_k(q). This is a
closed subspace Z_y of a compact Hausdorff space with a clopen basis, hence profinite.
(6) Over each q, any finite set of equations lies in an initial block. Set the next
coordinate to zero and solve backwards x_k=y_k(q)+t_k(x_{k+1}); use zero in the remaining
coordinates. Compactness and the closed finite intersection property give a solution to
all equations. Thus Z_y -> Q is surjective, including when Q is empty.
(7) This single profinite cover carries the coordinate sections solving (1-s)x=y. Local
surjectivity and exact forgetting make 1-s epic. Sectionwise limits identify its kernel
with the ordinary inverse limit, with induced scalar action. The canonical map is the
one having the limit projections as coordinates, so the displayed short complex is
short exact. Natural additive section presentations give the assumed continuous bundle
transitions; the scalar compatibility is already part of each module morphism.
(8) Apply the short-exact-complex distinguished triangle to complexes in degree zero.
Exact products identify the localized product and its actual projections with the
ordinary derived product (step 4). The middle map is exactly 1-s: its composite with
projection k is pr_k-t_k pr_{k+1}; uniqueness in the product universal property identifies
it. No uniform Mittag--Leffler condition, surjective transition, or Stonean base is used.
Empty bases, zero fibres and varying fibre cardinalities are allowed. -/
theorem relativeFiniteBundle_roos
    (P : Profinite.{u}) (T : Type v) [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T]
    [HasDerivedCategory.{w} (SheafOfModules.{max u v + 1} (relativeContinuousRing P T))]
    (M : ℕᵒᵖ ⥤ SheafOfModules.{max u v + 1} (relativeContinuousRing P T))
    (E : ℕ → FiniteAbelianBundle P)
    (hE : ∀ n : ℕ, Nonempty ((E n).SectionPresentation (M.obj (op n)))) :
    ∃ hz : Pi.lift (fun n : ℕ ↦ limit.π M (op n)) ≫
        towerTransitionEndomorphism
          (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op) = 0,
      (ShortComplex.mk (Pi.lift (fun n : ℕ ↦ limit.π M (op n)))
        (towerTransitionEndomorphism
          (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)) hz).ShortExact ∧
      Nonempty (IsLimit (Fan.mk
        ((DerivedCategory.singleFunctor _ 0).obj (∏ᶜ fun n : ℕ ↦ M.obj (op n)))
        (fun n : ℕ ↦ (DerivedCategory.singleFunctor _ 0).map
          (Pi.π (fun n : ℕ ↦ M.obj (op n)) n)))) ∧
      ∃ δ : (DerivedCategory.singleFunctor _ 0).obj (∏ᶜ fun n : ℕ ↦ M.obj (op n)) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj (limit M))⟦(1 : ℤ)⟧,
        Triangle.mk
          ((DerivedCategory.singleFunctor _ 0).map
            (Pi.lift (fun n : ℕ ↦ limit.π M (op n))))
          ((DerivedCategory.singleFunctor _ 0).map (towerTransitionEndomorphism
            (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op))) δ ∈
          distTriang (DerivedCategory
            (SheafOfModules.{max u v + 1} (relativeContinuousRing P T))) := by
  let A := SheafOfModules.{max u v + 1} (relativeContinuousRing P T)
  let K := fun n : ℕ ↦ M.obj (op n)
  let t := towerProductShift (K := K) (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)
  have ht (n : ℕ) : t ≫ Pi.π K n =
      Pi.π K (n + 1) ≫ M.map (homOfLE (Nat.le_succ n)).op := Pi.lift_π _ _
  let hz := Fan.IsLimit.lift_π_comp_one_sub_eq_zero (productIsProduct K) t ht
    (limit.cone M)
  let S := ShortComplex.mk _ _ hz
  have hk := Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct K) t ht (limit.isLimit M)
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := relativeFiniteBundle_roos_epi P T M E hE
    exact { exact := S.exact_of_f_is_kernel hk }
  refine ⟨hz, hS, ?_, hS.singleδ, hS.singleTriangle_distinguished⟩
  have : IsGrothendieckAbelian.{max u v + 1} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses _ (relativeContinuousRing P T)
  have : HasExactLimitsOfShape (Discrete (ULift.{max u v + 1} ℕ)) A :=
    relativeContinuousRing_exact_products P T _
  have : HasExactLimitsOfShape (Discrete ℕ) A :=
    HasExactLimitsOfShape.of_domain_equivalence A (Discrete.equivalence Equiv.ulift)
  have : PreservesLimitsOfShape (Discrete ℕ) ((CochainComplex.singleFunctors A).functor 0) :=
    inferInstanceAs (PreservesLimitsOfShape _ (HomologicalComplex.single A _ 0))
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.singleFunctor A 0) :=
    preservesLimitsOfShape_of_natIso (F := (CochainComplex.singleFunctors A).functor 0 ⋙
      DerivedCategory.Q)
      ((SingleFunctors.evaluation _ _ 0).mapIso
        (DerivedCategory.singleFunctorsPostcompQIso A)).symm
  exact ⟨isLimitFanMkObjOfIsLimit (DerivedCategory.singleFunctor A 0) K _
    (productIsProduct K)⟩

end Profinite
