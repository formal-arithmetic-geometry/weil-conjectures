/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductionsStatement
public import WeilConjectures.AlgebraicGeometry.Embedded.EmbeddedIntegralResidueTransport
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteResidueTor
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCriterion
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre

/-!
# Residue reduction controls integral Tor amplitude

Source:
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-residue-tor.md
Place: Complete statement, with the standing field/scheme/coefficient conventions made explicit; no
change to its objects, hypotheses or conclusions.
(blueprint: lem-coef-integral-residue-tor).

The statement uses the intrinsic condensed coefficient ring and the canonical derived
extension of scalars to each finite quotient.  The proof is postponed: the residue
cohomology interval is transported through the quotient tensor, the finite uniformizer
filtration gives the same interval at every level, and the integral criterion identifies
bounded constructibility with finite Tor amplitude.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private noncomputable def quotientComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.val)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.val))
    (n : ℕ) : integralQuotient ℓ E.val π n ≃+*
      Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) n := by
  let F := ULift.{u} E.val
  let e := integerLiftEquiv ℓ E
  have hd := (Padic.extension_integers_dvr ℓ F
    (Padic.coefficientExtensionAbsoluteValue ℓ F)
    (spectralNorm_extends (K := ℚ_[ℓ]) (L := F))).choose_spec.choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers ℓ F) := hd.2.2.2.1
  have hm : Padic.coefficientExtensionMaximalIdeal ℓ F =
      IsLocalRing.maximalIdeal (Padic.coefficientExtensionIntegers ℓ F) :=
    IsLocalRing.eq_maximalIdeal hd.2.2.2.2.1
  have hg : Ideal.span {Padic.coefficientExtensionUniformizer ℓ F} =
      Padic.coefficientExtensionMaximalIdeal ℓ F :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  apply Ideal.quotientEquiv _ _ e
  rw [Padic.coefficientExtensionIdeal, Ideal.map_pow, hπ, hg, hm]
  exact congrArg (fun I ↦ I ^ n) (IsLocalRing.map_ringEquiv_maximalIdeal e).symm

private noncomputable def quotientRingComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.val)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.val))
    (n : ℕ) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
    letI := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
    Profinite.continuousMapRingSheaf.{u} (integralQuotient ℓ E.val π n) ≅
      DerivedNakayama.quotientRingSheaf ℓ (ULift.{u} E.val) n := by
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.val)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.val) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := quotientComparison ℓ E π hπ n
  have hc : Continuous e := by
    apply isQuotientMap_quot_mk.continuous_iff.mpr
    exact continuous_quot_mk.comp (integerLiftHomeo ℓ E).continuous_toFun
  have hi : Continuous e.symm := by
    apply isQuotientMap_quot_mk.continuous_iff.mpr
    exact continuous_quot_mk.comp (integerLiftHomeo ℓ E).continuous_invFun
  let forward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, integralQuotient ℓ E.val π n) →+*
        ULift.{u + 1} C(S.unop, Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) n) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous _ hc).comp ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) n) →+*
        ULift.{u + 1} C(S.unop, integralQuotient ℓ E.val π n) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous _ hi).comp ULift.ringEquiv.toRingHom)
  refine
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S x
    apply ULift.ext
    ext t
    exact e.symm_apply_apply _
  · ext S x
    apply ULift.ext
    ext t
    exact e.apply_symm_apply _

/-- Bounds on the first residue reduction give a common Tor interval at every finite
coefficient level, and identify the intrinsic bounded constructible and finite-Tor
subcategories for the integral condensed coefficient ring.

Source:
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-residue-tor.md
Place: Complete statement, with the standing field/scheme/coefficient conventions made explicit; no
change to its objects, hypotheses or conclusions.
(blueprint: lem-coef-integral-residue-tor).

Implementation: `quotientComparison` and `quotientRingComparison` construct the
coefficient identifications at every exponent. The square with the actual reduction
maps is checked before applying `derivedResidueSquare`. The integral criterion and
`integralCriterionReductions` supply constructibility, and
`integral_finite_residue_normalization` and `integral_finite_residue_tor` implement
the associativity and residue-test steps below. Exact monoidal scalar restriction
preserves the first homology interval and reflects the resulting Tor interval.
The integral criterion itself gives the final equality over the integral ring.

Proof (the landed six-step split):

1. The blueprint opens with the canonical balanced coefficient-tensor associativity identity:
$K_n\otimes^L_{(A_{E,n})_X}\kappa_X\simeq K\otimes^L_{R_X}\kappa_X=K_1$, where $A_{E,n}=R/(\pi_E^n)$
and $\kappa=A_{E,1}$. The coefficient maps compose to the first quotient; on tensor representatives
the balancing map is $(x\otimes u)\otimes v\mapsto x\otimes uv$, with inverse $x\otimes
v\mapsto(x\otimes1)\otimes v$. This records the opening associativity calculation, without the
former scalar-mate construction.

2. For the constructibility sentence, the integral criterion [sk-prop-integral-criterion],
(1)$\Rightarrow$(2), supplies derived completeness and bounded constructibility of $K_1$ from $K\in
D^b_c(X,R)$. For Noetherian $X$, [det-prop-integral-criterion-reductions] therefore supplies bounded
constructibility of every $K_n$. This is the reduction-constructibility step of the blueprint, not
an identification of a cohomological interval with a Tor interval. Its Noetherian hypothesis is the
standing separated finite-type-over-a-field setting.

3. Fix $n\ge1$ and write $A=A_{E,n}$. Since $A$ is finite discrete,
[lem-sf-module-object-ordinary-coefficient-equivalence] identifies its pulled-back condensed
coefficient ring with the constant ring sheaf on $X_{\mathrm{pro\acute et}}$, and preserves relative
derived tensors and Tor intervals. Use this ordinary module-sheaf presentation, on the same site.
Choose a complex representing $K_n$ and a K-flat resolution $P$ with flat terms by
[lem-pc-kflat-resolution]. By [def-weil-derived-tensor], $K_n\otimes_A^L M$ is represented by the
termwise tensor $P\otimes_A M$ for every module sheaf $M$ in degree zero. Step 1 and the hypothesis
on $K_1$ therefore give $H^i(P\otimes_A\kappa_X)=0$ whenever $i<a$ or $b<i$.

4. Let $r$ be the image of $\pi_E$ in $A$. The DVR and uniformizer assertions of
[lem-weil-l-adic-extension-integers-dvr] give $r^n=0$ and $A/(r)=\kappa$ a field; thus $(r)$ is
maximal, including when $n=1$ and $r=0$. For any $A_X$-module sheaf $N$ killed by $r$, apply
[lem-sf-proetale-residue-module-tensor-homology] to $T=X$, this ring $A$, the complex $P$, the
residue unit $\kappa_X$, and $N$. Its conclusion is $H^i(P\otimes_A N)=0$ for each $i$ outside
$[a,b]$, by the residue vanishing from step 3. This lemma is stated on the small pro-etale site for
arbitrary schemes and complexes; neither a finite-field datum nor constructibility is a hypothesis.

5. For any $A_X$-module sheaf $M$, put $M_j=\operatorname{im}(r^j:M\to M)$ for $0\le j\le n$. Then
$M_0=M$, $M_n=0$, and $G_j=M_j/M_{j+1}$ is killed by $r$, since $rM_j\subseteq M_{j+1}$. Each
sequence $0\to M_{j+1}\to M_j\to G_j\to0$ is short exact. Flatness of $P^q$ means its tensor functor
is exact [def-pc-flat-sheaf-modules]; applying the short-exact image assertion of
[lem-weil-pbc-exact-functor-ses-triangle-image] to this functor in every degree $q$ gives a
degreewise short exact sequence $0\to P\otimes_A M_{j+1}\to P\otimes_A M_j\to P\otimes_A G_j\to0$.
For each $i$ outside $[a,b]$, [lem-weil-pbc-complex-ses-homology-long-exact] gives the exact segment
$H^i(P\otimes M_{j+1})\to H^i(P\otimes M_j)\to H^i(P\otimes G_j)$. The last term is zero by step 4.
Descending induction from $M_n=0$ therefore makes the middle term zero, without enlarging the
interval. By step 3 this is the vanishing of $H^i(K_n\otimes_A^L M)$ for every $M$, hence precisely
Tor amplitude $[a,b]$ [def-weil-finite-tor-amplitude]. The same $[a,b]$ works for every $n$.

6. For the final equality over $R_X$ itself, apply [sk-prop-integral-criterion],
(1)$\Leftrightarrow$(4), to the Noetherian scheme $X$. Its two conditions say exactly $K\in
D^b_c(X,\mathcal O_E)$ and $K\in D^b_{ctf}(X,\mathcal O_E)$; thus it supplies the forward inclusion
for every $K$, not merely a condition on reductions. The reverse inclusion is also part of
[sk-def-sfb-constructible], which defines the finite-Tor category as a full subcategory of $D^b_c$.
Since both are full subcategories of the same ordinary derived category, equality of these object
conditions gives the stated equality of full subcategories. No identification with site-perfectness
is made.
-/
theorem integralResidueTor
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : ℓ ≠ p)
    (k : Type u) [Field k] [CharP k p] (_hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : {π : PadicAlgCl.integers ℓ E.1 //
      Ideal.span ({π} : Set (PadicAlgCl.integers ℓ E.1)) =
        IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)}) :
    letI : MonObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) :=
      Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
        (Profinite.padicIntegersCondensedRing ℓ E.1)
    letI : IsCommMonObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) :=
      Profinite.isCommMonObj_padicIntegersRingObj ℓ E.1
    letI (n : ℕ) : MonObj (integralQuotientRingObj ℓ E.1 π.1 n) :=
      Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
        (Profinite.continuousMapRingSheaf (integralQuotient ℓ E.1 π.1 n))
    letI (n : ℕ) : IsCommMonObj (integralQuotientRingObj ℓ E.1 π.1 n) :=
      Profinite.isCommMonObj_continuousMapRingObj (integralQuotient ℓ E.1 π.1 n)
    letI : MonObj (condensedRingObj
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) X.left) :=
      ((upperStarFromPoint X.left).mapMon.obj
        (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.1))).mon
    letI : IsCommMonObj (condensedRingObj
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) X.left) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X.left)
    letI (n : ℕ) : MonObj (condensedRingObj
        (integralQuotientRingObj ℓ E.1 π.1 n) X.left) :=
      ((upperStarFromPoint X.left).mapMon.obj
        (Mon.mk (integralQuotientRingObj ℓ E.1 π.1 n))).mon
    letI (n : ℕ) : IsCommMonObj (condensedRingObj
        (integralQuotientRingObj ℓ E.1 π.1 n) X.left) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X.left)
    (∀ (K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left) K →
      ∀ a b : ℤ, a ≤ b →
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((CategoryTheory.Mod.extendScalars
            (integralReductionCoefficientMap X.left ℓ E.1 π.1 1)).leftDerivedFunctor.obj K) →
        ∀ n : ℕ, 1 ≤ n →
          _root_.DerivedCategory.torAmplitudeIn
            (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
              (condensedRingObj (integralQuotientRingObj ℓ E.1 π.1 n) X.left)) a b
            ((CategoryTheory.Mod.extendScalars
              (integralReductionCoefficientMap X.left ℓ E.1 π.1 n)).leftDerivedFunctor.obj K)) ∧
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left) =
        condensedConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ E.1) X.left := by
  classical
  let : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let d₀ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (integerRingSheafIso ℓ E)
  have : IsMonHom d₀.hom := Sheaf.isMonHom_sheafCompose_map _
    (integerRingSheafIso ℓ E).hom
  have : IsMonHom d₀.inv := Sheaf.isMonHom_sheafCompose_map _
    (integerRingSheafIso ℓ E).inv
  let d := (upperStarFromPoint X.left).mapIso d₀
  have : IsMonHom d.hom := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X.left).map d₀.hom))
  have : IsMonHom d.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X.left).map d₀.inv))
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) d.inv
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso d.inv).isEquivalence_functor
  have : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  have hc (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X.left)))
      (hK : boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X.left) K) :
      constantModelBoundedConstructible
        (DerivedNakayama.integerRing ℓ (ULift.{u} E.val)) X.left
        (F.mapDerivedCategory.obj K) := by
    obtain ⟨e⟩ := integralCoefficientIso ℓ E
    have hK' : constantModelBoundedConstructible
        (Profinite.padicIntegersRingObj ℓ E.val) X.left K := by
      refine ⟨hK.1, fun q ↦ ?_⟩
      let M := (DerivedCategory.homologyFunctor _ q).obj K
      let φ := coefficientMap e.hom.hom X.left
      have ht : IsConstructibleModuleObject
          (condensedRingObj (integralCondensedRing ℓ (ULift.{u} E.val)) X.left)
          ((Mod.comap φ).obj M) := by
        obtain ⟨T, hT⟩ := hK.2 q
        refine ⟨T, fun a ↦ ?_⟩
        let H := AlgebraicGeometry.ProEtale.upperStar Ab (T.immersion a)
        exact lfp_of_iso (lfp_comap (H.map φ) (hT a))
          ((H.mapModComapIso φ).app M).symm
      exact (constantModel_comap_iff e.hom.hom X.left M).mp
        ((integralLfpConstantModelComparison ℓ (ULift.{u} E.val) X.left _).mp ht)
    refine ⟨F.bounded_mapDerivedCategory_obj hK'.1, fun q ↦ ?_⟩
    exact AlgebraicGeometry.ProEtale.constructible_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
      ((constantModel_comap_iff d₀.inv X.left _).mpr (hK'.2 q))
  constructor
  · intro K hK a b hab hb n hn
    let r₀ (j : ℕ) := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
        (quotientRingComparison ℓ E π.val π.property j)
    have hrh (j : ℕ) : IsMonHom (r₀ j).hom :=
      Sheaf.isMonHom_sheafCompose_map _
        (quotientRingComparison ℓ E π.val π.property j).hom
    have hri (j : ℕ) : IsMonHom (r₀ j).inv :=
      Sheaf.isMonHom_sheafCompose_map _
        (quotientRingComparison ℓ E π.val π.property j).inv
    let r (j : ℕ) := (upperStarFromPoint X.left).mapIso (r₀ j)
    have hr (j : ℕ) : IsMonHom (r j).hom := inferInstanceAs
      (IsMonHom ((upperStarFromPoint X.left).map (r₀ j).hom))
    have hi (j : ℕ) : IsMonHom (r j).inv := inferInstanceAs
      (IsMonHom ((upperStarFromPoint X.left).map (r₀ j).inv))
    let G (j : ℕ) := Mod.comap
      (D := Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (r j).inv
    have he (j : ℕ) : (G j).IsEquivalence :=
      (Mod.comapEquivalenceOfIsIso (r j).inv).isEquivalence_functor
    have hf (j : ℕ) : (G j).PreservesFlat :=
      Functor.preservesFlat_of_isEquivalence (G j)
    have hs (j : ℕ) : d.hom ≫
        AdicCompletion.quotient ℓ (ULift.{u} E.val) X.left j =
        integralReductionCoefficientMap X.left ℓ E.val π.val (j + 1) ≫
          (r (j + 1)).hom := by
      change (upperStarFromPoint X.left).map d₀.hom ≫
          (upperStarFromPoint X.left).map _ =
        (upperStarFromPoint X.left).map _ ≫ (upperStarFromPoint X.left).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    let comparison (j : ℕ) := derivedResidueSquare X.left d (r (j + 1))
      (integralReductionCoefficientMap X.left ℓ E.val π.val (j + 1))
      (AdicCompletion.quotient ℓ (ULift.{u} E.val) X.left j) (hs j)
    have hb' : DerivedCategory.homologyConcentratedIn a b
        ((AdicCompletion.derivedReduction ℓ (ULift.{u} E.val) X.left 0).obj
          (F.mapDerivedCategory.obj K)) := by
      exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
        ((comparison 0).app K)
        ((G 1).homologyConcentratedIn_mapDerivedCategory_obj hb)
    have hK' := hc K hK
    have hcriterion := (internal_integral_residue_criterion ℓ
      (ULift.{u} E.val) X.left).1 _ |>.mp hK'
    have hred := ((integralCriterionReductions ℓ (ULift.{u} E.val) X.left
      (F.mapDerivedCategory.obj K) hcriterion.1).mp hcriterion.2.1).1
    have ht := integral_finite_residue_tor ℓ (ULift.{u} E.val) X.left (n - 1)
      ((AdicCompletion.derivedReduction ℓ (ULift.{u} E.val) X.left (n - 1)).obj
        (F.mapDerivedCategory.obj K)) (hred (n - 1)) a b hab (by
          obtain ⟨en⟩ := integral_finite_residue_normalization ℓ (ULift.{u} E.val)
            X.left (F.mapDerivedCategory.obj K) (n - 1)
          intro q hq
          exact (((homology_bounds _ a b).mp hb') q hq).of_iso
            ((DerivedCategory.homologyFunctor _ q).mapIso en))
    have hnn : n - 1 + 1 = n := by omega
    rw [← hnn]
    apply DerivedCategory.torAmplitudeIn_of_torAmplitudeIn_mapDerivedCategory_obj
      (G (n - 1 + 1))
    exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
      ((comparison (n - 1)).app K).symm ht
  · funext K
    apply propext
    constructor
    · intro hK
      refine ⟨hK, ?_⟩
      have ht := (congrFun (internal_integral_residue_criterion ℓ
        (ULift.{u} E.val) X.left).2 (F.mapDerivedCategory.obj K)).mp (hc K hK)
      obtain ⟨a, b, ht⟩ := ht.2
      exact ⟨a, b, DerivedCategory.torAmplitudeIn_of_torAmplitudeIn_mapDerivedCategory_obj
        F ht⟩
    · exact fun h ↦ h.1

end AlgebraicGeometry.ProEtale.CondensedRing
