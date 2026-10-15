/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.SingleHomology
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Derived Hom from a locally finite free module on a ringed site

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, specialized to P[0]
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).

The degree-zero formulation below is applied to every shifted bounded-below complex.
Thus H⁰ RΓ(P∨ ⊗ K[n]) is Hⁿ RΓ(P∨ ⊗ K), including negative n. The cycle normalization
specifies evaluation, rather than only asserting the existence of abstract group isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

/-- The termwise tensor functor with P∨. Source: Stacks, Tag 08JJ
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeDualTensor
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  letI := SheafOfModules.monoidalCategory R
  MonoidalCategory.tensorLeft (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _))

/-- The tensor map induced contravariantly by p and covariantly by f.
Source: Stacks, Tag 08JJ (blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def locallyFreeDualTensorMap
    (P P' M N : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (p : P' ⟶ P) (f : M ⟶ N) :
    (locallyFreeDualTensor J R P).obj M ⟶ (locallyFreeDualTensor J R P').obj N :=
  letI := SheafOfModules.monoidalCategory R
  MonoidalCategory.tensorHom (SheafOfModules.homObjMap (R := R) p (𝟙 (SheafOfModules.unit _))) f

/-- Global sections as Hom from the unit module. Source: Stacks, Tag 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeSections :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit _))

/-- Global cochains after termwise tensor by P∨. Source: Stacks, Tag 08JJ
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable abbrev locallyFreeTensorSections
    (P : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
        CochainComplex AddCommGrpCat.{u} ℤ :=
  ((locallyFreeDualTensor J R P) ⋙ locallyFreeSections J R).mapHomologicalComplex (.up ℤ)

/-- Evaluation of a global section of P∨ ⊗ N, giving a map P → N.
Source: Stacks, Tag 08JJ (blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def locallyFreeEvaluate
    (P N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (z : SheafOfModules.unit _ ⟶ (locallyFreeDualTensor J R P).obj N) : P ⟶ N :=
  letI := SheafOfModules.monoidalCategory R
  (ρ_ P).inv ≫ P ◁ z ≫
    (α_ P (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _)) N).inv ≫
    ((SheafOfModules.tensorHomEquiv P (SheafOfModules.homObj (R := R) P (SheafOfModules.unit _))
      (SheafOfModules.unit _)).symm (𝟙 _)) ▷ N ≫ (λ_ N).hom

variable [HasDerivedCategory.{w} (ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]

/-- The canonical ordinary-to-derived global cohomology map.
Source: Stacks, Tags 0A8Z and 08JA
(blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom). -/
noncomputable def locallyFreeSectionsComparison
    (K : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (((locallyFreeSections J R).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ⟶
      (ringedSiteZerothHypercohomology J R).obj (DerivedCategory.Q.obj K) := by
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  let Γ := locallyFreeSections J R
  let G := Γ.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0
  let a : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor :=
    (Functor.isoWhiskerRight (Γ.mapHomotopyCategoryFactors (.up ℤ))
      DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u})).inv ≫
    Functor.whiskerLeft q Γ.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
      Γ.rightDerivedFunctor).hom
  exact ((Functor.isoWhiskerLeft G
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0)).inv ≫
    Functor.whiskerRight a Hd).app K

set_option maxHeartbeats 800000 in
-- Repeated derived categories and the cycle normalization need extra elaboration steps.
set_option synthInstance.maxHeartbeats 100000 in
-- The signature repeatedly elaborates the derived Hom and tensor categories.
/-- The evaluation-induced derived Hom formula, in degree zero on all shifts.
Source: Stacks, Tag 08JJ (blueprint: lem-weil-pbc-ringed-site-locally-free-derived-hom).

Proof:
1. On a covering trivializing P with finite, possibly varying ranks, evaluate a dual basis.
   This identifies P∨ ⊗ N with Hom(P,N); rank zero gives the zero map between zero objects.
   Local bijectivity gives the global sheaf isomorphism. Slice restriction is exact and
   finite sums are exact, so both functors are exact and preserve quasi-isomorphisms.
2. Resolve a bounded-below K by a bounded-below injective complex I. Tensor with P∨ is
   Hom(P,-). This preserves K-injectives: its left adjoint P ⊗ - is exact, so the
   tensor-Hom adjunction sends the acyclic Hom test to an acyclic Hom test. Thus its
   global sections compute the right derived global sections of P∨ ⊗ K. To compare
   with the stipulated injective computation, resolve this bounded-below K-injective
   tensor complex again by a bounded-below degreewise injective complex. The resulting
   quasi-isomorphism between K-injectives is a homotopy equivalence. Global sections
   preserve those homotopy equations, so both computations give the same cohomology.
3. Global degree-zero cycles are maps P → I⁰ killed by the differential. Boundaries are
   maps factoring through d : I⁻¹ → I⁰. These are exactly chain maps P[0] → I modulo
   homotopy. K-injectivity identifies them with derived morphisms. The normalization
   below says precisely that this identification uses evaluation on a cycle.
4. Precomposition in P and postcomposition in K commute with evaluation; the displayed
   naturality equation follows. Quasi-isomorphisms become invertible on both sides,
   so this also gives naturality for derived morphisms and independence of resolution.
5. Apply the same formula to K[n]. Tensor commutes termwise with shift, including its
   sign (-1)^n, and K-injective resolutions remain K-injective after shift. This is
   exactly the stated integer-degree formula and its compatibility with shifts.
-/
theorem locallyFree_derivedHom :
    ∃ e : ∀ (P : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (_ : P.IsFiniteLocallyFree)
      (K : CochainComplex (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
      (_ : CochainComplex.plus _ K),
      ((DerivedCategory.singleFunctor _ 0).obj P ⟶ DerivedCategory.Q.obj K) ≃+
        (ringedSiteZerothHypercohomology J R).obj
          (DerivedCategory.Q.obj
            (((locallyFreeDualTensor J R P).mapHomologicalComplex (.up ℤ)).obj K)),
      (∀ (P P' : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (hP : P.IsFiniteLocallyFree) (hP' : P'.IsFiniteLocallyFree) (p : P' ⟶ P)
        (K L : CochainComplex (ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (hK : CochainComplex.plus _ K) (hL : CochainComplex.plus _ L) (f : K ⟶ L)
        (t : ((locallyFreeDualTensor J R P).mapHomologicalComplex (.up ℤ)).obj K ⟶
          ((locallyFreeDualTensor J R P').mapHomologicalComplex (.up ℤ)).obj L),
        (∀ i : ℤ, t.f i =
          locallyFreeDualTensorMap J R P P' (K.X i) (L.X i) p (f.f i)) →
        ∀ a : (DerivedCategory.singleFunctor _ 0).obj P ⟶ DerivedCategory.Q.obj K,
          e P' hP' L hL
            ((DerivedCategory.singleFunctor _ 0).map p ≫ a ≫ DerivedCategory.Q.map f) =
          (ringedSiteZerothHypercohomology J R).map (DerivedCategory.Q.map t)
            (e P hP K hK a)) ∧
      (∀ (P : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (hP : P.IsFiniteLocallyFree)
        (K : CochainComplex (ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (hK : CochainComplex.plus _ K) (_ : K.IsKInjective)
        (z : ((locallyFreeTensorSections J R P).obj K).cycles 0)
        (f : (CochainComplex.singleFunctor _ 0).obj P ⟶ K),
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).inv ≫ f.f 0 =
          locallyFreeEvaluate J R P (K.X 0)
            ((((locallyFreeTensorSections J R P).obj K).iCycles 0) z) →
        e P hP K hK (DerivedCategory.Q.map f) =
          locallyFreeSectionsComparison J R
            (((locallyFreeDualTensor J R P).mapHomologicalComplex (.up ℤ)).obj K)
            ((((locallyFreeTensorSections J R P).obj K).homologyπ 0) z)) := by
  sorry

end CategoryTheory
