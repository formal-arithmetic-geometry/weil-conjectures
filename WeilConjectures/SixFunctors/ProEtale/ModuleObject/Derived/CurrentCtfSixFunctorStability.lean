/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompatibleRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The six operations on constructible finite-Tor complexes in the current field scope

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
sec-the-remaining-operations/sk-thm-sf-ctf-stability/_section.md and
sk-thm-sf-ctf-stability.proof.md; standing field convention in
part-six-operations/prose-P1-01.md, final paragraph, and
sec-introduction/sec-conventions/prose-01-09.md (blueprint: sk-thm-sf-ctf-stability).

The compact-support functor is the chosen compactification composite. Its exceptional
right adjoint is characterized by the actual localizing adjunction. Every category is a
full subcategory of the ordinary uncompleted module-object derived category.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- All six operations preserve bounded constructible finite-Tor complexes, with the
three adjunctions restricting by the original natural Hom bijections. The existential
exceptional adjunction is a right adjoint of the specified compactification functor,
so uniqueness identifies it with the adjunction of sk-prop-sf-existence.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors/
sec-the-remaining-operations/sk-thm-sf-ctf-stability/_section.md and the four
paragraphs of sk-thm-sf-ctf-stability.proof.md
(blueprint: sk-thm-sf-ctf-stability).

Proof (the nine steps of the DAG node):
1. The finite or algebraically closed base field has \operatorname{cd}_\ell(k)\leq1 by
   [sk-lem-base-field-cd]; this verifies the finite-CD premise of the specified exceptional
   adjunction, rather than adding it to the proposition. A field is Noetherian (its only ideals
   are zero and the unit ideal), hence every standing finite-type scheme is Noetherian and qcqs.
   If a_X=a_Yf are structure maps, separated and locally-finite-type cancellation give that f is
   separated and locally of finite type; quasi-compactness of X and quasi-separatedness of Y
   give that f is quasi-compact, hence finite type. Thus the chosen compactification and every
   preservation theorem below have their required hypotheses.
2. For finite A, [sk-lem-sf-flat-model] supplies bounded flat constructible models of the
   inputs; their terms have finite projective constant models on strata. Pullback takes a
   constant scalar model on a stratum to the same scalar model on its inverse-image stratum. The
   existing unbounded-pullback theorem gives precisely preservation of \Dctf by this ambient
   Lf^* for every admissible coefficient. Its pullback is the ordinary coefficient-compatible
   inverse image, which is exact by [sk-prop-sfb-cartesian-coefficients]. This proves the
   pullback clause, including preservation of boundedness. No finite-Tor assertion about
   individual cohomology sheaves is used.
3. For finite A, bounded constructibility of K\otimes^{\mathbf L}L is
   [lem-sfb-admissible-tensor-constructibility]. To verify finite Tor amplitude, let K,L have
   intervals [a,b],[c,d] and let N be any degree-zero module. Then L\otimes^{\mathbf L}N has
   cohomology in [c,d]. Apply the lower and upper tensor-bound lemmas to K\otimes^{\mathbf
   L}(L\otimes^{\mathbf L}N): it vanishes below a+c and above b+d. Derived associativity
   identifies this with (K\otimes^{\mathbf L}L)\otimes^{\mathbf L}N. For \mathcal O_E use
   [sk-lem-int-tensor] for bounded constructibility; for E,\Qlb use
   [lem-sfb-dc-tensor-preserves]. The equality \Dbc=\Dctf on the qcqs schemes of Step 1 then
   gives finite Tor amplitude. The cases \mathbf Z_\ell,\mathbf Q_\ell are E=\mathbf Q_\ell.
   Thus tensor preserves \Dctf for all six coefficients.
4. For a locally closed a:S\hookrightarrow X, factor a=i u through its scheme-theoretic image.
   The coefficient-extension theorem gives exact a_!=i_*u_! and H^n(a_!K)=a_!H^n(K). Open
   extension by zero and closed direct image preserve constructibility, applying the open/closed
   theorem to the two complementary pairs. Hence a_!K is bounded constructible. For a
   degree-zero module N, the immersion projection formula identifies (a_!K)\otimes^{\mathbf L}N
   with a_!(K\otimes^{\mathbf L}a^*N). Coefficient-compatible a^* is exact, so a^*N is degree
   zero; exactness of a_! preserves the vanishing outside the Tor interval of K. This proves
   extension-by-zero preservation in paragraph 1 for every coefficient.
5. For a quasi-compact open j, [sk-cor-sf-direct-image-ctf] gives Rj_* preservation of \Dctf for
   arbitrary finite commutative \ell-primary A. For \mathcal O_E,E,\Qlb,
   [sk-prop-open-coefficients] gives bounded constructibility of Rj_*K;
   [lem-integral-ctf-equals-bc] upgrades this to \Dctf. This applies both to source and target,
   which are qcqs by Step 1. Again E=\mathbf Q_\ell includes the two remaining coefficients.
   Proper Rp_* preserves \Dctf by [sk-thm-sfb-proper-base-change].
6. Choose the standing compactification f=pj with quasi-compact open j:X\hookrightarrow\bar X
   and proper p:\bar X\to Y, all within the setting. Derived direct-image composition gives
   Rf_*\simeq Rp_*Rj_*, and the prescribed compactification lower-shriek definition gives
   Rf_!=Rp_*D(j_!). Step 5 handles the proper and open direct images and Step 4 handles D(j_!),
   proving preservation by both composites. Clause (4) of [sk-thm-existence] supplies
   preservation by the specified localizing right adjoint f^!. This is the right adjoint of the
   same chosen compactification functor; finite-CD is supplied by Step 1, and no later duality
   or scalar-comparison theorem enters.
7. Fix L\in\Dctf(X,\Lambda). By contravariant exactness of the native relative internal Hom, the
   property Q(K):\cHom_X(K,L)\in\Dctf(X,\Lambda) is stable under shifts and cones: the image
   triangle is distinguished and its other two vertices are in the intersection of bounded
   constructibility and finite Tor amplitude. These two properties are triangulated by the cited
   bounded-constructibility and Tor-amplitude statements. By
   [lem-sfb-ctf-locally-closed-perfect-generation], it therefore suffices to prove Q(a_!P) for a
   locally closed immersion and a locally constant perfect scalar complex P. This is the
   finite-stratification/stupid-filtration reduction of paragraph 3, applied to whole complexes,
   not to potentially infinite-Tor cohomology sheaves.
8. For such a generator use only the formula clause of [det-thm-sf-ctf-stability-internal-hom]:
   \cHom_X(a_!P,L)\simeq Ra_*\cHom_S(P,a^!L)\simeq Ra_*(P^\vee\otimes^{\mathbf L}a^!L). Its
   formula is the tensor--Hom/projection-formula calculation of paragraph 3; its overall
   preservation conclusion is not used. The locally constant perfect dual lemma makes P^\vee
   bounded constructible, and the perfect dual Tor-bound lemma supplies finite Tor amplitude.
   Step 6 gives a^!L\in\Dctf, Step 3 gives the tensor in \Dctf, and Steps 5--6 give the Ra_*
   image in \Dctf. Thus Q(a_!P), and the finite-cone induction in Step 7 gives internal-Hom
   preservation for every K\in\Dctf.
9. Use the specified ambient Lf^*\dashv Rf_* and relative tensor--internal-Hom adjunctions,
   together with Rf_!\dashv f^! on the localizing closures. For tensor write the left adjoint in
   the blueprint order -\otimes^{\mathbf L}K, transporting the K\otimes^{\mathbf L}- adjunction
   through the native tensor braiding. The ringed-site closed symmetric monoidal theorem
   supplies this braiding and the right-factor adjunction; the internal-module/ringed-site
   comparison identifies its internal Hom and evaluation with the specified native ones. Thus
   the internal Hom remains \cHom(K,-). Steps 2--8 put all six images in the required full
   subcategories. Restrict their object and morphism assignments; fullness identifies each
   restricted Hom set with its ambient Hom set, so the same natural Hom bijections are
   adjunctions there. Their units and counits are obtained from the same identities by the same
   bijections. Taking identity inclusion comparisons satisfies exactly
   [def-sp-compatible-adjunction-restriction]. -/
theorem ctfSixFunctorStabilityFiniteOrAlgClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    (∀ K : ConstantModelConstructibleFiniteTor Λ Y.left,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((upperStar Λ f.left).leftDerivedFunctor.obj K.obj)) ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ K L : ConstantModelConstructibleFiniteTor Λ X.left,
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((derivedTensor Λ X.left).obj K.obj).obj L.obj) ∧
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        (((derivedHom Λ X.left).obj (op K.obj)).obj L.obj)) ∧
    WeilConjectures.podCompatibleRestriction (derivedUpperStarLowerStarAdjunction Λ f.left)
      (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι
      (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι ∧
    (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
      WeilConjectures.podCompatibleRestriction
        ((derivedTensorHomAdjunction Λ K.obj).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ _
            (_root_.DerivedCategory.braidedCategory' _) K.obj))
        (constantModelBoundedConstructible Λ X.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι
        (constantModelBoundedConstructible Λ X.left ⊓
          _root_.DerivedCategory.finiteTorAmplitude _).ι) ∧
    ∃ (h : ∀ K, localizingClosureProEtale Λ X.left K →
          localizingClosureProEtale Λ Y.left
            ((rightDerivedLowerShriekOfCompactification Λ
              (compactificationOverField f)).obj K))
      (hX : (constantModelBoundedConstructible Λ X.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) ≤ localizingClosureProEtale Λ X.left)
      (hY : (constantModelBoundedConstructible Λ Y.left ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) ≤ localizingClosureProEtale Λ Y.left),
      (∀ K : ConstantModelConstructibleFiniteTor Λ X.left,
        (constantModelBoundedConstructible Λ Y.left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
          ((rightDerivedLowerShriekOfCompactification Λ
            (compactificationOverField f)).obj K.obj)) ∧
      ∃ (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
          (localizingClosureProEtale Λ X.left).FullSubcategory)
        (adj : localizingLowerShriek Λ (compactificationOverField f) h ⊣ G),
        (∀ K : (localizingClosureProEtale Λ Y.left).FullSubcategory,
          (constantModelBoundedConstructible Λ Y.left ⊓
            _root_.DerivedCategory.finiteTorAmplitude _) K.obj →
          (constantModelBoundedConstructible Λ X.left ⊓
            _root_.DerivedCategory.finiteTorAmplitude _) (G.obj K).obj) ∧
        WeilConjectures.podCompatibleRestriction adj
          (ObjectProperty.ιOfLE hX) (ObjectProperty.ιOfLE hY) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
