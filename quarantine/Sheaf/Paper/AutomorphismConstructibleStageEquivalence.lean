/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import all Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.IsomorphismFieldTransport
import Sheaf.Paper.SimultaneousIntegralPullbackComparisons
import Sheaf.Paper.IntegralScalarPullbackCompletionNormalization
import Sheaf.Paper.IntegralAutomorphismCancellationNormalization
import Sheaf.Paper.CommonStagePullbackRepresentativeLinearity
import Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import all Sheaf.Paper.IntegralOperationsPreserveConstructible
import all Sheaf.Paper.IntegralCoefficientCompletenessTransport
import Sheaf.Paper.ProEtaleConstantModulePullbackComposition
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.SfIntegralConstructibleTriangulated
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.IntegralPullbackSystemComparison
public import Sheaf.Paper.IntegralPullbackShiftCoordinates
public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
public import Sheaf.Paper.FiniteSystemPullbackCoherence
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero

/-! # Automorphism pullback at the four constructible coefficient stages

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph, first two sentences
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).

## Main statements

- `automorphismConstructibleStage_finite`, `automorphismConstructibleStage_integral_rational`,
  and `automorphismConstructibleStage_qbar`: the four prescribed exact equivalences.
- `automorphismConstructibleStage_strata` and `automorphismConstructibleStage_reduction`:
  the specified partitions and entire quotient systems.
- The comparison constructors and coherence statements retain the actual completion,
  composition, shift, scalar extension, rationalization and common-stage comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Aut
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v r s u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped TensorProduct
local instance (priority := 5000) (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] sfIntrinsicModuleEquivalence
  HasDerivedCategory.standard integralDerivedPullback scalarReductionExistence
  scalarReductionDerivedExistence completedIntegralCoefficientSheafUnrestricted

/-- Prime-to-characteristic coefficients are invertible on each scheme in the statement.
Source: the global finite-field datum and the Weil-structures paragraph
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the cardinality of k₀ gives characteristic p, also on its algebraic closure.
The prime l is distinct from p, hence nonzero and a unit in k. Every local ring
and residue field of a k-scheme inherits this unit under its structure map. -/
theorem automorphismConstructibleStage_units
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T : Over (Spec (.of D.k))) :
    (∀ x : T.left, IsUnit (l : T.left.presheaf.stalk x)) ∧
      (∀ x : T.left, IsUnit (l : T.left.residueField x)) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  have hk : IsUnit (l : D.k) := by
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have hs (x : T.left) : IsUnit (l : T.left.presheaf.stalk x) := by
    simpa only [map_natCast] using hk.map
      (StructureSheaf.toStalk (CommRingCat.of D.k) (T.hom x) ≫ T.hom.stalkMap x).hom
  exact ⟨hs, fun x ↦ by
    simpa only [map_natCast] using (hs x).map (T.left.residue x).hom⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.hasShift ObjectProperty.commShiftι

private theorem lift_shift_component
    {B : Type*} [Category B] [HasShift B ℤ]
    (P : ObjectProperty B) [P.IsStableUnderShift ℤ]
    (H : B ⥤ B) [H.CommShift ℤ]
    (hH : ∀ K : P.FullSubcategory, P (H.obj K.obj))
    (r : ℤ) (K : P.FullSubcategory) :
    HEq (((P.lift (P.ι ⋙ H) hH).commShiftIso r).hom.app K).hom
      ((H.commShiftIso r).hom.app K.obj) := by
  let e := P.liftCompιIso (P.ι ⋙ H) hH
  have hi := Functor.CommShift.OfComp.map_iso_hom_app e r K
  simp only [e, ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Functor.commShiftIso_comp_hom_app] at hi
  simp only [Functor.commShiftIso,
    Functor.CommShift.ofHasShiftOfFullyFaithful, ObjectProperty.liftCompιIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.FullyFaithful.hasShift, hasShiftMk, shiftFunctor, Discrete.functor] at hi
  change (((P.lift (P.ι ⋙ H) hH).commShiftIso r).hom.app K).hom =
    (H.map (𝟙 (K.obj⟦r⟧)) ≫ (H.commShiftIso r).hom.app K.obj) ≫
      (shiftFunctor B r).map (𝟙 (H.obj K.obj)) ≫ 𝟙 ((H.obj K.obj)⟦r⟧) at hi
  apply heq_of_eq
  rw [H.map_id, Category.id_comp, (shiftFunctor B r).map_id] at hi
  exact hi.trans (by
    rw [Category.comp_id]
    exact Category.comp_id _)


set_option allowUnsafeReducibility true in
attribute [local irreducible] ObjectProperty.hasShift ObjectProperty.commShiftι

/-- Finite automorphism pullback preserves constructibility and every cohomological interval.
Source: Weil-structures paragraph, finite coefficient specialization
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).

Proof plan:
1. Put $G_e=e^{-1}$ with the canonical constant coefficient action. By [lem-weil-proetale-
isomorphism-inverse-image], on an object $V\to T$ this is reindexing $M(V\to T)\mapsto
M(V\xrightarrow e T)$, with inverse reindexing by $e^{-1}$. Both send covering families to
covering families. The constant-section comparison fixes every $a\in A_n$, so reindexing is
$A_n$-linear on morphisms. This exact equivalence on module sheaves induces an exact functor on
the unbounded derived categories by [lem-sf-exact-functor-derived-triangulated]. The finite
pullback prescribed in [def-weil-derived-pullback-tensor-hom] is precisely this termwise functor;
its inverse is the one for $e^{-1}$.
2. Let $M$ be a cohomology sheaf and $(S_\nu)$ a witnessing partition in [def-weil-finite-torsion-
constructibility]. Restrict the isomorphism $e$ to $e^{-1}S_\nu\xrightarrow\sim S_\nu$. Inverse
images of the finitely many locally closed constructible pieces are again such pieces, disjoint
and covering $T$. Reindexing a covering which trivializes $M|_{S_\nu}$ trivializes its inverse
image with the identical finite $A_n$-module. Thus this is the required partition. By [lem-pur-
proetale-constant-module-pullback-homology], $\mathcal H^a(F_{e,n}K)\cong e_n^*\mathcal H^a(K)$.
If the latter sheaf is zero outside $[r,s]$, so is the former; apply the same argument to $e^{-1}$
for the inverse. This proves the finite restriction to $D^b_c$ with the same interval.
3. Use [lem-weil-pbc-proetale-derived-pullback-composition] for finite compositors, with the
coefficient equations of [lem-weil-pbc-profinite-coefficient-inverse-image]. The identity is
precisely the termwise comparison of [lem-pur-proetale-derived-pullback-identity]. The module
compositor is the comparison of left adjoints to the base-change direct-image identification by
[lem-pur-proetale-module-pullback-composition]. For three maps, the two direct-image comparisons
identify either parenthesized iterated fibre product with the same fibre product, carrying its
projections identically. They therefore agree by the fibre-product universal property. Now [lem-
trf-adjoint-composition-coherence] gives associativity of these specified left-adjoint
comparisons. The identity equations follow by the same unit normalization with an identity fibre
product. The localization universal property [lem-weil-pbc-localization-universal-property]
carries these termwise equations to derived functors. Shifts reindex the same component maps.
Substituting $(e,e^{-1})$ gives the inverse-composition comparisons. For $e_Xj=je_U$, compose the
compositor for $j\circ e_U$ with the inverse compositor for $e_X\circ j$ to obtain $b$; use $i$
for $d$. Their identity, inverse and shift equations are instances of these composition equations.
4. Integrally write $B=\widehat R_T$ and let $H_e$ be ordinary module pullback along $c_e$. The
reindexing in [lem-weil-proetale-isomorphism-inverse-image] transports the $B$-module action
through $c_e$ and has inverse using $c_{e^{-1}}$: their composites act as the identity on both
sections and scalars, by the composition equation in [lem-weil-pbc-profinite-coefficient-inverse-
image]. It is therefore an exact equivalence also for these nonconstant coefficient sheaves,
preserving products, kernels and cokernels by reindexing. It induces an exact derived equivalence
by [lem-sf-exact-functor-derived-triangulated]. The strict-tower comparison of [lem-pur-integral-
ambient-operation-models] identifies $(H_eK)_n$ with $F_{e,n}K_n$ and identifies quotient
augmentations and transitions. Apply $H_e$ to a completeness Roos triangle from [def-weil-derived-
complete]: products become products, $1-s$ becomes the $1-s$ of this identified reduction tower,
and its first map remains the family of quotient maps. Thus $H_eK$ is derived complete whenever
$K$ is; the same holds for its inverse.
5. For complete $K$ the SPECIFIED ordinary-to-completed comparison is invertible by [lem-weil-
isomorphism-derived-pullback-comparison-normalization]: its factorization is
$\theta_{e,K}\kappa^e_K=H_e(u_K)$. Hence the prescribed completed $F_e$ agrees with $H_e$ through
this actual comparison. By [lem-pur-integral-ambient-operation-models], on a flat-term K-flat
representative the reduction comparison is the balanced tensor map on the entire quotient tower,
not a choice of maps between its cohomology objects. Its augmentation is the specified map, with
zero shifted-product coordinate. Consequently the resulting isomorphisms
$(F_eK)\otimes_B^L(A_n)_T\cong F_{e,n}(K_n)$ commute with quotient transitions, the finite
projections and completion units. Together with Step 2 and completeness from Step 4, the
definition [def-weil-derived-complete-integral-detailed] gives $F_eK\in D^b_c(T,R)$, preserving
the SAME uniform $[r,s]$.
6. The integral restrictions are exact inverse equivalences by Steps 4–5. They are $R$-linear: the
equation $\pi_nc_e=c_{e,n}e^{-1}\pi_n$ fixes every constant scalar $r$ at each quotient, hence its
image in $B$; on sections $H_e(rf)=rH_e(f)$. For $b,d$ use the two integral compositors of [lem-
pod-integral-pullback-composition] for $j\circ e_U=e_X\circ j$ or $i\circ e_Z=e_X\circ i$; this
supplies associativity and their finite reduction formulas. To check the full-map equations, use
[lem-pur-completed-operation-tower-substitution], which explicitly identifies the canonical
completed compositor with the limit of the adjunction-normalized WHOLE-SYSTEM compositor,
compatibly with substitution. Its normalization hypothesis holds for the reduction system of any
input $K$: take the single flat-term K-flat representative used above. Its scalar extensions $Q_m$
stay K-flat by [lem-weil-pbc-ringed-pullback-preserves-kflat] applied to the identity topos and
the quotient coefficient map. Thus $Q_m\otimes_{A_m}A_n=Q_n$ computes the transition adjoint;
multiplication of scalar factors gives its identity and cocycle equations. Step 5 identifies $K$
with its actual reconstruction. Step 3's equations then hold on the finite system maps: the two
sides have identical scalar-association components and transitions on these representatives. Apply
the total-limit functor and the substitution comparisons of the tower-substitution lemma. This
gives identity, inverse and shift equations for the actual integral maps and their completion and
reduction comparisons, without assuming that finite reductions are jointly faithful on morphisms.
7. For $E\subset L$ write $T_W$ for the COMPLETED integral scalar extension of [def-weil-integral-
scalar-extension]. For $f=e,e^{-1},i,j$ use the framework comparison
$\theta_f:T_XF_{f,E}\xrightarrow{\sim}F_{f,L}T_Y$ of [lem-pur-integral-operations-scalar-
extension], normalized by [lem-trf-integral-pullback-comparison-realization]. All schemes have
$\ell$ invertible since they are $k$-schemes and $\ell\ne p$; every input is constructible and
derived complete by Steps 4–6. No etale-origin witness and no $k$-linearity of $e$ is required.
The realization lemma gives, for $h:Z\to W$, $k:W\to V$, $$F_{h,L}(\theta_k)\circ\theta_h
F_{k,E}\circ T_Z(c^E_{h,k})=c^L_{h,k}T_V\circ\theta_{kh}.$$ Apply this twice to the equal maps $j
e_U=e_Xj$; cancelling the invertible compositors gives the scalar square for $b$ defined in Step
6. With $i$ it gives the square for $d$, and with $(e,e^{-1})$ it gives the inverse-composition
square. The same lemma gives units and the successive-field associator equations for these actual
comparisons. The shift equation for these specified $\theta_f$, which is not asserted by that
realization lemma, is [lem-sf-framework-theta-shift-compatibility]. Thus these are coherent
comparisons for the framework completed operations.
8. By [def-weil-rationalization-karoubi], rationalization has the integral objects, morphisms
$\operatorname{Hom}(K,M)\otimes_R E$, the induced shift, and distinguished triangles isomorphic to
images of integral distinguished triangles. An $R$-linear exact functor $F$ from Steps 4–6
therefore extends by $F(u\otimes a)=F(u)\otimes a$: the balancing relation follows from
$R$-linearity; composition and identities follow on pure tensors and then by additivity. Its
linearized shift comparison carries every image integral triangle to a distinguished triangle, and
hence every distinguished triangle to one. Integral natural transformations extend by their same
components; naturality and their composition, inverse and shift equations extend by bilinearity.
The integral immersion pullbacks $i^*,j^*$ of [def-pur-integral-derived-operations] are also
$R$-linear and exact: on flat-term K-flat representatives they are the functorial
$\operatorname{Cone}(1-s)[-1]$ of termwise additive functors (reduction, $f^*$,
$\operatorname{Res}_n$, products), which carry the termwise split sequence $0\to Q\to C(u)\to
P[1]\to0$ of a cone to a termwise split sequence, hence a cone triangle to a distinguished
triangle, with the shift comparison obtained by shifting the representative and its tower. Apply
this to $F_e,F_{e^{-1}},i^*,j^*$, their inverse comparisons, $b,d$, and Step 7's $\theta$ squares.
These are precisely the rational operations on objects and pure tensors in [def-weil-derived-
pullback-tensor-hom]. Consequently the equivalence and all equations hold in the FRAMEWORK
$D^b_c(T,E)$; no identification with a different rational category is used.
9. Apply [lem-sf-framework-common-stage-descent] to the exact rational functors from Step 8 with
$\beta=\theta$ rationalized. Step 7 gives its unit and associator equations and the theta shift
lemma gives its shift hypothesis; the framework scalar transitions are exact by [lem-weil-scalar-
extension-exact-triangulated]. For a representative $u$ over $L$, descent sends it to
$\theta_{E',L}^{-1}F_{e,L}(u)\theta_{E,L}$. Both this formula and the object $(E,F_{e,E}K)$ are
exactly those prescribed at algebraically closed coefficients in [def-weil-derived-pullback-
tensor-hom], using [def-weil-algebraically-closed-coefficients]. Thus the descended equivalence is
the specified $F_e$. Descend $F_{e^{-1}}$ and the compatible inverse transformations to obtain its
inverse. The same comparison of formulas, with $\theta_i,\theta_j$ (Steps 7–8 and the theta shift
lemma for $f=i,j$), shows that the exact families $i^*_E,j^*_E$ descend to the prescribed
$i^*,j^*$. For $b$, apply descent to the composite families $F_{e_U}j^*$ and $j^*F_{e_X}$, with
the whiskered composite comparisons; the composition clause of the descent lemma identifies their
descended functors with these composites of prescribed functors. Step 7 is exactly the scalar-
compatibility square for $b_E$ (in the $(h,k)$ notation of Step 7,
$b_E=c^E_{j,e_X}\circ(c^E_{e_U,j})^{-1}$), so its class gives the prescribed pullback-composition
$b$; the same applies to $d$. Descent preserves their shift, identity, inverse and associativity
equations from Steps 3 and 6. It gives exactness and independence of the common field. Its
$\overline{\mathbf Q}_\ell$-linearity follows over one finite field containing the finitely many
scalars and representative arrows, where every functor is linear.
10. Finally [def-weil-frobenius-detailed] supplies the geometric-Frobenius scheme automorphisms on
geometric fibres from finite-field models. For complementary immersions from the same model the
two squares commute already by the base-change definition
$g=\mathrm{id}\times\operatorname{Spec}(\gamma)$. They therefore satisfy exactly the scheme-
automorphism hypotheses used above, even though they need not be $k$-morphisms. Substituting these
automorphisms gives the final specialization.
-/
theorem automorphismConstructibleStage_finite
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) (n : ℕ) :
    (∀ K : proEtaleDerivedCategory T.left (finiteCoefficientRing l E (n + 1)),
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
          T.left ((finiteDerivedPullback l E n e.hom).obj K) ↔
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) T.left K) ∧
    (∀ (K : proEtaleDerivedCategory T.left (finiteCoefficientRing l E (n + 1)))
      (a b : ℤ),
      proEtaleCohomologicalSupport K ⊆ Set.Icc a b →
        proEtaleCohomologicalSupport ((finiteDerivedPullback l E n e.hom).obj K) ⊆
          Set.Icc a b) ∧
    ∃ F : finiteTorsionConstructibleCategory D l hl E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) T.left ⥤
        finiteTorsionConstructibleCategory D l hl E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) T.left,
      F ⋙ (finiteTorsionConstructible D l hl E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) T.left).ι =
      (finiteTorsionConstructible D l hl E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) T.left).ι ⋙ finiteDerivedPullback l E n e.hom ∧
      F.IsEquivalence ∧
      ∃ c : F.CommShift ℤ, F.IsTriangulated ∧
        ∀ (r : ℤ) (K : finiteTorsionConstructibleCategory D l hl E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) T.left),
          HEq (((F.commShiftIso (self := c) r).hom.app K).hom)
            (((finiteDerivedPullback l E n e.hom).commShiftIso r).hom.app K.obj) := by
  classical
  let : Fact (l ≠ D.p) := ⟨hl⟩
  let : ∀ x : T.left, Invertible (l : T.left.residueField x) :=
    fun x ↦ ((automorphismConstructibleStage_units D l hl T).2 x).invertible
  let A := finiteCoefficientRing l E (n + 1)
  let P := finiteTorsionConstructible D l hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) T.left
  let H := finiteDerivedPullback l E n e.hom
  let J := finiteDerivedPullback l E n e.inv
  let cancel (g : Aut T.left) :
      finiteDerivedPullback l E n g.hom ⋙ finiteDerivedPullback l E n g.inv ≅ 𝟭 _ :=
    (sfIntrinsicDerivedPullbackComp A g.inv g.hom).symm ≪≫
      eqToIso (congrArg (sfIntrinsicDerivedPullback A) g.inv_hom_id) ≪≫
        sfIntrinsicDerivedPullbackId A T.left
  let : H.IsEquivalence := Functor.IsEquivalence.mk' J (cancel e).symm (cancel e.symm)
  obtain ⟨hH, _⟩ := isomorphismFiniteDerivedPullback_termwise l E e.hom n
  obtain ⟨hJ, _⟩ := isomorphismFiniteDerivedPullback_termwise l E e.inv n
  have hp (K : proEtaleDerivedCategory T.left A) : P (H.obj K) ↔ P K := by
    constructor
    · intro hK
      exact P.prop_of_iso ((cancel e).app K) ((hJ (H.obj K) hK).1)
    · intro hK
      exact (hH K hK).1
  let F := P.lift (P.ι ⋙ H) (fun K ↦ (hp K.obj).2 K.property)
  let : F.EssSurj := ⟨fun K ↦
    ⟨⟨J.obj K.obj, (hJ K.obj K.property).1⟩, ⟨P.isoMk ((cancel e.symm).app K.obj)⟩⟩⟩
  refine ⟨hp, ?_, F, rfl, ⟨inferInstance, inferInstance, inferInstance⟩,
    inferInstance, inferInstance, ?_⟩
  · intro K a b h i hi
    apply h
    intro hz
    exact hi ((sfIntrinsicPullback A e.hom).isZero_homologyFunctor_mapDerivedCategory_obj hz)
  · exact lift_shift_component P H (fun K ↦ (hp K.obj).2 K.property)

/-- Invertibility on residue fields, obtained from the prime-to-characteristic convention.
Source: Weil-structures paragraph, coefficient convention
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
instance automorphismConstructibleStage_invertible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [h : Fact (l ≠ D.p)]
    (T : Over (Spec (.of D.k))) (x : T.left) :
    Invertible (l : T.left.residueField x) :=
  ((automorphismConstructibleStage_units D l h.out T).2 x).invertible

attribute [local semireducible] HasDerivedCategory.standard

private theorem rational_pullback_linear
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (f : X ⟶ X)
    [(constructibleIntegralPullback l E f).Additive]
    [(constructibleIntegralPullback l E f).Linear
      (Padic.coefficientExtensionIntegers l E)] :
    (rationalDerivedPullback l E f).Linear
      (Localization.Away (Padic.coefficientExtensionUniformizer l E)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let C := sfIntegralConstructibleCategory l E X
  let t := Padic.coefficientExtensionUniformizer l E
  let F := ScalarLocalization.map R C t (constructibleIntegralPullback l E f)
  have he : F = rationalDerivedPullback l E f := by
    apply (rationalDerivedPullback_existsUnique l E f).unique
    · refine ⟨inferInstance, fun K ↦ rfl, ?_⟩
      intro K M g a
      apply heq_of_eq
      exact LinearMap.baseChange_tmul _ _ _
    · exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual integral and rational functors are inverse exact equivalences.
Source: Weil-structures paragraph, integral and rational coefficient assertions
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: reindexing along e and its inverse is an exact module equivalence. It preserves
products and the entire Roos quotient tower, including its augmentation. Thus it preserves
completeness and every uniform interval. The actual comparison with completed pullback
is invertible. Restrict to constructible objects. The inverse-composition comparisons
are the normalized pullback compositors. Localize the linear integral functors and their
comparisons to obtain the asserted rational equivalence and exactness. -/
theorem automorphismConstructibleStage_integral_rational
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) :
    (constructibleIntegralPullback l E e.hom).IsEquivalence ∧
    (constructibleIntegralPullback l E e.hom).Linear
      (Padic.coefficientExtensionIntegers l E) ∧
    (∃ _ : (constructibleIntegralPullback l E e.hom).CommShift ℤ,
      (constructibleIntegralPullback l E e.hom).IsTriangulated) ∧
    Nonempty (constructibleIntegralPullback l E e.hom ⋙
      constructibleIntegralPullback l E e.inv ≅ 𝟭 _) ∧
    Nonempty (constructibleIntegralPullback l E e.inv ⋙
      constructibleIntegralPullback l E e.hom ≅ 𝟭 _) ∧
    (rationalDerivedPullback l E e.hom).IsEquivalence ∧
    (rationalDerivedPullback l E e.hom).Linear
      (Localization.Away (Padic.coefficientExtensionUniformizer l E)) ∧
    (∃ _ : (rationalDerivedPullback l E e.hom).CommShift ℤ,
      (rationalDerivedPullback l E e.hom).IsTriangulated) ∧
    Nonempty (rationalDerivedPullback l E e.hom ⋙ rationalDerivedPullback l E e.inv ≅ 𝟭 _) ∧
    Nonempty (rationalDerivedPullback l E e.inv ⋙ rationalDerivedPullback l E e.hom ≅ 𝟭 _) := by
  classical
  let i : ∀ x : T.left, Invertible (l : T.left.residueField x) := inferInstance
  have hft : LocallyOfFiniteType T.hom := inferInstance
  have hqc : QuasiCompact T.hom := inferInstance
  let : T.left.Over (Spec (.of D.k)) := ⟨T.hom⟩
  let : LocallyOfFiniteType (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hft
  let : QuasiCompact (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hqc
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨iX, iY, h⟩ := isomorphismFieldTransport D l (Fact.out : l ≠ D.p)
    (AlgebraicClosure ℚ_[l]) e.hom
  have hiX : iX = i :=
    Subsingleton.elim _ _
  have hiY : iY = i :=
    Subsingleton.elim _ _
  cases hiX
  cases hiY
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨hX, hY, hS, _⟩ := h
  obtain ⟨S⟩ := (hS E).1
  obtain ⟨R⟩ := (hS E).2
  let : (constructibleIntegralPullback l E e.hom).Linear
      (Padic.coefficientExtensionIntegers l E) := S.integralLinear
  let : (constructibleIntegralPullback l E e.hom).CommShift ℤ := S.integralShift
  let : (constructibleIntegralPullback l E e.hom).IsTriangulated := S.integralExact
  let : (constructibleIntegralPullback l E e.hom).Additive := inferInstance
  refine ⟨S.integralEquivalence, S.integralLinear,
    ⟨S.integralShift, S.integralExact⟩, ?_, ?_, S.rationalEquivalence,
    rational_pullback_linear l E e.hom, ⟨S.rationalShift, S.rationalExact⟩, ?_, ?_⟩
  · simpa only [IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, IsIso.inv_inv] using
      Nonempty.intro S.epsilon
  · simpa only [IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, IsIso.inv_inv] using
      Nonempty.intro R.epsilon
  · simpa only [IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, IsIso.inv_inv] using
      Nonempty.intro S.rationalEpsilon
  · simpa only [IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, IsIso.inv_inv] using
      Nonempty.intro R.rationalEpsilon

/-- The prescribed coherent common-stage functor is an exact equivalence.
Source: Weil-structures paragraph, algebraically closed coefficient assertion
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: rationalize the normalized integral scalar comparisons, including their unit,
associator, and shift equations. Descend the families for e and its inverse through the
actual common-stage representative formula. Their compatible inverse comparisons descend
and remain inverse. Every triangle comes from one common finite coefficient field,
where exactness is already proved. Linearity is checked over a field containing all
finitely many coefficient scalars and arrow representatives. -/
theorem automorphismConstructibleStage_qbar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) :
    (commonStageDerivedPullback l Ω e.hom).IsEquivalence ∧
    (commonStageDerivedPullback l Ω e.hom).Additive ∧
    (∃ _ : (commonStageDerivedPullback l Ω e.hom).CommShift ℤ,
      (commonStageDerivedPullback l Ω e.hom).IsTriangulated) ∧
    Nonempty (commonStageDerivedPullback l Ω e.hom ⋙
      commonStageDerivedPullback l Ω e.inv ≅ 𝟭 _) ∧
    Nonempty (commonStageDerivedPullback l Ω e.inv ⋙
      commonStageDerivedPullback l Ω e.hom ≅ 𝟭 _) := by
  classical
  let i : ∀ x : T.left, Invertible (l : T.left.residueField x) := inferInstance
  have hft : LocallyOfFiniteType T.hom := inferInstance
  have hqc : QuasiCompact T.hom := inferInstance
  let : T.left.Over (Spec (.of D.k)) := ⟨T.hom⟩
  let : LocallyOfFiniteType (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hft
  let : QuasiCompact (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hqc
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨iX, iY, h⟩ := isomorphismFieldTransport D l (Fact.out : l ≠ D.p) Ω e.hom
  have hiX : iX = i :=
    Subsingleton.elim _ _
  have hiY : iY = i :=
    Subsingleton.elim _ _
  cases hiX
  cases hiY
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨hX, hY, _, _, S, R, _, ⟨A⟩, ⟨B⟩⟩ := h
  refine ⟨A.equivalence, A.additive, ⟨A.shift, A.exact⟩, ?_, ?_⟩
  · simpa only [IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, IsIso.inv_inv] using
      Nonempty.intro A.epsilon
  · simpa only [IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, IsIso.inv_inv] using
      Nonempty.intro B.epsilon


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Positive coefficient levels have their existing finite-ring structure.
Source: the coefficient convention in the Weil-structures paragraph
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
instance automorphismConstructibleStage_finiteRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (finiteCoefficientRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Fixed-scalar coordinates for the intrinsic finite coefficient category.
This only abbreviates the inverse of the recorded realization, followed by its
termwise exact derived functor. Source: the finite coefficient convention
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
abbrev automorphismStageFiniteCoordinates
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :=
  (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory

private theorem scalar_in_coordinates
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    {R : Type*} [Ring R] [Linear R D]
    (G : C ⥤ D) [G.Full] [G.Faithful] (F : C ⥤ C) (H : D ⥤ D) [H.Linear R]
    (e : F ⋙ G ≅ G ⋙ H) {K M : C} (f : K ⟶ M) (a : R) :
    G.map (F.map (G.preimage (a • G.map f))) = a • G.map (F.map f) := by
  have hc {K M : C} (g : K ⟶ M) :
      G.map (F.map g) = e.hom.app K ≫ H.map (G.map g) ≫ e.inv.app M := by
    have hn := e.hom.naturality g
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hc, G.map_preimage, H.map_smul, Linear.smul_comp, Linear.comp_smul, ← hc]

/-- Coefficient linearity in the canonical constant-module coordinates.
Source: Weil-structures paragraph, finite coefficient equivalence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the actual inverse-image comparison fixes every constant coefficient.
On module sheaves, inverse image therefore respects scalar multiplication on maps.
Termwise passage to complexes and localization preserve this equality. The inverse
realization is fully faithful, so the displayed formula is precisely linearity
on every derived morphism, including those represented by roofs. -/
theorem automorphismConstructibleStage_finite_linear
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) (n : ℕ)
    (K M : proEtaleDerivedCategory T.left (finiteCoefficientRing l E (n + 1)))
    (f : K ⟶ M) (a : ULift.{u + 1} (finiteCoefficientRing l E (n + 1))) :
    (automorphismStageFiniteCoordinates (finiteCoefficientRing l E (n + 1)) T.left).map
      ((finiteDerivedPullback l E n e.hom).map
        ((automorphismStageFiniteCoordinates (finiteCoefficientRing l E (n + 1))
          T.left).preimage
          (a • (automorphismStageFiniteCoordinates (finiteCoefficientRing l E (n + 1))
            T.left).map f))) =
      a • (automorphismStageFiniteCoordinates (finiteCoefficientRing l E (n + 1))
        T.left).map ((finiteDerivedPullback l E n e.hom).map f) := by
  let A := finiteCoefficientRing l E (n + 1)
  let G := (sfIntrinsicModuleEquivalence T.left A).inverse
  let H := AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) e.hom
  let Λ := ULift.{u + 1} A
  let B := ModuleCat.{u + 1} Λ
  let : (AlgebraicGeometry.ProEtale.lowerStar B e.hom).Linear Λ := {}
  let : H.Linear Λ :=
    (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction B e.hom).left_adjoint_linear
  let c : sfIntrinsicPullback A e.hom ⋙ G ≅ G ⋙ H :=
    Functor.isoWhiskerLeft G
      ((Functor.associator H (sfIntrinsicModuleEquivalence T.left A).functor G) ≪≫
        Functor.isoWhiskerLeft H (sfIntrinsicModuleEquivalence T.left A).unitIso.symm ≪≫
        Functor.rightUnitor H)
  let d : finiteDerivedPullback l E n e.hom ⋙ G.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ H.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso (sfIntrinsicPullback A e.hom) G).symm ≪≫
      Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryCompIso G H
  exact scalar_in_coordinates G.mapDerivedCategory (finiteDerivedPullback l E n e.hom)
    H.mapDerivedCategory d f a

/-- Each particular witnessing constructible partition pulls back to its inverse image.
Source: Weil-structures paragraph, finite constructibility clause
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the canonical stratification pullback has precisely the subsets e⁻¹S_i
and base changes of their specified immersions. Pull back each local trivializing
cover. The same finite coefficient modules trivialize the restrictions. The
restricted automorphism is an isomorphism, so its geometric stalks are the
original finite stalks. Exact inverse image commutes with cohomology, and hence
this applies to each cohomology sheaf in a witnessing partition. -/
theorem automorphismConstructibleStage_strata
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) (n : ℕ)
    (M : proEtaleRingModules T.left (proEtaleConstantRing T.left
      (finiteCoefficientRing l E (n + 1)))) (S : Stratification T.left)
    (hS : ∀ i : Fin S.n,
      IsLocallyConstantProEtaleModuleSheaf (S.domain i) (finiteCoefficientRing l E (n + 1))
        (proEtaleConstantModulePullback (S.immersion i) (finiteCoefficientRing l E (n + 1)) M) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricModuleStalk y
          (proEtaleConstantRing (S.domain i) (finiteCoefficientRing l E (n + 1)))
          (proEtaleConstantModulePullback (S.immersion i)
            (finiteCoefficientRing l E (n + 1)) M))) :
    ∀ i : Fin (S.pullback e.hom).n,
      IsLocallyConstantProEtaleModuleSheaf ((S.pullback e.hom).domain i)
        (finiteCoefficientRing l E (n + 1))
        (proEtaleConstantModulePullback ((S.pullback e.hom).immersion i)
          (finiteCoefficientRing l E (n + 1))
          ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) e.hom).obj M)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ (S.pullback e.hom).domain i),
        Finite (proEtaleGeometricModuleStalk y
          (proEtaleConstantRing ((S.pullback e.hom).domain i)
            (finiteCoefficientRing l E (n + 1)))
          (proEtaleConstantModulePullback ((S.pullback e.hom).immersion i)
            (finiteCoefficientRing l E (n + 1))
            ((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) e.hom).obj M))) := by
  classical
  intro i
  let A := finiteCoefficientRing l E (n + 1)
  let p := pullback.fst (S.immersion i) e.hom
  let q := pullback.snd (S.immersion i) e.hom
  let M' := proEtaleConstantModulePullback p A
    (proEtaleConstantModulePullback (S.immersion i) A M)
  have hM' := proEtale_finiteLocalConstancy_pullback p A _ (hS i)
  obtain ⟨c⟩ := proEtaleConstantModulePullback_comp e.hom q A
  obtain ⟨d⟩ := proEtaleConstantModulePullback_comp (S.immersion i) p A
  let a : proEtaleConstantModulePullback q A ((sfIntrinsicPullback A e.hom).obj M) ≅ M' :=
    (proEtaleConstantModulePullbackFunctor q A).mapIso
        ((openSquarePullbackModel A e.hom).app M).symm ≪≫
      (c.app M).symm ≪≫
      eqToIso (congrArg (fun g ↦ proEtaleConstantModulePullback g A M)
        pullback.condition.symm) ≪≫ d.app M
  exact (finiteLocal_iff _ A _).mp
    (AlgebraicGeometry.ProEtale.isFiniteLocallyConstant_of_iso
      ((proEtaleModuleRestriction _ A).mapIso a.symm)
      ((finiteLocal_iff _ A _).mpr hM'))

/-- The finite commuting-square map is the prescribed pair of pullback compositors.
Source: Weil-structures paragraph, the maps b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageFiniteSquare (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    sfIntrinsicDerivedPullback A f ⋙ sfIntrinsicDerivedPullback A eY.hom ≅
      sfIntrinsicDerivedPullback A eX.hom ⋙ sfIntrinsicDerivedPullback A f :=
  (sfIntrinsicDerivedPullbackComp A eY.hom f).symm ≪≫
    eqToIso (congrArg (sfIntrinsicDerivedPullback A) h) ≪≫
      sfIntrinsicDerivedPullbackComp A f eX.hom


/-- Ordinary and completed integral pullback agree through the actual comparison;
completeness and the original uniform interval are preserved.
Source: Weil-structures paragraph, integral coefficient assertions
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: reindexing transports the canonical completed-ring action and preserves products.
Apply it to the Roos triangle with its given quotient augmentation. This proves
completeness of ordinary pullback. The normalization of the actual comparison by the
completion unit makes that comparison invertible on complete objects. Its finite
projection-adjoint maps identify reductions with finite pullbacks, and their exactness
preserves the identical interval for every positive level. -/
theorem automorphismConstructibleStage_completion
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [h : Fact (l ≠ D.p)]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left)
    (K : DerivedCategory (integralTowerModules l E T.left))
    (hK : IsSfDerivedComplete l E T.left K) :
    IsSfDerivedComplete l E T.left
      ((AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E e.hom).obj K) ∧
    IsSfDerivedComplete l E T.left ((integralDerivedPullback l E e.hom).obj K) ∧
    IsIso (AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived l E e.hom
      (automorphismConstructibleStage_units D l h.out T).1
      (automorphismConstructibleStage_units D l h.out T).1 K) ∧
    ∀ a b : ℤ,
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension l E T.left n).obj K) ⊆ Set.Icc a b) →
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension l E T.left n).obj
          ((integralDerivedPullback l E e.hom).obj K)) ⊆ Set.Icc a b := by
  classical
  obtain ⟨P, ⟨a⟩⟩ := goodRepresentative l E T.left K
  have hc := pullback_effectivity l E e.hom K P a
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E T.left
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact q.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := q, a := 1, q := q, prime := hprime, exponent_pos := le_refl 1
      cardinality_eq := (pow_one q).symm, k₀ := ZMod q
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod q) }
  have hl₀ : l ≠ D₀.p := by change l ≠ q; omega
  have hK₀ : IsDerivedCompleteUnrestricted l E T.left K :=
    ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E T.left D₀ hl₀ K).mp hK⟩
  obtain ⟨_, _, _, κinv, hleft, hright, _⟩ :=
    isomorphismDerivedPullbackComparisonNormalization l E e.hom
      (automorphismConstructibleStage_units D l h.out T).1
      (automorphismConstructibleStage_units D l h.out T).1 S hS K hK₀
  let κ := AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived l E e.hom
    (automorphismConstructibleStage_units D l h.out T).1
    (automorphismConstructibleStage_units D l h.out T).1 K
  let κiso : (AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E e.hom).obj K ≅
      (integralDerivedPullback l E e.hom).obj K := ⟨κ, κinv, hright, hleft⟩
  refine ⟨complete_of_iso l E T.left κiso.symm hc.1, hc.1, κiso.isIso_hom, ?_⟩
  intro a' b' hb n
  let A := finiteCoefficientRing l E (n + 1)
  let F := proEtaleConstantRingPullback A e.hom
  let : IsIso (integralPullbackFiniteComparison l E e.hom K P a n) := hc.2 n
  let c : (scalarReductionDerivedExtension l E T.left n).obj
        ((integralDerivedPullback l E e.hom).obj K) ≅
      F.mapDerivedCategory.obj ((scalarReductionDerivedExtension l E T.left n).obj K) :=
    asIso (integralPullbackFiniteComparison l E e.hom K P a n) ≪≫
      DerivedCategory.Q.mapIso
        ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E e.hom n)
          (ComplexShape.up ℤ)).app ((unrestrictedIntegralFiniteComplex l E T.left n).obj P.obj)) ≪≫
      (F.mapDerivedCategoryFactors.app
        ((unrestrictedIntegralFiniteComplex l E T.left n).obj P.obj)).symm ≪≫
      F.mapDerivedCategory.mapIso
        ((coefficientFiniteReductionModel l E T.left P.obj P.property.1 n).symm ≪≫
          (scalarReductionDerivedExtension l E T.left n).mapIso a)
  intro i hi
  apply hb n
  intro hz
  exact hi (((F.isZero_homologyFunctor_mapDerivedCategory_obj hz).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso c)))



private theorem integral_composition_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) :
    ∃ c : constructibleIntegralPullback l E (h ≫ k) ≅
        constructibleIntegralPullback l E k ⋙ constructibleIntegralPullback l E h,
      ∀ K, (c.hom.app K).hom = (integralComparisonComposition l E C h k K).hom := by
  let P := sfIntegralConstructible l E V
  let U := integralComparisonDerivedSequencePullback l E h
  let L := coefficientSequenceLimit l E Z
  let β : P.ι ⋙ integralDerivedPullback l E k ⋙ ((C.coefficient E).system W).reduction ≅
      P.ι ⋙ ((C.coefficient E).system V).reduction ⋙
        integralComparisonDerivedSequencePullback l E k :=
    NatIso.ofComponents (fun K ↦
      @asIso _ _ _ _ _ ((C.coefficient E).effective k K)) (fun {K J} r ↦ by
        exact (integralComparisonPullbackCounit l E k
          ((C.coefficient E).system V) ((C.coefficient E).system W)
          ((C.coefficient E).roos W) ((C.coefficient E).pullback k)).naturality r.hom)
  let η : P.ι ⋙ integralDerivedPullback l E k ⋙ integralDerivedPullback l E h ≅
      P.ι ⋙ ((C.coefficient E).system V).reduction ⋙
        integralComparisonDerivedSequencePullback l E k ⋙ U ⋙ L :=
    Functor.isoWhiskerLeft (P.ι ⋙ integralDerivedPullback l E k)
        ((C.coefficient E).pullback h).realization ≪≫
      Functor.isoWhiskerRight β (U ⋙ L)
  let γ : P.ι ⋙ integralDerivedPullback l E (h ≫ k) ≅
      P.ι ⋙ integralDerivedPullback l E k ⋙ integralDerivedPullback l E h :=
    Functor.isoWhiskerLeft P.ι ((C.coefficient E).pullback (h ≫ k)).realization ≪≫
      Functor.isoWhiskerLeft (P.ι ⋙ ((C.coefficient E).system V).reduction)
        (Functor.isoWhiskerRight (integralComparisonSystemComposition l E h k) L) ≪≫ η.symm
  refine ⟨NatIso.ofComponents (fun K ↦ (sfIntegralConstructible l E Z).isoMk (γ.app K))
    (fun {K J} r ↦ ?_), fun K ↦ ?_⟩
  · apply ObjectProperty.hom_ext
    exact γ.hom.naturality r
  · rfl

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem integral_congr_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] {g g' : Y ⟶ X} (h : g = g')
    (K : sfIntegralConstructibleCategory l E X) :
    ((eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g)
      h)).hom.app K).hom =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) := by
  cases h
  rfl


/-- The normalized integral commuting-square comparison is uniquely specified by the
actual completed pullback compositors. Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: invert the compositor for e_Y followed by f, identify the two equal scheme maps,
and apply the compositor for f followed by e_X. Each compositor is natural, so the
result is a natural isomorphism. Its displayed components determine it uniquely. -/
theorem automorphismStageIntegralSquare_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :
    ∃! b : constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.hom ≅
        constructibleIntegralPullback l E eX.hom ⋙ constructibleIntegralPullback l E f,
      ∀ K : sfIntegralConstructibleCategory l E X,
        (b.hom.app K).hom =
          (integralComparisonComposition l E C eY.hom f K).inv ≫
            eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
              (integralComparisonComposition l E C f eX.hom K).hom := by
  obtain ⟨c, hc⟩ := integral_composition_natural l E C eY.hom f
  obtain ⟨d, hd⟩ := integral_composition_natural l E C f eX.hom
  let b := c.symm ≪≫
    eqToIso (congrArg (fun g : Y ⟶ X ↦ constructibleIntegralPullback l E g) h) ≪≫ d
  have hb (K : sfIntegralConstructibleCategory l E X) :
      (b.hom.app K).hom =
        (integralComparisonComposition l E C eY.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
            (integralComparisonComposition l E C f eX.hom K).hom := by
    have hc' : (c.inv.app K).hom =
        (integralComparisonComposition l E C eY.hom f K).inv := by
      apply (cancel_mono (integralComparisonComposition l E C eY.hom f K).hom).1
      calc
        _ = (c.inv.app K).hom ≫ (c.hom.app K).hom := by rw [hc K]
        _ = 𝟙 _ := congrArg (fun r ↦ r.hom) (c.inv_hom_id_app K)
        _ = _ := (Iso.inv_hom_id _).symm
    simp only [b, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom, hc', hd]
    rw [integral_congr_component l E h K]
  refine ⟨b, hb, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (ha K).trans (hb K).symm


/-- The actual integral square, with the component normalization just stated.
Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :=
  (automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose


set_option backward.isDefEq.respectTransparency.types false


private theorem map_heq {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem rawIso_existsUnique
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear S D]
    (t : R) (b : S) (c : Localization.Away t → Localization.Away b)
    (U V : C ⥤ D) (e : U ≅ V)
    (F G : ScalarLocalization R C t ⥤ ScalarLocalization S D b)
    [F.Additive] [G.Additive]
    (hF : ∀ K, F.obj K = ⟨U.obj K.obj⟩)
    (hG : ∀ K, G.obj K = ⟨V.obj K.obj⟩)
    (mF : ∀ (K L : C) (a : K ⟶ L) (z : Localization.Away t),
      HEq (F.map (z ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c z ⊗ₜ[S] U.map a))
    (mG : ∀ (K L : C) (a : K ⟶ L) (z : Localization.Away t),
      HEq (G.map (z ⊗ₜ[R] a : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (c z ⊗ₜ[S] V.map a)) :
    ∃! α : F ≅ G, ∀ K, HEq (α.hom.app K)
      ((ScalarLocalization.localization S D b).map (e.hom.app K.obj)) := by
  let Q := ScalarLocalization.localization S D b
  let a (K : ScalarLocalization R C t) :=
    eqToIso (hF K) ≪≫ Q.mapIso (e.app K.obj) ≪≫ (eqToIso (hG K)).symm
  have ha (K : ScalarLocalization R C t) :
      HEq (a K).hom (Q.map (e.hom.app K.obj)) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
      Functor.mapIso_hom]
    exact ((conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 rfl)
  have hn (K L : ScalarLocalization R C t) (f : K ⟶ L) :
      F.map f ≫ (a L).hom = (a K).hom ≫ G.map f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul z f =>
      have h₁ := heq_comp (hF K) (hF L) (hG L) (mF K.obj L.obj f z) (ha L)
      have h₂ := heq_comp (hF K) (hG K) (hG L) (ha K) (mG K.obj L.obj f z)
      apply eq_of_heq
      refine h₁.trans (HEq.trans ?_ h₂.symm)
      apply heq_of_eq
      change ScalarLocalization.composition S D b _ _ _
          (1 ⊗ₜ[S] e.hom.app L.obj) (c z ⊗ₜ[S] U.map f) =
        ScalarLocalization.composition S D b _ _ _
          (c z ⊗ₜ[S] V.map f) (1 ⊗ₜ[S] e.hom.app K.obj)
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, e.hom.naturality]
    | add x y hx hy => simp only [F.map_add, G.map_add,
        Preadditive.add_comp, Preadditive.comp_add, hx, hy]
  refine ⟨NatIso.ofComponents a (fun {K L} f ↦ hn K L f), ha, ?_⟩
  intro α hα
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact eq_of_heq ((hα K).trans (ha K).symm)

/-- Rationalization retains the normalized integral square on every component.
Source: Weil-structures paragraph, rationalized b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: apply the integral-to-rational localization to each component. Integral
naturality extends to pure tensors by linearity and then to sums by additivity.
The localized inverse gives a natural inverse. The specified components determine
the natural isomorphism uniquely. -/
theorem automorphismStageRationalSquare_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :
    ∃! b : rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.hom ≅
        rationalDerivedPullback l E eX.hom ⋙ rationalDerivedPullback l E f,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (b.hom.app K)
          ((sfRationalConstructibleLocalization l E Y).map
            ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K.obj)) := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let U := constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.hom
  let V := constructibleIntegralPullback l E eX.hom ⋙ constructibleIntegralPullback l E f
  let F := rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.hom
  let G := rationalDerivedPullback l E eX.hom ⋙ rationalDerivedPullback l E f
  have ho {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W)
      (K : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj K =
        ScalarLocalization.mk ((constructibleIntegralPullback l E g).obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 K
  have hm {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W)
      (K M : sfIntegralConstructibleCategory l E W) (a : K ⟶ M)
      (z : Localization.Away t) :
      HEq ((rationalDerivedPullback l E g).map (z ⊗ₜ[R] a))
        (z ⊗ₜ[R] (constructibleIntegralPullback l E g).map a) := by
    simpa only [rationalDerivedPullback, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 K M a z
  have hadd {Z W : Scheme.{u}}
      [∀ z : Z, Invertible (l : Z.residueField z)]
      [∀ w : W, Invertible (l : W.residueField w)] (g : Z ⟶ W) :
      (rationalDerivedPullback l E g).Additive :=
    (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.1
  let : (rationalDerivedPullback l E f).Additive := hadd f
  let : (rationalDerivedPullback l E eX.hom).Additive := hadd eX.hom
  let : (rationalDerivedPullback l E eY.hom).Additive := hadd eY.hom
  apply rawIso_existsUnique t t id U V
    (automorphismStageIntegralSquare l E C f eX eY h) F G
  · intro K
    exact (ho eY.hom _).trans (congrArg
      (fun Z : sfRationalConstructibleCategory l E Y ↦
        ScalarLocalization.mk ((constructibleIntegralPullback l E eY.hom).obj Z.obj)) (ho f K))
  · intro K
    exact (ho f _).trans (congrArg
      (fun Z : sfRationalConstructibleCategory l E X ↦
        ScalarLocalization.mk ((constructibleIntegralPullback l E f).obj Z.obj)) (ho eX.hom K))
  · intro K M a z
    exact (map_heq (rationalDerivedPullback l E eY.hom)
      (ho f _) (ho f _) (hm f K M a z)).trans
        (hm eY.hom _ _ ((constructibleIntegralPullback l E f).map a) z)
  · intro K M a z
    exact (map_heq (rationalDerivedPullback l E f)
      (ho eX.hom _) (ho eX.hom _) (hm eX.hom K M a z)).trans
        (hm f _ _ ((constructibleIntegralPullback l E eX.hom).map a) z)


/-- The rational square is exactly the rationalization of the integral one.
Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageRationalSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :=
  (automorphismStageRationalSquare_existsUnique l E C f eX eY h).exists.choose


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Common-stage b and d have exactly the rational components over each representative's
coefficient field. Source: Weil-structures paragraph, common-stage b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the integral scalar-composition equation gives the square for b by cancellation
of the invertible compositors, and likewise for d. Rationalize that equation. Thus the
rational component families descend through coherent finite-field descent. The actual
prescribed operation formulas identify the resulting functors with the displayed ones.
Every object is a literal pair, so these components uniquely determine the comparison. -/
theorem automorphismStageQbarSquare_existsUnique
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :
    ∃! b : commonStageDerivedPullback l Ω f ⋙ commonStageDerivedPullback l Ω eY.hom ≅
        commonStageDerivedPullback l Ω eX.hom ⋙ commonStageDerivedPullback l Ω f,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        HEq (b.hom.app K)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) K.stage).map
            ((automorphismStageRationalSquare l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)
              C f eX eY h).hom.app K.obj)) := by
  sorry

/-- The common-stage square with the exact specified representative normalization.
Source: Weil-structures paragraph, b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageQbarSquare
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :=
  (automorphismStageQbarSquare_existsUnique l Ω C f eX eY h).exists.choose


/-- The integral inverse-composition comparison uses the actual compositor and identity unit.
Source: Weil-structures paragraph, inverse automorphism comparisons
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralCancel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (C : IntegralComparisonSystem.{u} l)
    {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)] (e : Aut X)
    (K : sfIntegralConstructibleCategory l E X) :
    ((constructibleIntegralPullback l E e.hom ⋙
      constructibleIntegralPullback l E e.inv).obj K).obj ≅ K.obj :=
  (integralComparisonComposition l E C e.inv e.hom K).symm ≪≫
    eqToIso (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) e.inv_hom_id) ≪≫
      integralComparisonUnit l E C X K


/-- The canonical finite inverse-composition comparison, without an arbitrary choice of unit.
Source: Weil-structures paragraph, inverse automorphism comparisons
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageFiniteCancel (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} (e : Aut X) :
    sfIntrinsicDerivedPullback A e.hom ⋙ sfIntrinsicDerivedPullback A e.inv ≅ 𝟭 _ :=
  (sfIntrinsicDerivedPullbackComp A e.inv e.hom).symm ≪≫
    eqToIso (congrArg (sfIntrinsicDerivedPullback A) e.inv_hom_id) ≪≫
      sfIntrinsicDerivedPullbackId A X



/-- The inverse automorphisms satisfy the same commuting immersion square.
Source: Weil-structures paragraph, inverse coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: compose the given square on the source with eY inverse and on the target
with eX inverse. Cancel both automorphism composites using their inverse laws. -/
theorem automorphismStage_inverseSquare {X Y : Scheme.{u}} (f : Y ⟶ X)
    (eX : Aut X) (eY : Aut Y) (h : eY.hom ≫ f = f ≫ eX.hom) :
    eY.inv ≫ f = f ≫ eX.inv := by
  apply (eY.inv_comp_eq).2
  rw [← Category.assoc, h, Category.assoc, eX.hom_inv_id, Category.comp_id]

section FiniteCoherence
open CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard sfIntrinsicPullback
  sfIntrinsicPullbackComp sfIntrinsicPullbackId sfIntrinsicSquarePullback Functor.mapDerivedCategory
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

private theorem derive_transport
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    {f g : Y ⟶ X} (h : f = g) :
    (mapDerivedCategoryNatIso (eqToIso (congrArg (sfIntrinsicPullback A) h))).hom =
      (eqToIso (congrArg (sfIntrinsicDerivedPullback A) h)).hom := by
  cases h
  exact mapDerivedCategoryNatIso_refl

private theorem finite_square_derived
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    automorphismStageFiniteSquare A f eX eY h =
      sfIntrinsicDerivedSquarePullback A eY.hom f f eX.hom h := by
  apply Iso.ext
  rw [sfIntrinsicDerivedSquarePullback, sfIntrinsicSquarePullback]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [mapDerivedCategoryNatIso_trans, mapDerivedCategoryNatIso_trans,
    mapDerivedCategoryNatIso_symm, derive_transport A h]
  simp only [automorphismStageFiniteSquare, sfIntrinsicDerivedPullbackComp,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]


private theorem identity_transport
    {C D : Type*} [Category C] [Category D] {X Y : Scheme.{u}}
    (P : (X ⟶ X) → C ⥤ C) (Q : (Y ⟶ Y) → D ⥤ D)
    (H : (Y ⟶ X) → C ⥤ D)
    (B : ∀ (a : Y ⟶ Y) (f : Y ⟶ X) (b : X ⟶ X),
      a ≫ f = f ≫ b → (H f ⋙ Q a ≅ P b ⋙ H f))
    (uX : P (𝟙 X) ≅ 𝟭 _) (uY : Q (𝟙 Y) ≅ 𝟭 _)
    (f : Y ⟶ X)
    (hi : ∀ (w : 𝟙 Y ≫ f = f ≫ 𝟙 X) (K : C),
      (B (𝟙 Y) f (𝟙 X) w).hom.app K ≫ (H f).map (uX.hom.app K) =
        uY.hom.app ((H f).obj K))
    (a : Y ⟶ Y) (b : X ⟶ X) (ha : a = 𝟙 Y) (hb : b = 𝟙 X)
    (w : a ≫ f = f ≫ b) (K : C) :
    (B a f b w).hom.app K ≫
      (H f).map ((eqToIso (congrArg P hb) ≪≫ uX).hom.app K) =
      (eqToIso (congrArg Q ha) ≪≫ uY).hom.app ((H f).obj K) := by
  subst a
  subst b
  simpa only [eqToIso_refl, Iso.refl_trans] using hi w K

private theorem finite_derived_identity
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : Y ⟶ Y) (b : X ⟶ X) (ha : a = 𝟙 Y) (hb : b = 𝟙 X)
    (w : a ≫ f = f ≫ b) (K : proEtaleDerivedCategory X A) :
    (sfIntrinsicDerivedSquarePullback A a f f b w).hom.app K ≫
      (sfIntrinsicDerivedPullback A f).map
        ((eqToIso (congrArg (sfIntrinsicDerivedPullback A) hb) ≪≫
          sfIntrinsicDerivedPullbackId A X).hom.app K) =
    (eqToIso (congrArg (sfIntrinsicDerivedPullback A) ha) ≪≫
      sfIntrinsicDerivedPullbackId A Y).hom.app
        ((sfIntrinsicDerivedPullback A f).obj K) := by
  have hbase (v : 𝟙 Y ≫ f = f ≫ 𝟙 X) (J : proEtaleDerivedCategory X A) :
      (sfIntrinsicDerivedSquarePullback A (𝟙 Y) f f (𝟙 X) v).hom.app J ≫
        (sfIntrinsicDerivedPullback A f).map
          ((sfIntrinsicDerivedPullbackId A X).hom.app J) =
      (sfIntrinsicDerivedPullbackId A Y).hom.app
        ((sfIntrinsicDerivedPullback A f).obj J) := by
    exact mapDerivedCategorySquareIso_hom_app_id
      (sfIntrinsicSquarePullback A (𝟙 Y) f f (𝟙 X) v)
      (sfIntrinsicPullbackId A X) (sfIntrinsicPullbackId A Y)
      (sfSquare_identity A f v) J
  exact identity_transport (sfIntrinsicDerivedPullback A) (sfIntrinsicDerivedPullback A)
    (sfIntrinsicDerivedPullback A)
    (fun a f b w ↦ sfIntrinsicDerivedSquarePullback A a f f b w)
    (sfIntrinsicDerivedPullbackId A X) (sfIntrinsicDerivedPullbackId A Y)
    f hbase a b ha hb w K

private theorem finite_derived_pasting
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom)
    (w : (eY.inv ≫ eY.hom) ≫ f = f ≫ (eX.inv ≫ eX.hom))
    (K : proEtaleDerivedCategory X A) :
    (sfIntrinsicDerivedSquarePullback A (eY.inv ≫ eY.hom) f f
      (eX.inv ≫ eX.hom) w).hom.app K ≫
        (sfIntrinsicDerivedPullback A f).map
          ((sfIntrinsicDerivedPullbackComp A eX.inv eX.hom).hom.app K) =
      (sfIntrinsicDerivedPullbackComp A eY.inv eY.hom).hom.app
          ((sfIntrinsicDerivedPullback A f).obj K) ≫
        (sfIntrinsicDerivedPullback A eY.inv).map
          ((sfIntrinsicDerivedSquarePullback A eY.hom f f eX.hom h).hom.app K) ≫
        (sfIntrinsicDerivedSquarePullback A eY.inv f f eX.inv
          (automorphismStage_inverseSquare f eX eY h)).hom.app
            ((sfIntrinsicDerivedPullback A eX.hom).obj K) := by
  exact mapDerivedCategorySquareIso_hom_app_comp
    (sfIntrinsicSquarePullback A eY.hom f f eX.hom h)
    (sfIntrinsicSquarePullback A eY.inv f f eX.inv
      (automorphismStage_inverseSquare f eX eY h))
    (sfIntrinsicSquarePullback A (eY.inv ≫ eY.hom) f f (eX.inv ≫ eX.hom) w)
    (sfIntrinsicPullbackComp A eY.inv eY.hom)
    (sfIntrinsicPullbackComp A eX.inv eX.hom)
    (fun M ↦ (sfSquare_horizontal A eY.hom eY.inv f f f eX.hom eX.inv h
      (automorphismStage_inverseSquare f eX eY h) w M).symm) K

private theorem finite_shift (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    NatTrans.CommShift (automorphismStageFiniteSquare A f eX eY h).hom ℤ := by
  have he : NatTrans.CommShift
      (eqToIso (congrArg (sfIntrinsicDerivedPullback A) h)).hom ℤ := by
    have eqshift {Z W : Scheme.{u}} (a b : Z ⟶ W) (w : a = b) :
        NatTrans.CommShift (eqToIso (congrArg (sfIntrinsicDerivedPullback A) w)).hom ℤ := by
      subst b
      change NatTrans.CommShift (𝟙 _) ℤ
      infer_instance
    exact eqshift _ _ h
  have hc {Z W V : Scheme.{u}} (a : Z ⟶ W) (b : W ⟶ V) :
      NatTrans.CommShift (sfIntrinsicDerivedPullbackComp A a b).hom ℤ := by
    dsimp only [sfIntrinsicDerivedPullbackComp, Iso.trans_hom]
    infer_instance
  have := hc eY.hom f
  have := hc f eX.hom
  dsimp only [automorphismStageFiniteSquare, Iso.trans_hom, Iso.symm_hom]
  infer_instance

private theorem cancel_pasting
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P Pi P' : C ⥤ C) (Q Qi Q' : D ⥤ D)
    (B : F ⋙ Q ≅ P ⋙ F) (Bi : F ⋙ Qi ≅ Pi ⋙ F)
    (B' : F ⋙ Q' ≅ P' ⋙ F)
    (cX : P' ≅ P ⋙ Pi) (cY : Q' ≅ Q ⋙ Qi)
    (uX : P' ≅ 𝟭 C) (uY : Q' ≅ 𝟭 D)
    (K : C)
    (hp : B'.hom.app K ≫ F.map (cX.hom.app K) =
      cY.hom.app (F.obj K) ≫ Qi.map (B.hom.app K) ≫ Bi.hom.app (P.obj K))
    (hi : B'.hom.app K ≫ F.map (uX.hom.app K) = uY.hom.app (F.obj K)) :
    Qi.map (B.hom.app K) ≫ Bi.hom.app (P.obj K) ≫
      F.map ((cX.symm ≪≫ uX).hom.app K) =
    (cY.symm ≪≫ uY).hom.app (F.obj K) := by
  apply (cancel_epi (cY.hom.app (F.obj K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [Iso.hom_inv_id_app_assoc, ← reassoc_of% hp]
  simp only [← Functor.map_comp_assoc]
  rw [Iso.hom_inv_id_app, F.map_id, Category.id_comp]
  exact hi

private theorem finite_inverse
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) (K : proEtaleDerivedCategory X A) :
    (sfIntrinsicDerivedPullback A eY.inv).map
        ((automorphismStageFiniteSquare A f eX eY h).hom.app K) ≫
      (automorphismStageFiniteSquare A f eX.symm eY.symm
        (automorphismStage_inverseSquare f eX eY h)).hom.app
          ((sfIntrinsicDerivedPullback A eX.hom).obj K) ≫
      (sfIntrinsicDerivedPullback A f).map ((automorphismStageFiniteCancel A eX).hom.app K) =
    (automorphismStageFiniteCancel A eY).hom.app
      ((sfIntrinsicDerivedPullback A f).obj K) := by
  let w : (eY.inv ≫ eY.hom) ≫ f = f ≫ (eX.inv ≫ eX.hom) := by
    rw [eY.inv_hom_id, eX.inv_hom_id, Category.id_comp, Category.comp_id]
  have hp := finite_derived_pasting A f eX eY h w K
  have hi := finite_derived_identity A f _ _ eY.inv_hom_id eX.inv_hom_id w K
  have hi' := cancel_pasting (sfIntrinsicDerivedPullback A f)
    (sfIntrinsicDerivedPullback A eX.hom) (sfIntrinsicDerivedPullback A eX.inv)
    (sfIntrinsicDerivedPullback A (eX.inv ≫ eX.hom))
    (sfIntrinsicDerivedPullback A eY.hom) (sfIntrinsicDerivedPullback A eY.inv)
    (sfIntrinsicDerivedPullback A (eY.inv ≫ eY.hom))
    (sfIntrinsicDerivedSquarePullback A eY.hom f f eX.hom h)
    (sfIntrinsicDerivedSquarePullback A eY.inv f f eX.inv
      (automorphismStage_inverseSquare f eX eY h))
    (sfIntrinsicDerivedSquarePullback A (eY.inv ≫ eY.hom) f f
      (eX.inv ≫ eX.hom) w)
    (sfIntrinsicDerivedPullbackComp A eX.inv eX.hom)
    (sfIntrinsicDerivedPullbackComp A eY.inv eY.hom)
    (eqToIso (congrArg (sfIntrinsicDerivedPullback A) eX.inv_hom_id) ≪≫
      sfIntrinsicDerivedPullbackId A X)
    (eqToIso (congrArg (sfIntrinsicDerivedPullback A) eY.inv_hom_id) ≪≫
      sfIntrinsicDerivedPullbackId A Y) K hp hi
  rw [finite_square_derived A f eX eY h,
    finite_square_derived A f eX.symm eY.symm _]
  have hx (e : Aut X) : (sfIntrinsicDerivedPullbackComp A e.inv e.hom).symm ≪≫
      (eqToIso (congrArg (sfIntrinsicDerivedPullback A) e.inv_hom_id) ≪≫
        sfIntrinsicDerivedPullbackId A X) = automorphismStageFiniteCancel A e := rfl
  have hy (e : Aut Y) : (sfIntrinsicDerivedPullbackComp A e.inv e.hom).symm ≪≫
      (eqToIso (congrArg (sfIntrinsicDerivedPullback A) e.inv_hom_id) ≪≫
        sfIntrinsicDerivedPullbackId A Y) = automorphismStageFiniteCancel A e := rfl
  rw [hx, hy] at hi'
  exact hi'


/-- The finite commuting-square comparison respects shifts and inverse cancellation.
Source: Weil-structures paragraph, finite b and d coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the canonical module compositors are mates of reindexing compositors.
Their associativity and unit laws follow by identifying the same fibre products
and their projections. Termwise localization preserves these equations and shifts.
Paste the square for e with the square for its inverse; cancel the two inverse
composites. This is the second displayed equality. The identity square is the
same unit equation. -/
theorem automorphismConstructibleStage_finite_coherence
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    NatTrans.CommShift (automorphismStageFiniteSquare A f eX eY h).hom ℤ ∧
    (∀ K : proEtaleDerivedCategory X A,
      (sfIntrinsicDerivedPullback A eY.inv).map
          ((automorphismStageFiniteSquare A f eX eY h).hom.app K) ≫
        (automorphismStageFiniteSquare A f eX.symm eY.symm
          (automorphismStage_inverseSquare f eX eY h)).hom.app
            ((sfIntrinsicDerivedPullback A eX.hom).obj K) ≫
        (sfIntrinsicDerivedPullback A f).map ((automorphismStageFiniteCancel A eX).hom.app K) =
      (automorphismStageFiniteCancel A eY).hom.app
        ((sfIntrinsicDerivedPullback A f).obj K)) ∧
    (∀ K : proEtaleDerivedCategory X A,
      (automorphismStageFiniteSquare A f (Iso.refl X) (Iso.refl Y)
        ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app K ≫
          (sfIntrinsicDerivedPullback A f).map ((sfIntrinsicDerivedPullbackId A X).hom.app K) =
        (sfIntrinsicDerivedPullbackId A Y).hom.app ((sfIntrinsicDerivedPullback A f).obj K)) := by
  refine ⟨finite_shift A f eX eY h, finite_inverse A f eX eY h, ?_⟩
  intro K
  rw [show (automorphismStageFiniteSquare A f (Iso.refl X) (Iso.refl Y)
      ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app K =
      (sfIntrinsicDerivedSquarePullback A (𝟙 Y) f f (𝟙 X)
        ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app K from
    congrArg (fun b ↦ b.hom.app K)
      (finite_square_derived A f (Iso.refl X) (Iso.refl Y) _)]
  simpa only [eqToIso_refl, Iso.refl_trans] using
    finite_derived_identity A f (𝟙 Y) (𝟙 X) rfl rfl
      ((Category.id_comp f).trans (Category.comp_id f).symm) K

end FiniteCoherence

/-- The actual completion comparison is normalized by the actual reconstruction unit.
Source: Weil-structures paragraph, ordinary-to-completed comparison
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: identify ordinary inverse image with reindexing of one flat-term K-flat
resolution and its strict quotient tower. The Roos comparison preserves its
augmentation, with zero shifted-product coordinate. Its composite with the
specified ordinary-to-completed map is therefore inverse image of the actual
adjunction unit. Naturality descends from chain maps and localization. -/
theorem automorphismConstructibleStage_completion_unit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left)
    (S : CoefficientDerivedSystemCalculus l E T.left)
    (_hS : Nonempty (CoefficientDerivedSystemCoherence l E T.left S)) :
    ∃ θ : integralDerivedPullback l E e.hom ≅
        S.reduction ⋙ coefficientSequenceLimit l E T.left ⋙
          AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E e.hom,
      ∀ K : DerivedCategory (integralTowerModules l E T.left),
        AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived l E e.hom
            (automorphismConstructibleStage_units D l hl T).1
            (automorphismConstructibleStage_units D l hl T).1 K ≫ θ.hom.app K =
          (AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E e.hom).map
            (S.adjunction.unit.app K) := by
  classical
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact q.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := q
      a := 1
      q := q
      prime := hprime
      exponent_pos := le_refl 1
      cardinality_eq := (pow_one q).symm
      k₀ := ZMod q
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod q) }
  have hl₀ : l ≠ D₀.p := by
    change l ≠ q
    omega
  obtain ⟨N, _, hN⟩ := (sfIntegralConstructible l E T.left).exists_prop_of_containsZero
  let K₀ : sfIntegralConstructibleCategory l E T.left := ⟨N, hN⟩
  have hK₀ : IsDerivedCompleteUnrestricted l E T.left K₀.obj :=
    ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E T.left D₀ hl₀ K₀.obj).mp K₀.property.1⟩
  obtain ⟨θ, hθ, hn, _⟩ := isomorphismDerivedPullbackComparisonNormalization l E e.hom
    (automorphismConstructibleStage_units D l hl T).1
    (automorphismConstructibleStage_units D l hl T).1 S _hS K₀.obj hK₀
  exact ⟨NatIso.ofComponents θ (fun {K M} f ↦ hn K M f), hθ⟩

/-- Coherent reduction of automorphism pullback, normalized by every actual finite projection.
Source: Weil-structures paragraph, the displayed integral reduction isomorphism
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: use the one strict reduction tower of a flat-term K-flat representative.
Its quotient tensors and the reindexing pullback commute with all transitions.
The strict Roos comparison preserves the projections and its augmentation.
The counit of reduction/total-limit gives an isomorphism of the whole systems.
Evaluation is the adjoint of the defining finite Roos projection, transported by
the unit-normalized finite-pullback model: exactly the displayed rho, for every
representative, not just a collection of cohomology comparisons. -/
theorem automorphismConstructibleStage_reduction
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) :
    ∃ β : constructibleIntegralPullback l E e.hom ⋙ integralSystemReduction l E T.left ≅
        integralSystemReduction l E T.left ⋙
          finiteSystemDerivedPullback (integralSystemRings l E)
            (integralSystemTransition l E) e.hom,
      ∀ (K : sfIntegralConstructibleCategory l E T.left)
        (P : (integralOperationsGoodComplex l E T.left).FullSubcategory)
        (a : (DerivedCategory.Q (C := scalarReductionSource l E T.left)).obj P.obj ≅ K.obj)
        (n : ℕ),
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
            (integralSystemTransition l E) T.left n).map (β.hom.app K) ≫
          (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
            (integralSystemTransition l E) e.hom n).hom.app
              ((integralSystemReduction l E T.left).obj K) ≫
          (proEtaleConstantRingDerivedPullback (finiteCoefficientRing l E (n + 1)) e.hom).map
            ((integralSystemReductionEvaluation l E T.left n).hom.app K) =
        (integralSystemReductionEvaluation l E T.left n).hom.app
            ((constructibleIntegralPullback l E e.hom).obj K) ≫
          (integralSystemPullbackReductionIso l E e.hom K P a n).hom := by
  obtain ⟨β, hβ⟩ := integralPullbackSystemComparison l E
  exact ⟨β e.hom, hβ e.hom⟩

/-- Integral reduction in the prescribed intrinsic finite-coefficient coordinates.
Source: Weil-structures paragraph, displayed reduction comparison
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralFiniteReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (a : (DerivedCategory.Q (C := scalarReductionSource l E X)).obj P.obj ≅ K.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        ((constructibleIntegralPullback l E f).obj K).obj ≅
      (finiteDerivedPullback l E n f).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) :=
  integralSystemPullbackReductionIso l E f K P a n ≪≫
    (openSquareDerivedPullbackModel (finiteCoefficientRing l E (n + 1)) f).app
      ((scalarReductionDerivedExtension l E X n).obj K.obj)

section ScalarComparisonAgreement

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] integralDerivedPullback scalarPullbackCompleted
  integralComparisonLambda integralComparisonMu

/-- A simultaneous normalized calculus and its coherent scalar comparisons exist.
Source: Weil-structures paragraph, scalar-extension and composition coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: use the quotient coefficient diagrams simultaneously for all finite fields.
Their tensor generators fix the scalar units, associators and pullback compositors.
Derive these strict diagrams, apply their actual counits, and realize by Roos
limits. The identity, associativity and scalar equations on whole systems survive
realization. Uniqueness of the representative-normalized comparisons identifies
these with the scalar maps used by the prescribed common-stage operations. -/
theorem automorphismConstructibleStage_comparison_system (l : ℕ) [Fact l.Prime] :
    ∃ C : IntegralComparisonSystem.{u} l,
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
        (ι : E →ₐ[ℚ_[l]] L),
        IntegralComparisonRealizationCoherence l E L ι C ∧
        ∀ (X Y : Scheme.{u})
          [∀ x : X, Invertible (l : X.residueField x)]
          [∀ y : Y, Invertible (l : Y.residueField y)] (f : Y ⟶ X)
          (K : sfIntegralConstructibleCategory l E X),
          (integralComparisonScalar l E L ι C f K).hom =
            (integralPullbackScalarComparison l E L ι f K).hom.hom := by
  obtain ⟨C, hC⟩ := integralPullbackComparisonRealization_simultaneous.{u} l
  refine ⟨C, ?_⟩
  intro E _ _ _ L _ _ _ ι
  refine ⟨hC E L ι, ?_⟩
  intro X Y _ _ f K
  have h := integralScalarPullbackCompletion_normalization l E L ι C f K
    (((constructibleIntegralPullback l E f).obj K).property.1)
  simpa only [integralComparisonScalar, Iso.trans_hom, Iso.symm_hom,
    integralPullbackScalarComparison, ObjectProperty.isoMk, ObjectProperty.homMk] using
    ((Iso.eq_comp_inv (integralComparisonMu l E L ι C f K)).mpr h).symm

end ScalarComparisonAgreement

/-- Whole-system reduction comparison, with its prescribed counit normalization.
Source: Weil-structures paragraph, reduction and projection coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageSystemReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E X) :
    ((C.coefficient E).system Y).reduction.obj ((constructibleIntegralPullback l E f).obj K).obj ≅
      (integralComparisonDerivedSequencePullback l E f).obj
        (((C.coefficient E).system X).reduction.obj K.obj) :=
  @asIso _ _ _ _ _ ((C.coefficient E).effective f K)


/-- The entire finite-system square, using the specified system compositors.
Source: Weil-structures paragraph, finite reduction coherence of b and d
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageSystemSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequencePullback l E eY.hom ≅
      integralComparisonDerivedSequencePullback l E eX.hom ⋙
        integralComparisonDerivedSequencePullback l E f :=
  (integralComparisonSystemComposition l E eY.hom f).symm ≪≫
    eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) h) ≪≫
      integralComparisonSystemComposition l E f eX.hom




set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section ReductionCoherenceProof

set_option backward.defeqAttrib.useBackward false


set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback ObjectProperty.lift ObjectProperty.ι

private theorem counit_compositor
    {A B D : Type*} [Category A] [Category B] [Category D]
    (R : A ⥤ B) (L : B ⥤ A) (ε : L ⋙ R ⟶ 𝟭 B) (U : D ⥤ B)
    {X Y : A} {P : B} {Q Q' : D}
    (a : X ≅ L.obj P) (b : Y ≅ L.obj (U.obj Q)) (δ : Q ≅ Q') (c : P ≅ U.obj Q') :
    R.map ((a ≪≫ L.mapIso c ≪≫ (b ≪≫ L.mapIso (U.mapIso δ)).symm).hom) ≫
        (R.map b.hom ≫ ε.app (U.obj Q)) ≫ U.map δ.hom =
      (R.map a.hom ≫ ε.app P) ≫ c.hom := by
  let η := b ≪≫ L.mapIso (U.mapIso δ)
  have hn := ε.naturality (U.map δ.hom)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hb : R.map η.hom ≫ ε.app _ =
      (R.map b.hom ≫ ε.app _) ≫ U.map δ.hom := by
    simp only [η, Iso.trans_hom, Functor.mapIso_hom, R.map_comp, Category.assoc]
    rw [hn]
  rw [← hb]
  change R.map (a.hom ≫ L.map c.hom ≫ η.inv) ≫ (R.map η.hom ≫ _) = _
  simp only [R.map_comp, Category.assoc]
  have hi : R.map η.inv ≫ R.map η.hom = 𝟙 _ := by
    rw [← R.map_comp, Iso.inv_hom_id, R.map_id]
  rw [reassoc_of% hi]
  have hc := ε.naturality c.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]

private theorem integral_composition_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V) :
    ((C.coefficient E).system Z).reduction.map
        (integralComparisonComposition l E C h k K).hom ≫
      (automorphismStageSystemReduction l E C h
        ((constructibleIntegralPullback l E k).obj K)).hom ≫
      (integralComparisonDerivedSequencePullback l E h).map
        (automorphismStageSystemReduction l E C k K).hom =
    (automorphismStageSystemReduction l E C (h ≫ k) K).hom ≫
      (integralComparisonSystemComposition l E h k).hom.app
        (((C.coefficient E).system V).reduction.obj K.obj) := by
  exact counit_compositor
    ((C.coefficient E).system Z).reduction (coefficientSequenceLimit l E Z)
    ((C.coefficient E).system Z).adjunction.counit
    (integralComparisonDerivedSequencePullback l E h)
    (((C.coefficient E).pullback (h ≫ k)).realization.app K.obj)
    (((C.coefficient E).pullback h).realization.app
      ((constructibleIntegralPullback l E k).obj K).obj)
    (automorphismStageSystemReduction l E C k K)
    ((integralComparisonSystemComposition l E h k).app
      (((C.coefficient E).system V).reduction.obj K.obj))

private theorem reduction_square_paste
    {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {X Y X' Y' : A} {V W V' W' Z Z' : B}
    (a : X ≅ Y) (b : X' ≅ Y') (t : X ⟶ X') (v : Y ⟶ Y')
    (d₁ : R.obj Y ⟶ Z) (d₂ : Z ⟶ W)
    (d₁' : R.obj Y' ⟶ Z') (d₂' : Z' ⟶ W')
    (q : R.obj X ⟶ V) (q' : R.obj X' ⟶ V')
    (s : V ≅ W) (s' : V' ≅ W') (u : V ⟶ V')
    (ha : R.map a.hom ≫ d₁ ≫ d₂ = q ≫ s.hom)
    (hb : R.map b.hom ≫ d₁' ≫ d₂' = q' ≫ s'.hom)
    (ht : R.map t ≫ q' = q ≫ u) (hv : v = a.inv ≫ t ≫ b.hom) :
    R.map v ≫ d₁' ≫ d₂' = d₁ ≫ d₂ ≫ (s.inv ≫ u ≫ s'.hom) := by
  rw [hv]
  simp only [R.map_comp, Category.assoc]
  apply (cancel_epi (R.map a.hom)).1
  rw [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]
  rw [hb, reassoc_of% ha, Iso.hom_inv_id_assoc, reassoc_of% ht]

private theorem transport_family
    {A B D I : Type*} [Category A] [Category B] [Category D]
    (R : A ⥤ B) (F : I → A) (G : I → D ⥤ B) (N : D)
    (δ : ∀ i, R.obj (F i) ⟶ (G i).obj N) (i j : I) (h : i = j) :
    R.map (eqToHom (congrArg F h)) ≫ δ j =
      δ i ≫ (eqToIso (congrArg G h)).hom.app N := by
  cases h
  simp only [eqToHom_refl, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    R.map_id, Category.id_comp, Category.comp_id]

private theorem system_square_formula
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (_C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) (_K : sfIntegralConstructibleCategory l E X) :
    automorphismStageSystemSquare l E f eX eY h =
      (integralComparisonSystemComposition l E eY.hom f).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) h) ≪≫
          integralComparisonSystemComposition l E f eX.hom := by
  rfl

private theorem system_square_components
    {A B : Type*} [Category A] [Category B] {F G H I : A ⥤ B}
    (s : F ≅ G) (t : F ≅ H) (s' : H ≅ I) (N : A) :
    (s.symm ≪≫ t ≪≫ s').hom.app N = s.inv.app N ≫ t.hom.app N ≫ s'.hom.app N := by
  rfl

private theorem system_square_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) (K : sfIntegralConstructibleCategory l E X) :
    (automorphismStageSystemSquare l E f eX eY h).hom.app
        (((C.coefficient E).system X).reduction.obj K.obj) =
      (integralComparisonSystemComposition l E eY.hom f).inv.app
          (((C.coefficient E).system X).reduction.obj K.obj) ≫
        (eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) h)).hom.app
          (((C.coefficient E).system X).reduction.obj K.obj) ≫
        (integralComparisonSystemComposition l E f eX.hom).hom.app
          (((C.coefficient E).system X).reduction.obj K.obj) := by
  rw [system_square_formula l E C f eX eY h K]
  exact system_square_components
    (integralComparisonSystemComposition l E eY.hom f)
    (eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) h))
    (integralComparisonSystemComposition l E f eX.hom)
    (((C.coefficient E).system X).reduction.obj K.obj)

/-- The actual integral square reduces to the actual square of entire quotient diagrams.
Source: Weil-structures paragraph, coherence with finite reduction and projections
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: substitute the counit-built expressions for both compositors. The strict
system composition law identifies the two sides before total limit. The
completed-operation tower substitution theorem transports this equality, with
its augmentations and projections, to the actual integral maps. This uses whole
systems, rather than an unasserted faithfulness of individual finite reductions. -/
theorem automorphismConstructibleStage_square_reduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) (K : sfIntegralConstructibleCategory l E X) :
    ((C.coefficient E).system Y).reduction.map
        ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K).hom ≫
      (automorphismStageSystemReduction l E C f
        ((constructibleIntegralPullback l E eX.hom).obj K)).hom ≫
      (integralComparisonDerivedSequencePullback l E f).map
        (automorphismStageSystemReduction l E C eX.hom K).hom =
    (automorphismStageSystemReduction l E C eY.hom
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
      (integralComparisonDerivedSequencePullback l E eY.hom).map
        (automorphismStageSystemReduction l E C f K).hom ≫
      (automorphismStageSystemSquare l E f eX eY h).hom.app
        (((C.coefficient E).system X).reduction.obj K.obj) := by
  rw [system_square_component l E C f eX eY h K]
  simpa only [Iso.app_hom, Iso.app_inv] using
    reduction_square_paste ((C.coefficient E).system Y).reduction
      (integralComparisonComposition l E C eY.hom f K)
      (integralComparisonComposition l E C f eX.hom K)
      (eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h))
      ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K).hom
      (automorphismStageSystemReduction l E C eY.hom
        ((constructibleIntegralPullback l E f).obj K)).hom
      ((integralComparisonDerivedSequencePullback l E eY.hom).map
        (automorphismStageSystemReduction l E C f K).hom)
      (automorphismStageSystemReduction l E C f
        ((constructibleIntegralPullback l E eX.hom).obj K)).hom
      ((integralComparisonDerivedSequencePullback l E f).map
        (automorphismStageSystemReduction l E C eX.hom K).hom)
      (automorphismStageSystemReduction l E C (eY.hom ≫ f) K).hom
      (automorphismStageSystemReduction l E C (f ≫ eX.hom) K).hom
      ((integralComparisonSystemComposition l E eY.hom f).app
        (((C.coefficient E).system X).reduction.obj K.obj))
      ((integralComparisonSystemComposition l E f eX.hom).app
        (((C.coefficient E).system X).reduction.obj K.obj))
      ((eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) h)).hom.app
        (((C.coefficient E).system X).reduction.obj K.obj))
      (integral_composition_reduction l E C eY.hom f K)
      (integral_composition_reduction l E C f eX.hom K)
      (transport_family ((C.coefficient E).system Y).reduction
        (fun g : Y ⟶ X ↦ (integralDerivedPullback l E g).obj K.obj)
        (integralComparisonDerivedSequencePullback l E)
        (((C.coefficient E).system X).reduction.obj K.obj)
        (fun g ↦ (automorphismStageSystemReduction l E C g K).hom)
        (eY.hom ≫ f) (f ≫ eX.hom) h)
      ((automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose_spec K)


end ReductionCoherenceProof

/-- Scalar extension commutes with the specified commuting-square comparison.
Source: Weil-structures paragraph, common-stage scalar-extension coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: apply the normalized scalar/compositor equation to (eY,f) and (f,eX).
The equality of the two composite scheme maps identifies their scalar comparison.
Cancel the invertible compositors. This gives the equation on the full integral
maps. Its rationalization is the same equation after localization; the scalar
unit and associator equations make it independent of a chosen common field. -/
theorem automorphismConstructibleStage_square_scalar
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (C : IntegralComparisonSystem.{u} l)
    (_hC : IntegralComparisonRealizationCoherence l E L ι C) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E L ι Y).map
        ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K).hom ≫
      (integralComparisonScalar l E L ι C f
        ((constructibleIntegralPullback l E eX.hom).obj K)).hom ≫
      (integralDerivedPullback l L f).map
        (integralComparisonScalar l E L ι C eX.hom K).hom =
    (integralComparisonScalar l E L ι C eY.hom
        ((constructibleIntegralPullback l E f).obj K)).hom ≫
      (integralDerivedPullback l L eY.hom).map
        (integralComparisonScalar l E L ι C f K).hom ≫
      ((automorphismStageIntegralSquare l L C f eX eY h).hom.app
        ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have h₁ := congrArg (fun r ↦ r.hom) (_hC.scalarComposition eY.hom f K)
    have h₂ := congrArg (fun r ↦ r.hom) (_hC.scalarComposition f eX.hom K)
    dsimp only [integralComparisonScalarSquareLeft, integralComparisonScalarSquareRight,
      ObjectProperty.homMk_hom] at h₁ h₂
    have ht (g g' : Y ⟶ X) (w : g = g') :
        (integralScalarExtension l E L ι Y).map
            (eqToHom (congrArg (fun a ↦ (integralDerivedPullback l E a).obj K.obj) w)) ≫
          (integralComparisonScalar l E L ι C g' K).hom =
        (integralComparisonScalar l E L ι C g K).hom ≫
          eqToHom (congrArg (fun a ↦ (integralDerivedPullback l L a).obj
            ((integralComparisonConstructibleScalar l E L ι X).obj K).obj) w) := by
      subst g'
      simp only [eqToHom_refl, Category.comp_id]
      rw [(integralScalarExtension l E L ι Y).map_id, Category.id_comp]
    have hbE := (automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose_spec K
    have hbL := (automorphismStageIntegralSquare_existsUnique l L C f eX eY h).exists.choose_spec
      ((integralComparisonConstructibleScalar l E L ι X).obj K)
    change ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K).hom = _ at hbE
    change ((automorphismStageIntegralSquare l L C f eX eY h).hom.app
      ((integralComparisonConstructibleScalar l E L ι X).obj K)).hom = _ at hbL
    rw [hbE, hbL]
    simp only [(integralScalarExtension l E L ι Y).map_comp]
    apply (cancel_epi ((integralScalarExtension l E L ι Y).map
      (integralComparisonComposition l E C eY.hom f K).hom)).1
    simp only [Category.assoc]
    rw [← (integralScalarExtension l E L ι Y).map_comp_assoc,
      Iso.hom_inv_id, (integralScalarExtension l E L ι Y).map_id, Category.id_comp]
    rw [reassoc_of% h₁]
    rw [Iso.hom_inv_id_assoc]
    rw [h₂]
    rw [reassoc_of% (ht (eY.hom ≫ f) (f ≫ eX.hom) h)]


section IntegralCoherence

set_option backward.defeqAttrib.useBackward false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback ObjectProperty.lift ObjectProperty.ι
  Functor.comp Iso.refl Iso.symm
attribute [local irreducible] integralComparisonComposition integralComparisonUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (C : IntegralComparisonSystem.{u} l)

private theorem integral_comp_congr_inner
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (j : Z ⟶ W) {k k' : W ⟶ V} (w : k = k')
    (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonComposition l E C j k K).hom ≫
        (integralDerivedPullback l E j).map
          (eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) w)) =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj)
        (congrArg (fun k ↦ j ≫ k) w)) ≫
        (integralComparisonComposition l E C j k' K).hom := by
  cases w
  simp only [eqToHom_refl, (integralDerivedPullback l E j).map_id,
    Category.id_comp, Category.comp_id]

private theorem integral_comp_congr_outer
    {V W Z : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    {j j' : Z ⟶ W} (w : j = j') (k : W ⟶ V)
    (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonComposition l E C j k K).hom ≫
        eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj
          ((constructibleIntegralPullback l E k).obj K).obj) w) =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj)
        (congrArg (fun j ↦ j ≫ k) w)) ≫
        (integralComparisonComposition l E C j' k K).hom := by
  cases w
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem integral_associative_forward
    (hC : IntegralComparisonCompositionLaws l E C)
    {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
    (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonComposition l E C (j ≫ h) k K).hom ≫
        (integralComparisonComposition l E C j h
          ((constructibleIntegralPullback l E k).obj K)).hom =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj)
        (Category.assoc j h k)) ≫
        (integralComparisonComposition l E C j (h ≫ k) K).hom ≫
        (integralDerivedPullback l E j).map
          (integralComparisonComposition l E C h k K).hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact hC.associative j h k K

private theorem integral_associative_reverse
    (hC : IntegralComparisonCompositionLaws l E C)
    {V W Z Y : Scheme.{u}}
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (j : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V)
    (K : sfIntegralConstructibleCategory l E V) :
    (integralComparisonComposition l E C j (h ≫ k) K).hom ≫
        (integralDerivedPullback l E j).map
          (integralComparisonComposition l E C h k K).hom =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj)
        (Category.assoc j h k).symm) ≫
        (integralComparisonComposition l E C (j ≫ h) k K).hom ≫
        (integralComparisonComposition l E C j h
          ((constructibleIntegralPullback l E k).obj K)).hom := by
  have ht := congrArg
    (fun z ↦ eqToHom (congrArg
      (fun g ↦ (integralDerivedPullback l E g).obj K.obj) (Category.assoc j h k).symm) ≫ z)
    (integral_associative_forward l E C hC j h k K)
  simpa only [@Category.assoc (DerivedCategory (integralTowerModules l E Y)) _,
    eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] using ht.symm

private theorem integral_square_horizontal
    (hC : IntegralComparisonCompositionLaws l E C)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (a c : Y ⟶ Y) (b d : X ⟶ X)
    (h : a ≫ f = f ≫ b) (h' : c ≫ f = f ≫ d)
    (w : (c ≫ a) ≫ f = f ≫ (d ≫ b))
    (K : sfIntegralConstructibleCategory l E X) :
    ((integralComparisonComposition l E C (c ≫ a) f K).inv ≫
        eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) w) ≫
        (integralComparisonComposition l E C f (d ≫ b) K).hom) ≫
        (integralDerivedPullback l E f).map
          (integralComparisonComposition l E C d b K).hom =
      (integralComparisonComposition l E C c a
          ((constructibleIntegralPullback l E f).obj K)).hom ≫
        (integralDerivedPullback l E c).map
          ((integralComparisonComposition l E C a f K).inv ≫
            eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
            (integralComparisonComposition l E C f b K).hom) ≫
        (integralComparisonComposition l E C c f
          ((constructibleIntegralPullback l E b).obj K)).inv ≫
        eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj
          ((constructibleIntegralPullback l E b).obj K).obj) h') ≫
        (integralComparisonComposition l E C f d
          ((constructibleIntegralPullback l E b).obj K)).hom := by
  apply (cancel_epi (integralComparisonComposition l E C (c ≫ a) f K).hom).1
  simp only [@Category.assoc (DerivedCategory (integralTowerModules l E Y)) _, Iso.hom_inv_id_assoc]
  symm
  rw [reassoc_of% (integral_associative_forward l E C hC c a f K)]
  simp only [(integralDerivedPullback l E c).map_comp, Category.assoc]
  simp only [← (integralDerivedPullback l E c).map_comp_assoc, Iso.hom_inv_id_assoc]
  simp only [(integralDerivedPullback l E c).map_comp, Category.assoc]
  rw [reassoc_of% (integral_comp_congr_inner l E C c h K)]
  rw [reassoc_of% (integral_associative_reverse l E C hC c f b K)]
  rw [Iso.hom_inv_id_assoc]
  rw [reassoc_of% (integral_comp_congr_outer l E C h' b K)]
  rw [integral_associative_forward l E C hC f d b K]
  simp only [eqToHom_trans_assoc]

private theorem integral_square_identity
    (hC : IntegralComparisonCompositionLaws l E C)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (a : Y ⟶ Y) (b : X ⟶ X)
    (ha : a = 𝟙 Y) (hb : b = 𝟙 X) (w : a ≫ f = f ≫ b)
    (K : sfIntegralConstructibleCategory l E X) :
    ((integralComparisonComposition l E C a f K).inv ≫
        eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) w) ≫
        (integralComparisonComposition l E C f b K).hom) ≫
      (integralDerivedPullback l E f).map
        (eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) hb) ≫
          (integralComparisonUnit l E C X K).hom) =
      eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj
        ((constructibleIntegralPullback l E f).obj K).obj) ha) ≫
        (integralComparisonUnit l E C Y
          ((constructibleIntegralPullback l E f).obj K)).hom := by
  subst a
  subst b
  simp only [eqToHom_refl, Category.id_comp]
  apply (cancel_epi (integralComparisonComposition l E C (𝟙 Y) f K).hom).1
  simp only [@Category.assoc (DerivedCategory (integralTowerModules l E Y)) _]
  rw [Iso.hom_inv_id_assoc, hC.unitTarget f K, hC.unitSource f K]
  simp only [eqToHom_trans]

/-- The actual integral commuting-square maps respect inverse cancellation and units.
Source: Weil-structures paragraph, identity and inverse coherence
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: the whole-system unit and associativity equations hold before realization.
The normalized total-limit compositor transports them to integral pullback.
Paste the squares for e and its inverse and use the two canonical cancellations.
The identity square is the corresponding unit equation. These are equalities of
actual derived morphisms, not assertions detected only after finite reduction. -/
theorem automorphismConstructibleStage_integral_coherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) (_hC : IntegralComparisonCompositionLaws l E C)
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    (∀ K : sfIntegralConstructibleCategory l E X,
      (integralDerivedPullback l E eY.inv).map
          ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K).hom ≫
        ((automorphismStageIntegralSquare l E C f eX.symm eY.symm
          (automorphismStage_inverseSquare f eX eY h)).hom.app
            ((constructibleIntegralPullback l E eX.hom).obj K)).hom ≫
        (integralDerivedPullback l E f).map (automorphismStageIntegralCancel l E C eX K).hom =
      (automorphismStageIntegralCancel l E C eY
        ((constructibleIntegralPullback l E f).obj K)).hom) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      ((automorphismStageIntegralSquare l E C f (Iso.refl X) (Iso.refl Y)
        ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app K).hom ≫
          (integralDerivedPullback l E f).map (integralComparisonUnit l E C X K).hom =
        (integralComparisonUnit l E C Y ((constructibleIntegralPullback l E f).obj K)).hom) := by
  constructor
  · intro K
    have hb := (automorphismStageIntegralSquare_existsUnique l E C f eX eY h).exists.choose_spec K
    have hbi := (automorphismStageIntegralSquare_existsUnique l E C f eX.symm eY.symm
      (automorphismStage_inverseSquare f eX eY h)).exists.choose_spec
      ((constructibleIntegralPullback l E eX.hom).obj K)
    change ((automorphismStageIntegralSquare l E C f eX eY h).hom.app K).hom = _ at hb
    change ((automorphismStageIntegralSquare l E C f eX.symm eY.symm
      (automorphismStage_inverseSquare f eX eY h)).hom.app
      ((constructibleIntegralPullback l E eX.hom).obj K)).hom = _ at hbi
    let w : (eY.inv ≫ eY.hom) ≫ f = f ≫ (eX.inv ≫ eX.hom) := by
      rw [eY.inv_hom_id, eX.inv_hom_id, Category.id_comp, Category.comp_id]
    have hp := integral_square_horizontal l E C _hC f eY.hom eY.inv eX.hom eX.inv h
      (automorphismStage_inverseSquare f eX eY h) w K
    have hi := integral_square_identity l E C _hC f _ _
      eY.inv_hom_id eX.inv_hom_id w K
    rw [hb, hbi]
    simp only [automorphismStageIntegralCancel, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, Category.assoc]
    apply (cancel_epi (integralComparisonComposition l E C eY.inv eY.hom
      ((constructibleIntegralPullback l E f).obj K)).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← reassoc_of% hp]
    rw [← (integralDerivedPullback l E f).map_comp, Iso.hom_inv_id_assoc]
    simpa only [@Category.assoc (DerivedCategory (integralTowerModules l E Y)) _] using hi
  · intro K
    have hb := (automorphismStageIntegralSquare_existsUnique l E C f
      (Iso.refl X) (Iso.refl Y)
      ((Category.id_comp f).trans (Category.comp_id f).symm)).exists.choose_spec K
    change ((automorphismStageIntegralSquare l E C f (Iso.refl X) (Iso.refl Y)
      ((Category.id_comp f).trans (Category.comp_id f).symm)).hom.app K).hom = _ at hb
    rw [hb]
    simpa only [eqToHom_refl, Category.id_comp] using
      integral_square_identity l E C _hC f (𝟙 Y) (𝟙 X) rfl rfl
        ((Category.id_comp f).trans (Category.comp_id f).symm) K


end IntegralCoherence

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the recorded pullback interfaces opaque while checking their shift structures.
set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback integralDerivedPullback
  rationalDerivedPullback commonStageDerivedPullback

/-- A restricted integral shift is the signed Roos shift descended from good representatives.
This predicate only spells out the normalization of the comparison in this node.
Source: Weil-structures paragraph, canonical shift clause
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageIntegralShiftNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : (constructibleIntegralPullback l E f).CommShift ℤ) : Prop :=
  ∃ (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (d : (integralDerivedPullback l E f).CommShift ℤ),
    IntegralCompletedComparison.ShiftCoordinates l E f c ∧
      IntegralCompletedComparison.ShiftDescent l E f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l E X) (r : ℤ),
        HEq (((constructibleIntegralPullback l E f).commShiftIso (self := s) r).hom.app K).hom
          (((integralDerivedPullback l E f).commShiftIso (self := d) r).hom.app K.obj)

/-- The rational shift is precisely the localization of the normalized integral shift.
Source: Weil-structures paragraph, rationalization of shifts
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageRationalShiftNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : (rationalDerivedPullback l E f).CommShift ℤ) : Prop :=
  ∃ c : (constructibleIntegralPullback l E f).CommShift ℤ,
    automorphismStageIntegralShiftNormalization l E f c ∧
      ∀ (K : sfRationalConstructibleCategory l E X) (r : ℤ),
        HEq (((rationalDerivedPullback l E f).commShiftIso (self := s) r).hom.app K)
          ((sfRationalConstructibleLocalization l E Y).map
            (((constructibleIntegralPullback l E f).commShiftIso (self := c) r).hom.app K.obj))

/-- The algebraically closed shift is the same normalized rational shift in every finite stage.
Source: Weil-structures paragraph, coherent finite-field descent of shifts
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
def automorphismStageQbarShiftNormalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (s : (commonStageDerivedPullback l Ω f).CommShift ℤ) : Prop :=
  ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ c : (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).CommShift ℤ,
      automorphismStageRationalShiftNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f c ∧
      ∀ (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) (r : ℤ),
        HEq (((commonStageDerivedPullback l Ω f).commShiftIso (self := s) r).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := X) E).obj K))
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := Y) E).map
            (((rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) f).commShiftIso
                (self := c) r).hom.app K))

/-- Canonical signed shifts descend to all the integral pullbacks in a commuting square.
Source: Weil-structures paragraph, canonical shift comparisons
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: shift the good representative and its quotient tower termwise. The product
shift fixes the unshifted Roos coordinate and multiplies the shifted coordinate
by (-1)^r. This is precisely ShiftCoordinates. Localization gives ShiftDescent.
The full constructible inclusion inherits that shift comparison. The specified
compositors come from the same shifted system maps, so their square commutes
with shifts. Cone sequences of representatives are termwise split and preserved
by the entire construction, proving exactness. -/
theorem automorphismConstructibleStage_integral_shifts
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    (∀ (Z W : Scheme.{u}) (g : Z ⟶ W),
      ∃ (c : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
        (d : (integralDerivedPullback l E g).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E g c ∧
          IntegralCompletedComparison.ShiftDescent l E g c d) ∧
    ∃ (cf : (constructibleIntegralPullback l E f).CommShift ℤ)
      (cX : (constructibleIntegralPullback l E eX.hom).CommShift ℤ)
      (cY : (constructibleIntegralPullback l E eY.hom).CommShift ℤ),
      automorphismStageIntegralShiftNormalization l E f cf ∧
      automorphismStageIntegralShiftNormalization l E eX.hom cX ∧
      automorphismStageIntegralShiftNormalization l E eY.hom cY ∧
      (fun [sf : (constructibleIntegralPullback l E f).CommShift ℤ]
        [sX : (constructibleIntegralPullback l E eX.hom).CommShift ℤ]
        [sY : (constructibleIntegralPullback l E eY.hom).CommShift ℤ] ↦
        (constructibleIntegralPullback l E f).IsTriangulated ∧
          (constructibleIntegralPullback l E eX.hom).IsTriangulated ∧
          (constructibleIntegralPullback l E eY.hom).IsTriangulated ∧
          NatTrans.CommShift (automorphismStageIntegralSquare l E C f eX eY h).hom ℤ)
        (sf := cf) (sX := cX) (sY := cY) := by
  sorry

/-- The rational and common-stage square comparisons preserve the descended shifts.
Source: Weil-structures paragraph, rationalization and coherent finite-field descent
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: extend the integral shift comparisons and square components by linearity
on pure tensors. Their equations remain equalities after rationalization.
At algebraically closed coefficients represent each arrow at one finite common
stage. The scalar/compositor and scalar/shift squares identify every enlargement
with the same equation. Thus the shift-compatible square descends. -/
theorem automorphismConstructibleStage_descended_shifts
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      ∃ (cf : (rationalDerivedPullback l E f).CommShift ℤ)
        (cX : (rationalDerivedPullback l E eX.hom).CommShift ℤ)
        (cY : (rationalDerivedPullback l E eY.hom).CommShift ℤ),
        automorphismStageRationalShiftNormalization l E f cf ∧
        automorphismStageRationalShiftNormalization l E eX.hom cX ∧
        automorphismStageRationalShiftNormalization l E eY.hom cY ∧
        (fun [sf : (rationalDerivedPullback l E f).CommShift ℤ]
          [sX : (rationalDerivedPullback l E eX.hom).CommShift ℤ]
          [sY : (rationalDerivedPullback l E eY.hom).CommShift ℤ] ↦
          (rationalDerivedPullback l E f).IsTriangulated ∧
            (rationalDerivedPullback l E eX.hom).IsTriangulated ∧
            (rationalDerivedPullback l E eY.hom).IsTriangulated ∧
            NatTrans.CommShift (automorphismStageRationalSquare l E C f eX eY h).hom ℤ)
          (sf := cf) (sX := cX) (sY := cY)) ∧
    ∃ (cf : (commonStageDerivedPullback l Ω f).CommShift ℤ)
      (cX : (commonStageDerivedPullback l Ω eX.hom).CommShift ℤ)
      (cY : (commonStageDerivedPullback l Ω eY.hom).CommShift ℤ),
      automorphismStageQbarShiftNormalization l Ω f cf ∧
      automorphismStageQbarShiftNormalization l Ω eX.hom cX ∧
      automorphismStageQbarShiftNormalization l Ω eY.hom cY ∧
      (fun [sf : (commonStageDerivedPullback l Ω f).CommShift ℤ]
        [sX : (commonStageDerivedPullback l Ω eX.hom).CommShift ℤ]
        [sY : (commonStageDerivedPullback l Ω eY.hom).CommShift ℤ] ↦
        (commonStageDerivedPullback l Ω f).IsTriangulated ∧
          (commonStageDerivedPullback l Ω eX.hom).IsTriangulated ∧
          (commonStageDerivedPullback l Ω eY.hom).IsTriangulated ∧
          NatTrans.CommShift (automorphismStageQbarSquare l Ω C f eX eY h).hom ℤ)
        (sf := cf) (sX := cX) (sY := cY) := by
  sorry

attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] sfIntegralConstructibleLinear

/-- Cache the canonical linear structure on the named finite stage.
Source: Weil-structures paragraph, finite-field coefficient linearity
(blueprint: lem-sf-automorphism-constructible-stage-equivalence). -/
instance automorphismConstructibleStage_stageLinear
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    Linear (Localization.Away (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)))
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  @ScalarLocalization.linear (Padic.coefficientExtensionIntegers l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)) inferInstance
    (sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) T)
    inferInstance inferInstance
    (sfIntegralConstructibleLinear l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) T)
    (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E))

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
attribute [local instance 5000] automorphismConstructibleStage_stageLinear
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stagePreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Linearity over every finite field containing an algebraically closed coefficient scalar.
Source: Weil-structures paragraph, algebraically closed coefficient linearity
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: express the scalar and the arrow in a common finite coefficient field.
The rational functor there is linear. Conjugation by the two prescribed scalar
comparisons is linear too. Its equality descends through the actual common-stage
quotient, independently of further enlargement. Every scalar of the algebraic
closure belongs to such a finite field, so this is coefficient linearity. -/
theorem automorphismConstructibleStage_qbar_linear
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left)
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω T.left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)))
    (r : P.toStage hP ⟶ Q.toStage hQ) :
    HEq ((commonStageDerivedPullback l Ω e.hom).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ (a • r)))
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω e.hom P) (commonStagePullbackObject l Ω e.hom Q)
        L hP hQ
        (a • ((commonStagePullbackComparison l Ω e.hom P L hP).hom ≫
          (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            e.hom).map r ≫ (commonStagePullbackComparison l Ω e.hom Q L hQ).inv))) := by
  have hlin := (automorphismConstructibleStage_integral_rational D l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) T e).2.2.2.2.2.2.1
  exact commonStageDerivedPullback_map_smul_of_linear l Ω e.hom P Q L hP hQ hlin a r




set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback

/-- The inverse comparisons at all three infinite coefficient stages have their specified values.
Applying this to the inverse automorphism gives the other inverse-composition comparison.
Source: Weil-structures paragraph, canonical inverse comparisons and their descent
(blueprint: lem-sf-automorphism-constructible-stage-equivalence).
Proof: specialize the existing isomorphism transport theorem. The integral
normalization lemma identifies its epsilon with the prescribed compositor
inverse followed by the identity unit. Its rational epsilon already has the
specified localization formula. Equality of integral components identifies the
epsilon natural transformations for independently chosen finite-stage witnesses.
Their rational formulas then identify their rational components. Mapping that
equality through the common-stage inclusion gives the required last formula. -/
theorem automorphismConstructibleStage_inverse_comparisons
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l)
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] (e : Aut T.left) :
    ∃ a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
        constructibleIntegralPullback l E e.hom ⋙ constructibleIntegralPullback l E e.inv ≅ 𝟭 _,
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfIntegralConstructibleCategory l E T.left),
        ((a E).hom.app K).hom = (automorphismStageIntegralCancel l E C e K).hom) ∧
      ∃ b : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
          rationalDerivedPullback l E e.hom ⋙ rationalDerivedPullback l E e.inv ≅ 𝟭 _,
        (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
          (K : sfRationalConstructibleCategory l E T.left),
          HEq ((b E).hom.app K)
            ((sfRationalConstructibleLocalization l E T.left).map ((a E).hom.app K.obj))) ∧
        ∃ c : commonStageDerivedPullback l Ω e.hom ⋙
            commonStageDerivedPullback l Ω e.inv ≅ 𝟭 _,
          ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω T.left,
            HEq (c.hom.app K)
              ((GeneralAlgebraicallyClosedCoefficients.inclusion
                (l := l) (Ω := Ω) (Y := T.left) K.stage).map
                ((b (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).hom.app
                  K.obj)) := by
  classical
  obtain ⟨g, hg, he⟩ : ∃ (g : T.left ⟶ T.left) (hg : IsIso g),
      e = (letI : IsIso g := hg; asIso g) := by
    refine ⟨e.hom, inferInstance, ?_⟩
    apply Iso.ext
    rfl
  let : IsIso g := hg
  cases he
  let e : Aut T.left := asIso g
  let i : ∀ x : T.left, Invertible (l : T.left.residueField x) := inferInstance
  have hft : LocallyOfFiniteType T.hom := inferInstance
  have hqc : QuasiCompact T.hom := inferInstance
  let : T.left.Over (Spec (.of D.k)) := ⟨T.hom⟩
  let : LocallyOfFiniteType (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hft
  let : QuasiCompact (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hqc
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨iX, iY, h⟩ := isomorphismFieldTransport D l (Fact.out : l ≠ D.p) Ω e.hom
  have hiX : iX = i := Subsingleton.elim _ _
  have hiY : iY = i := Subsingleton.elim _ _
  cases hiX
  cases hiY
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨hX, hY, hS, _, S, _, _, ⟨A⟩, _⟩ := h
  let stage (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    Classical.choice (hS E).1
  simp only [automorphismStageIntegralCancel]
  let cancel (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfIntegralConstructibleCategory l E T.left) :
      ((constructibleIntegralPullback l E e.hom ⋙
        constructibleIntegralPullback l E (inv e.hom)).obj K).obj ⟶ K.obj :=
    (((integralComparisonComposition l E C (inv e.hom) e.hom K).symm ≪≫
      eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj)
        (IsIso.inv_hom_id e.hom)) ≪≫ integralComparisonUnit l E C T.left K :
      ((constructibleIntegralPullback l E e.hom ⋙
        constructibleIntegralPullback l E (inv e.hom)).obj K).obj ≅ K.obj).hom)
  have hn (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (B : IsomorphismFieldTransportStage l E e.hom hX hY)
      (K : sfIntegralConstructibleCategory l E T.left) :
      HEq (B.epsilon.hom.app K).hom (cancel E K) := by
    exact (B.epsilon_formula K).trans
      (integralAutomorphismCancellation_normalization l E C e.hom K)
  let a (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    (stage E).epsilon
  let b (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    (stage E).rationalEpsilon
  have hb (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfRationalConstructibleCategory l E T.left) :
      HEq ((b E).hom.app K)
        ((sfRationalConstructibleLocalization l E T.left).map ((a E).hom.app K.obj)) :=
    (stage E).rational_epsilon_formula K
  refine ⟨a, ?_, b, hb, A.epsilon, ?_⟩
  · intro E _ _ _ K
    apply eq_of_heq
    simpa only [a, cancel, e, asIso_hom, asIso_inv] using hn E (stage E) K
  · intro K
    have he : (S K.stage).epsilon =
        (stage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).epsilon := by
      apply Iso.ext
      apply NatTrans.ext
      funext J
      apply ObjectProperty.hom_ext
      exact eq_of_heq ((hn _ (S K.stage) J).trans (hn _ (stage _) J).symm)
    have hr := (S K.stage).rational_epsilon_formula K.obj
    rw [he] at hr
    have hrat : (S K.stage).rationalEpsilon.hom.app K.obj =
        (b (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).hom.app K.obj :=
      eq_of_heq (hr.trans (hb _ K.obj).symm)
    exact (A.epsilon_formula K).trans (heq_of_eq (congrArg
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := T.left) K.stage).map) hrat))

end WeilConjectures
