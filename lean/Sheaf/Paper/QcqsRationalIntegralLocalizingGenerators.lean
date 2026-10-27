/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.Defs.Filter
import all Sheaf.SixFunctors.IntegralModelsGenerators
import Sheaf.Paper.QcqsIntegralScalarExtensionCTF
import Sheaf.Paper.QcqsLatticeTreeReconstruction
import Sheaf.Paper.QcqsConstructibleIntegralLeafModels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Integral generators for qcqs rational constructible complexes

Source: blueprint main-20261015, det-sf-comp-coherence-refinement.proof.md, (2),
coefficient devissage for the closed-complement calculation
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators).

The algebraic-closure coefficient is the finite-subextension-valued condensed ring.
Both conclusions take place in the ordinary unbounded module-object derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

attribute [-instance] WeilConjectures.SixFunctors.integralModel_coefficientMonObj

attribute [local irreducible] upperStarFromPoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars CondensedRing.upperStar
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 20000]
  CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit
  CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape

set_option maxSynthPendingDepth 0

attribute [local instance 2000] CategoryTheory.Sheaf.instHasColimitsOfSize
  CategoryTheory.Sheaf.instHasColimitsOfShape CategoryTheory.Sheaf.instHasFiniteColimits
  CategoryTheory.Sheaf.hasLimitsOfSize CategoryTheory.Sheaf.instHasFiniteLimits
  CategoryTheory.Mod.monoidalCategory AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf

attribute [local irreducible] Mod.monoidalClosed Mod.monoidalCategory
  Mod.monoidalCategoryStruct

/-- The integral scalar-extension generators for the single coefficient field E.
The existential is closed under ambient isomorphisms, with no restriction on morphisms.
Source: blueprint refinement (2), definition of G_V
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators). -/
def rationalIntegralGenerators (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (V : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) V))) :=
  fun K ↦ ∃ J : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ E) V,
    Nonempty (((Mod.extendScalars (padicIntegersToPadicSubfield V ℓ E)).leftDerivedFunctor).obj
      J.obj ≅ K)

set_option synthInstance.maxHeartbeats 80000 in
-- The composite coefficient map makes the generic K-flat instance search larger.
/-- The integral scalar-extension generators for the finite-subextension-valued closure.
Every finite subextension is allowed, and the coefficient map is its actual inclusion.
Source: blueprint refinement (2), definition of G_V
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators). -/
def algClIntegralGenerators (ℓ : ℕ) [Fact ℓ.Prime] (V : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) V))) :=
  fun K ↦ ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (J : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ F) V),
    Nonempty (((Mod.extendScalars (padicIntegersToPadicSubfield V ℓ F ≫
      padicSubfieldRingObjToPadicAlgCl V ℓ F)).leftDerivedFunctor).obj J.obj ≅ K)

private theorem generator_derived_coeff_iso
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (V : Scheme.{u})
    (a b : condensedRingObj A V ⟶ condensedRingObj B V) [IsMonHom a] [IsMonHom b]
    (h : a = b) (J : DerivedCategory (LatticeTree.Modules A V)) :
    Nonempty (((Mod.extendScalars a).leftDerivedFunctor).obj J ≅
      ((Mod.extendScalars b).leftDerivedFunctor).obj J) := by
  subst b
  exact ⟨Iso.refl _⟩

private theorem generator_finite_model_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (V : Scheme.{u}) {M N : LatticeTree.Modules R V} (e : M ≅ N)
    (hM : HasFiniteConstantLocalModel R V M) : HasFiniteConstantLocalModel R V N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU a
  exact ⟨P, hP, ⟨((CondensedRing.upperStar R (U.f a)).mapIso e.symm) ≪≫ eP⟩⟩

private theorem generator_model_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (V : Scheme.{u}) {M N : LatticeTree.Modules R V} (e : M ≅ N)
    (hM : IsConstantModelConstructible R V M) : IsConstantModelConstructible R V N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢
  · obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun i ↦ generator_finite_model_iso R _
      ((CondensedRing.upperStar R (S.immersion i)).mapIso e) (hS i)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := hM U hU
    exact ⟨S, fun i ↦ generator_finite_model_iso R _
      ((CondensedRing.upperStar R (S.immersion i)).mapIso
        ((CondensedRing.upperStar R U.ι).mapIso e)) (hS i)⟩

private theorem generator_ctf_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (V : Scheme.{u}) {K L : DerivedCategory (LatticeTree.Modules R V)} (e : K ≅ L)
    (hK : constantModelBoundedConstructible R V K ∧ _root_.DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible R V L ∧ _root_.DerivedCategory.finiteTorAmplitude _ L := by
  exact ⟨⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1.1,
    fun q ↦ generator_model_iso R V ((DerivedCategory.homologyFunctor _ q).mapIso e)
      (hK.1.2 q)⟩, (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e hK.2⟩

private theorem generator_iter_iso
    {C : Type*} [Category C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (n : ℕ) :
    (P.extensionProductIter n).IsClosedUnderIsomorphisms := by
  cases n with
  | zero => rw [ObjectProperty.extensionProductIter_zero]; infer_instance
  | succ n => rw [ObjectProperty.extensionProductIter_succ]; infer_instance

private theorem generator_finite_to_localizing
    {C : Type*} [Category C] [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (G : ObjectProperty C) {K : C}
    (hK : ∃ n, (G.shiftClosure ℤ).extensionProductIter n K) : localizingClosure G K := by
  intro P hP hG
  let := hP.1
  let := hP.2.1
  obtain ⟨n, hn⟩ := hK
  exact ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂ (G.shiftClosure ℤ)
    ((ObjectProperty.shiftClosure_le_iff G P).mpr hG) n K hn

private theorem generator_bounded
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (V : Scheme.{u}) (G : ObjectProperty (DerivedCategory (LatticeTree.Modules R V)))
    (hgen : ∀ M : LatticeTree.Modules R V, IsConstantModelConstructible R V M →
      ∃ n, (G.shiftClosure ℤ).extensionProductIter n (LatticeTree.single R V M))
    (K : DerivedCategory (LatticeTree.Modules R V))
    (hK : constantModelBoundedConstructible R V K) :
    ∃ n, (G.shiftClosure ℤ).extensionProductIter n K := by
  let P := G.shiftClosure ℤ
  let Q : ObjectProperty (DerivedCategory (LatticeTree.Modules R V)) :=
    fun K ↦ ∃ n, P.extensionProductIter n K
  have (n : ℕ) : (P.extensionProductIter n).IsClosedUnderIsomorphisms :=
    generator_iter_iso P n
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    rintro K L e ⟨n, hn⟩
    exact ⟨n, (P.extensionProductIter n).prop_of_iso e hn⟩⟩
  let H : ObjectProperty (LatticeTree.Modules R V) := IsConstantModelConstructible R V
  have : H.IsClosedUnderIsomorphisms := ⟨generator_model_iso R V⟩
  apply DerivedCategory.prop_of_bounded_of_degreewise Q ?_ ?_ (fun _ ↦ H) ?_ K hK.1 hK.2
  · intro M hM
    obtain ⟨n, hn⟩ := hgen 0
      (constantModelConstructible_of_isZero R V 0 (isZero_zero _))
    exact ⟨n, (P.extensionProductIter n).prop_of_iso
      (((DerivedCategory.singleFunctor _ 0).map_isZero (isZero_zero _)).iso hM) hn⟩
  · intro T hT h₁ h₃
    obtain ⟨n, hn⟩ := h₁
    obtain ⟨m, hm⟩ := h₃
    refine ⟨n + 1 + m, ?_⟩
    rw [ObjectProperty.extensionProductIter_add P rfl]
    exact ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, hn, hm⟩
  · intro q M hM
    obtain ⟨n, hn⟩ := hgen M hM
    exact ⟨n, (P.extensionProductIter n).prop_of_iso
      (((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by omega)).app M)
      ((P.extensionProductIter n).le_shift (-q) _ hn)⟩

private theorem generator_path_qcqs {V W : Scheme.{u}} {t : QcqsOpenClosedTree V}
    (p : t.Path W) : CompactSpace W ∧ QuasiSeparatedSpace W := by
  induction p with
  | root t => cases t <;> exact ⟨inferInstance, inferInstance⟩
  | openBranch _ _ _ _ _ _ ih => exact ih
  | closedBranch _ _ _ _ _ _ ih => exact ih

private theorem generator_sheaf
    (ℓ : ℕ) [Fact ℓ.Prime] {I : Type}
    (F : I → PadicAlgCl.FiniteIntermediateField ℓ)
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (a : ∀ i : I, Profinite.padicIntegersRingObj.{u} ℓ (F i).1 ⟶ R)
    [∀ i : I, IsMonHom (a i)] (V : Scheme.{u})
    (G : ObjectProperty (DerivedCategory (LatticeTree.Modules R V)))
    (hG : ∀ (i : I) (J : ConstantModelConstructibleFiniteTor
        (Profinite.padicIntegersRingObj ℓ (F i).1) V) (K),
      Nonempty ((((Mod.extendScalars (coefficientMap (a i) V)).leftDerivedFunctor).obj
        J.obj) ≅ K) → G K)
    (hrec : LatticeTree.Reconstruction ℓ I F R a)
    (hflat : ∀ (W : Scheme.{u}) [CompactSpace W] [QuasiSeparatedSpace W] (i : I),
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a i) W)))
    (M : LatticeTree.Modules R V) (t : QcqsOpenClosedTree V)
    (d : LatticeTree.LeafModels ℓ I F R a t M) :
    ∃ n, (G.shiftClosure ℤ).extensionProductIter n (LatticeTree.single R V M) := by
  have hfl (W : Scheme.{u}) (p : t.Path W) (i : I) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a i) W)) := by
    let := (generator_path_qcqs p).1
    let := (generator_path_qcqs p).2
    exact hflat W i
  obtain ⟨hbranch, n, hn⟩ := (hrec V t hfl).2 M d
  refine ⟨n, ObjectProperty.monotone_extensionProductIter ?_ n _ hn⟩
  rintro K ⟨w, ⟨e⟩⟩
  obtain ⟨hc, ht, _, ⟨es⟩⟩ := hbranch w
  apply ObjectProperty.le_shiftClosure
  exact hG (d.fieldIndex w) ⟨_, hc, ht⟩ K ⟨es ≪≫ e.symm⟩

/-- Integral scalar extensions are constructible of finite Tor amplitude, and every
bounded constructible finite-Tor complex is in their ambient localizing hull. In fact it
is a finite iterated extension of shifts of those generators. All triangle maps are
arbitrary ambient linear maps; no finite-field descent of maps or complexes is claimed.

Source: blueprint refinement (2), coefficient devissage
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators).

Proof plan (the complete DAG proof, with the finite-field case omitting closure descent):
1. Work with the section-ring sheaves of the pulled-back ring objects. The equivalence
[lem-sfb-module-object-ringed-site-derived-comparison] leaves underlying sheaves and maps
unchanged, and [lem-pe-internal-section-tensor-comparison] identifies relative tensor, flatness
and K-flatness. Thus finite scalar presentations, cohomology, Tor bounds and the specified derived
scalar extensions have exactly their ringed-site meanings. At the end this equivalence transports
the argument back to module objects. It preserves ambient coproducts by their universal property;
all categories and coproducts use [def-weil-size-convention].
2. For every scheme $T$, $A_T\to F_T$ is a flat localization by
[det-prop-sfb-qlbar-colimit-x-invert-ell]. For the finite-subextension-valued algebraic closure,
$F_T\to\Lambda_T$ is flat by [lem-sfb-qlbar-flat]. Their composite is flat: its tensor functor is
the composite of the two exact scalar-extension functors, by $(b\otimes f)\otimes m\mapsto
b\otimes fm$ and its inverse $b\otimes m\mapsto(b\otimes1)\otimes m$. These maps follow directly
from the balancing relations. Consequently $T_{F,T}$ is exact termwise scalar extension,
triangulated by [lem-sf-exact-functor-derived-triangulated], and its cohomology is the scalar
extension of the original cohomology by [lem-weil-pbc-exact-functor-complex-cohomology]. Only the
finite-valued algebraic-closure coefficient is used here.
3. Let $J\in D_{\mathrm{ctf}}(V,A)$. Each local scalar model of each $H^q(J)$ has the two-term
finite-free scalar resolution of [lem-sfb-finite-constant-model-two-term-free-resolution]. After
step 2 its scalar matrix is over the field $\Lambda(*)$; its cokernel is a finite-dimensional
vector space, so its realized cokernel is finite free. Hence $H^q(T_{F,V}J)$ has finite constant
models on the same finite constructible stratification. Boundedness follows from the cohomology
identification in step 2. For a Tor interval $[a,b]$ of $J$, [lem-pe-coefficient-tor-flat-model]
supplies a flat complex supported in $[a,b]$. Base change carries flat modules to flat modules:
tensoring the base-changed module with an arbitrary target-module sheaf equals tensoring the
original module with that sheaf after scalar restriction, by the same balancing relations. The
base-changed flat complex therefore has the same support and represents $T_{F,V}J$ by
[lem-pur-derived-change-of-rings]. Apply the Tor/flat-model criterion again. This proves $\mathcal
G_V\subset D_{\mathrm{ctf}}(V,\Lambda)$.
4. Fix a constructible $\Lambda_V$-module $M$. Apply
[lem-fix-constructible-open-closed-refinement] to a finite constructible locally closed
stratification witnessing its constructibility. This gives a finite binary tree with qcqs
vertices, each cut by a quasi-compact open and its closed complement, and genuine scheme morphisms
from leaves to original strata. Along each branch use the exact inverse-image composition of
[det-pe-topos-functoriality-inverse-image] and the coefficient isomorphism [lem-sfb-alpha-iso].
Pull back the trivializing covers and scalar presentations. On a leaf the pulled scalar module is
finite-dimensional over $\Lambda(*)$, hence its realization is finite free. Thus each leaf
restriction of $M$ is lisse. The use of actual factoring morphisms avoids inferring factorization
merely from containment of underlying sets.
5. On a qcqs leaf $T$, the lisse module is already over $E_T$ when $\Lambda=E$. When
$\Lambda=\Omega^{\mathrm{fin}}$, apply clause (1) of [det-lem-coefficient-finite-descent-lisse] on
this qcqs $T$, obtaining a finite subextension $F$ and lisse $F_T$-module $L$ whose extension is
$M|_T$. This result applies to lisse objects, not to the full complex or its arrows. Split $T$
into its finitely many clopen constant-rank pieces using [det-lem-stratified-lattice-rank] for
$L$. All pieces remain qcqs, and rank zero is permitted.
6. For a constant-rank lisse $F_T$-module $L$ on qcqs $T$, [det-lem-stratified-lattice-scheme]
gives a separated etale surjection $q:\mathrm{Lat}(L)\to T$ and a universal lisse integral lattice
in $q^*L$. Images of affine opens of $\mathrm{Lat}(L)$ are open by
[lem-weil-pbc-etale-morphism-open-map]. Quasi-compactness [def-weil-pbc-quasi-compact-scheme]
selects finitely many whose images cover $T$. Their disjoint union $P$ is qcqs, and $p:P\to T$ is
separated, etale and surjective. Restrict the universal lattice to $P$. Apply
[lem-weil-pbc-etale-stratified-finite] (Stacks Tag 03S0) to $p$. It supplies a finite
constructible locally closed partition of $T$ such that every $p_S:P\times_T S\to S$ is finite
etale and surjective. This use of 03S0 requires only qcqs, not Noetherianity.
7. Fix one such $S$, with lattice $N\subset p_S^*L$. Split $p_S$ on an etale covering using
[lem-weil-pbc-finite-etale-etale-local-split]. On a splitting with sheets indexed by a finite set
$I$, define $p_{S*}p_S^*L\to L$ by $(s_i)\mapsto\sum_i s_i$. Two splittings differ locally by a
permutation of the sheets, which leaves this sum unchanged; hence these local maps glue by the
sheaf condition. Define $L_0$ as the image of $p_{S*}N\to L$. Over a splitting it is the sum of
the sheet lattices. The set $I$ is nonempty since $p_S$ is surjective. This constructs the trace
and its image without dividing by the degree.
8. Trivialize $L$ further pro-etale locally. Clause (1) of [det-lem-stratified-lattice-scheme]
identifies a lattice in this trivialization with a section of the constant sheaf on
$\mathrm{GL}_r(F)/\mathrm{GL}_r(\mathcal O_F)$. Thus on a further common covering the finitely
many sheet lattices are fixed scalar lattices $B_i\subset F^r$. Apply
[lem-sfb-continuous-lattice-sum]: their sheaf sum is the sheaf of continuous functions into
$\sum_iB_i$, is finite free over the integral coefficients, and its actual inclusion spans the
rational coefficient module. The comparison [lem-weil-pbc-continuous-coefficient-realizations]
identifies this calculation with the pulled-back condensed coefficients, including the inclusion.
Therefore $L_0$ is lisse over $\mathcal O_{F,S}$ and $F_S\otimes L_0\cong L|_S$. This is a direct
local sum calculation, with no Noetherian hypothesis on $S$.
9. Apply [lem-fix-constructible-open-closed-refinement] on each qcqs $T$ from step 5 to the finite
partition just obtained. Its leaves have actual maps to the lattice-bearing strata. Pull back
$L_0$ and its spanning isomorphism, using [lem-sfb-alpha-iso] and
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. A locally free integral module remains
locally free under this pullback, because the pulled trivializing cover and basis remain a cover
and a basis. Coefficient extension also pulls back by the cited tensor comparison. Attach these
finite trees to the original tree of step 4. We obtain one finite qcqs open/closed tree over $V$;
on every nonempty terminal leaf $W$ there are a finite coefficient field $F$ (equal to $E$ in the
finite-field case), an integral lisse module $B_W$, and an isomorphism $\Lambda_W\otimes_{\mathcal
O_{F,W}} B_W\cong M|_W$.
10. For an edge of this tree, extension from an open child means $j_!$, and extension from a
closed child means $i_*$. These are exact, restrict to the identity on the child, and vanish on
the other child by [lem-weil-pbc-proetale-ringed-open-closed]. If a child module has finite
constant models on a finite constructible partition, its extension has the same models on those
strata and the zero model on the complementary child. All these subsets are constructible in the
parent: a quasi-compact open is constructible, its complement is constructible, and relative
constructible subsets compose in such a constructible locally closed subset
[def-weil-constructible-subset]. Thus the extensions preserve the finite scalar-model
constructibility used here. A locally free module has Tor amplitude $[0,0]$ by its local free
tensor calculation; [lem-sfb-tor-interval-local-detection] tests this on the trivializing cover
and then on complementary children. Consequently either edge extension of a flat module is flat,
and iteration preserves Tor amplitude $[0,0]$.
11. These edge extensions commute with the exact coefficient extension of step 2. For $j_!$ take
the map $j_!(\Lambda_U\otimes B)\to\Lambda_T\otimes j_!B$ adjoint to its identity restriction on
$U$. For $i_*$ take $\Lambda_T\otimes i_*B\to i_*(\Lambda_Z\otimes B)$ adjoint to its identity
restriction on $Z$. The restriction comparisons are
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], with coefficient identifications
[lem-sfb-alpha-iso]. Each map restricts to an isomorphism on its own child and to $0\to0$ on the
other by [lem-weil-pbc-proetale-ringed-open-closed]. The kernel and cokernel have both
restrictions zero; [lem-exc-open-closed-detection] makes them zero. This proves both comparison
isomorphisms, and iteration proves the comparison along any branch.
12. For a terminal leaf $W$, extend its $B_W$ to $V$ along its branch, using the edge operations
of step 10, and denote the resulting integral sheaf by $J_W$. Step 10 gives bounded
constructibility and Tor amplitude $[0,0]$, so $J_W[0]\in D_{\mathrm{ctf}}(V,\mathcal O_F)$. Step
11 and the leaf isomorphism of step 9 identify $T_{F,V}(J_W[0])$ with the branch extension of
$(M|_W)[0]$. It therefore lies in $\mathcal G_V$. The empty leaf contributes zero, for which the
zero integral module is a model.
13. At each internal vertex $T$, the localization sequence of
[lem-weil-pbc-proetale-ringed-open-closed] applied to $M|_T$ is $0\to j_!(M|_U)\to M|_T\to
i_*(M|_Z)\to0$. Extend it to $V$ by the exact edge functors along the branch. By
[lem-sf-derived-ses-triangle] this is a distinguished triangle. Induct upward through the finite
tree: its terminal branch extensions are in $\mathcal G_V$ by step 12, and its middle vertex is an
extension of the two child vertices. Thus $M[0]$ is obtained from finitely many objects of
$\mathcal G_V$ by finitely many triangle extensions. This is a finite-tree induction, with the
terminal case already proved; it does not assume that an original stratum is open in the union of
the remaining strata.
14. For $K\in D_{\mathrm{ctf}}(V,\Lambda)$ choose $a\le b$ containing its cohomology. Every
$H^q(K)[0]$ is constructible, so step 13 gives its finite construction from $\mathcal G_V$. Apply
the truncation triangles of [lem-weil-pbc-truncation-triangle]: $\tau_{\le a-1}K=0$, and for
$q=a,\ldots,b$ the triangle has vertices $\tau_{\le q-1}K$, $\tau_{\le q}K$, and $H^q(K)[-q]$.
Induction gives $\tau_{\le b}K\simeq K$ in the finite shift-and-extension closure of $\mathcal
G_V$, hence in its ambient localizing hull. No connecting map is descended to $F$; all triangles
and their arbitrary $\Lambda_V$-linear maps stay in the ambient category. Together with step 3
this proves both clauses. The zero complex, empty $V$ and rank-zero leaves are included.
-/
theorem qcqs_rational_integral_localizing_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    (∀ K, rationalIntegralGenerators ℓ E V K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) V K ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K) ∧
    (∀ K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj E) V,
      CategoryTheory.localizingClosure (rationalIntegralGenerators ℓ E V) K.obj ∧
        ∃ n : ℕ,
          ((rationalIntegralGenerators ℓ E V).shiftClosure ℤ).extensionProductIter n K.obj) := by
  constructor
  · rintro K ⟨J, ⟨e⟩⟩
    obtain ⟨a, b, hab⟩ := J.property.2
    have h := (CondensedRing.qcqs_integral_scalar_extension_ctf ℓ E V).1
    obtain ⟨_, _, _, _, _, hctf, _⟩ := h
    exact generator_ctf_iso _ V e (hctf J a b hab).1
  · intro K
    have hfinite : ∃ n, ((rationalIntegralGenerators ℓ E V).shiftClosure ℤ).extensionProductIter
         n K.obj := by
      apply generator_bounded _ V _ ?_ K.obj K.property.1
      intro M hM
      obtain ⟨t, ⟨d⟩⟩ := (qcqs_constructible_integral_leaf_models ℓ E V).1 M hM
      apply generator_sheaf ℓ (fun _ : Unit ↦ E) _
        (fun _ ↦ padicIntegersRingObjToContinuousMapRingObj ℓ E) V _
        (fun _ J K h ↦ ⟨J, h⟩)
        ((LatticeTree.qcqs_lattice_tree_reconstruction ℓ).1 E) ?_ M t d
      intro W _ _ _
      exact (CondensedRing.qcqs_integral_scalar_extension_ctf ℓ E W).1.choose
    exact ⟨generator_finite_to_localizing _ hfinite, hfinite⟩

/-- Integral scalar extensions are constructible of finite Tor amplitude, and every
bounded constructible finite-Tor complex is in their ambient localizing hull. In fact it
is a finite iterated extension of shifts of those generators. All triangle maps are
arbitrary ambient linear maps; no finite-field descent of maps or complexes is claimed.

Source: blueprint refinement (2), coefficient devissage
(blueprint: lem-sfb-qcqs-rational-integral-localizing-generators).

Proof plan (the complete DAG proof, with the finite-field case omitting closure descent):
1. Work with the section-ring sheaves of the pulled-back ring objects. The equivalence
[lem-sfb-module-object-ringed-site-derived-comparison] leaves underlying sheaves and maps
unchanged, and [lem-pe-internal-section-tensor-comparison] identifies relative tensor, flatness
and K-flatness. Thus finite scalar presentations, cohomology, Tor bounds and the specified derived
scalar extensions have exactly their ringed-site meanings. At the end this equivalence transports
the argument back to module objects. It preserves ambient coproducts by their universal property;
all categories and coproducts use [def-weil-size-convention].
2. For every scheme $T$, $A_T\to F_T$ is a flat localization by
[det-prop-sfb-qlbar-colimit-x-invert-ell]. For the finite-subextension-valued algebraic closure,
$F_T\to\Lambda_T$ is flat by [lem-sfb-qlbar-flat]. Their composite is flat: its tensor functor is
the composite of the two exact scalar-extension functors, by $(b\otimes f)\otimes m\mapsto
b\otimes fm$ and its inverse $b\otimes m\mapsto(b\otimes1)\otimes m$. These maps follow directly
from the balancing relations. Consequently $T_{F,T}$ is exact termwise scalar extension,
triangulated by [lem-sf-exact-functor-derived-triangulated], and its cohomology is the scalar
extension of the original cohomology by [lem-weil-pbc-exact-functor-complex-cohomology]. Only the
finite-valued algebraic-closure coefficient is used here.
3. Let $J\in D_{\mathrm{ctf}}(V,A)$. Each local scalar model of each $H^q(J)$ has the two-term
finite-free scalar resolution of [lem-sfb-finite-constant-model-two-term-free-resolution]. After
step 2 its scalar matrix is over the field $\Lambda(*)$; its cokernel is a finite-dimensional
vector space, so its realized cokernel is finite free. Hence $H^q(T_{F,V}J)$ has finite constant
models on the same finite constructible stratification. Boundedness follows from the cohomology
identification in step 2. For a Tor interval $[a,b]$ of $J$, [lem-pe-coefficient-tor-flat-model]
supplies a flat complex supported in $[a,b]$. Base change carries flat modules to flat modules:
tensoring the base-changed module with an arbitrary target-module sheaf equals tensoring the
original module with that sheaf after scalar restriction, by the same balancing relations. The
base-changed flat complex therefore has the same support and represents $T_{F,V}J$ by
[lem-pur-derived-change-of-rings]. Apply the Tor/flat-model criterion again. This proves $\mathcal
G_V\subset D_{\mathrm{ctf}}(V,\Lambda)$.
4. Fix a constructible $\Lambda_V$-module $M$. Apply
[lem-fix-constructible-open-closed-refinement] to a finite constructible locally closed
stratification witnessing its constructibility. This gives a finite binary tree with qcqs
vertices, each cut by a quasi-compact open and its closed complement, and genuine scheme morphisms
from leaves to original strata. Along each branch use the exact inverse-image composition of
[det-pe-topos-functoriality-inverse-image] and the coefficient isomorphism [lem-sfb-alpha-iso].
Pull back the trivializing covers and scalar presentations. On a leaf the pulled scalar module is
finite-dimensional over $\Lambda(*)$, hence its realization is finite free. Thus each leaf
restriction of $M$ is lisse. The use of actual factoring morphisms avoids inferring factorization
merely from containment of underlying sets.
5. On a qcqs leaf $T$, the lisse module is already over $E_T$ when $\Lambda=E$. When
$\Lambda=\Omega^{\mathrm{fin}}$, apply clause (1) of [det-lem-coefficient-finite-descent-lisse] on
this qcqs $T$, obtaining a finite subextension $F$ and lisse $F_T$-module $L$ whose extension is
$M|_T$. This result applies to lisse objects, not to the full complex or its arrows. Split $T$
into its finitely many clopen constant-rank pieces using [det-lem-stratified-lattice-rank] for
$L$. All pieces remain qcqs, and rank zero is permitted.
6. For a constant-rank lisse $F_T$-module $L$ on qcqs $T$, [det-lem-stratified-lattice-scheme]
gives a separated etale surjection $q:\mathrm{Lat}(L)\to T$ and a universal lisse integral lattice
in $q^*L$. Images of affine opens of $\mathrm{Lat}(L)$ are open by
[lem-weil-pbc-etale-morphism-open-map]. Quasi-compactness [def-weil-pbc-quasi-compact-scheme]
selects finitely many whose images cover $T$. Their disjoint union $P$ is qcqs, and $p:P\to T$ is
separated, etale and surjective. Restrict the universal lattice to $P$. Apply
[lem-weil-pbc-etale-stratified-finite] (Stacks Tag 03S0) to $p$. It supplies a finite
constructible locally closed partition of $T$ such that every $p_S:P\times_T S\to S$ is finite
etale and surjective. This use of 03S0 requires only qcqs, not Noetherianity.
7. Fix one such $S$, with lattice $N\subset p_S^*L$. Split $p_S$ on an etale covering using
[lem-weil-pbc-finite-etale-etale-local-split]. On a splitting with sheets indexed by a finite set
$I$, define $p_{S*}p_S^*L\to L$ by $(s_i)\mapsto\sum_i s_i$. Two splittings differ locally by a
permutation of the sheets, which leaves this sum unchanged; hence these local maps glue by the
sheaf condition. Define $L_0$ as the image of $p_{S*}N\to L$. Over a splitting it is the sum of
the sheet lattices. The set $I$ is nonempty since $p_S$ is surjective. This constructs the trace
and its image without dividing by the degree.
8. Trivialize $L$ further pro-etale locally. Clause (1) of [det-lem-stratified-lattice-scheme]
identifies a lattice in this trivialization with a section of the constant sheaf on
$\mathrm{GL}_r(F)/\mathrm{GL}_r(\mathcal O_F)$. Thus on a further common covering the finitely
many sheet lattices are fixed scalar lattices $B_i\subset F^r$. Apply
[lem-sfb-continuous-lattice-sum]: their sheaf sum is the sheaf of continuous functions into
$\sum_iB_i$, is finite free over the integral coefficients, and its actual inclusion spans the
rational coefficient module. The comparison [lem-weil-pbc-continuous-coefficient-realizations]
identifies this calculation with the pulled-back condensed coefficients, including the inclusion.
Therefore $L_0$ is lisse over $\mathcal O_{F,S}$ and $F_S\otimes L_0\cong L|_S$. This is a direct
local sum calculation, with no Noetherian hypothesis on $S$.
9. Apply [lem-fix-constructible-open-closed-refinement] on each qcqs $T$ from step 5 to the finite
partition just obtained. Its leaves have actual maps to the lattice-bearing strata. Pull back
$L_0$ and its spanning isomorphism, using [lem-sfb-alpha-iso] and
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. A locally free integral module remains
locally free under this pullback, because the pulled trivializing cover and basis remain a cover
and a basis. Coefficient extension also pulls back by the cited tensor comparison. Attach these
finite trees to the original tree of step 4. We obtain one finite qcqs open/closed tree over $V$;
on every nonempty terminal leaf $W$ there are a finite coefficient field $F$ (equal to $E$ in the
finite-field case), an integral lisse module $B_W$, and an isomorphism $\Lambda_W\otimes_{\mathcal
O_{F,W}} B_W\cong M|_W$.
10. For an edge of this tree, extension from an open child means $j_!$, and extension from a
closed child means $i_*$. These are exact, restrict to the identity on the child, and vanish on
the other child by [lem-weil-pbc-proetale-ringed-open-closed]. If a child module has finite
constant models on a finite constructible partition, its extension has the same models on those
strata and the zero model on the complementary child. All these subsets are constructible in the
parent: a quasi-compact open is constructible, its complement is constructible, and relative
constructible subsets compose in such a constructible locally closed subset
[def-weil-constructible-subset]. Thus the extensions preserve the finite scalar-model
constructibility used here. A locally free module has Tor amplitude $[0,0]$ by its local free
tensor calculation; [lem-sfb-tor-interval-local-detection] tests this on the trivializing cover
and then on complementary children. Consequently either edge extension of a flat module is flat,
and iteration preserves Tor amplitude $[0,0]$.
11. These edge extensions commute with the exact coefficient extension of step 2. For $j_!$ take
the map $j_!(\Lambda_U\otimes B)\to\Lambda_T\otimes j_!B$ adjoint to its identity restriction on
$U$. For $i_*$ take $\Lambda_T\otimes i_*B\to i_*(\Lambda_Z\otimes B)$ adjoint to its identity
restriction on $Z$. The restriction comparisons are
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], with coefficient identifications
[lem-sfb-alpha-iso]. Each map restricts to an isomorphism on its own child and to $0\to0$ on the
other by [lem-weil-pbc-proetale-ringed-open-closed]. The kernel and cokernel have both
restrictions zero; [lem-exc-open-closed-detection] makes them zero. This proves both comparison
isomorphisms, and iteration proves the comparison along any branch.
12. For a terminal leaf $W$, extend its $B_W$ to $V$ along its branch, using the edge operations
of step 10, and denote the resulting integral sheaf by $J_W$. Step 10 gives bounded
constructibility and Tor amplitude $[0,0]$, so $J_W[0]\in D_{\mathrm{ctf}}(V,\mathcal O_F)$. Step
11 and the leaf isomorphism of step 9 identify $T_{F,V}(J_W[0])$ with the branch extension of
$(M|_W)[0]$. It therefore lies in $\mathcal G_V$. The empty leaf contributes zero, for which the
zero integral module is a model.
13. At each internal vertex $T$, the localization sequence of
[lem-weil-pbc-proetale-ringed-open-closed] applied to $M|_T$ is $0\to j_!(M|_U)\to M|_T\to
i_*(M|_Z)\to0$. Extend it to $V$ by the exact edge functors along the branch. By
[lem-sf-derived-ses-triangle] this is a distinguished triangle. Induct upward through the finite
tree: its terminal branch extensions are in $\mathcal G_V$ by step 12, and its middle vertex is an
extension of the two child vertices. Thus $M[0]$ is obtained from finitely many objects of
$\mathcal G_V$ by finitely many triangle extensions. This is a finite-tree induction, with the
terminal case already proved; it does not assume that an original stratum is open in the union of
the remaining strata.
14. For $K\in D_{\mathrm{ctf}}(V,\Lambda)$ choose $a\le b$ containing its cohomology. Every
$H^q(K)[0]$ is constructible, so step 13 gives its finite construction from $\mathcal G_V$. Apply
the truncation triangles of [lem-weil-pbc-truncation-triangle]: $\tau_{\le a-1}K=0$, and for
$q=a,\ldots,b$ the triangle has vertices $\tau_{\le q-1}K$, $\tau_{\le q}K$, and $H^q(K)[-q]$.
Induction gives $\tau_{\le b}K\simeq K$ in the finite shift-and-extension closure of $\mathcal
G_V$, hence in its ambient localizing hull. No connecting map is descended to $F$; all triangles
and their arbitrary $\Lambda_V$-linear maps stay in the ambient category. Together with step 3
this proves both clauses. The zero complex, empty $V$ and rank-zero leaves are included.
-/
theorem qcqs_algCl_integral_localizing_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] :
    (∀ K, algClIntegralGenerators ℓ V K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) V K ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K) ∧
    (∀ K : ConstantModelConstructibleFiniteTor (Profinite.padicAlgClRingObj ℓ) V,
      CategoryTheory.localizingClosure (algClIntegralGenerators ℓ V) K.obj ∧
        ∃ n : ℕ, ((algClIntegralGenerators ℓ V).shiftClosure ℤ).extensionProductIter n K.obj) := by
  constructor
  · rintro K ⟨F, J, ⟨e⟩⟩
    obtain ⟨a, b, hab⟩ := J.property.2
    have h := (CondensedRing.qcqs_integral_scalar_extension_ctf ℓ F V).2
    obtain ⟨hflat, _, _, _, _, hctf, _⟩ := h
    have hφ : coefficientMap (CondensedRing.integralScalarMap ℓ F ≫
        Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) V =
        padicIntegersToPadicSubfield V ℓ F ≫ padicSubfieldRingObjToPadicAlgCl V ℓ F :=
      coefficientMap_comp _ _ V
    obtain ⟨ed⟩ := generator_derived_coeff_iso _ _ V _ _ hφ J.obj
    exact generator_ctf_iso _ V (ed ≪≫ e) (hctf J a b hab).1
  · intro K
    have hfinite : ∃ n, ((algClIntegralGenerators ℓ V).shiftClosure ℤ).extensionProductIter
         n K.obj := by
      apply generator_bounded _ V _ ?_ K.obj K.property.1
      intro M hM
      let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
      obtain ⟨t, ⟨d⟩⟩ := (qcqs_constructible_integral_leaf_models ℓ E V).2 M hM
      apply generator_sheaf ℓ (fun F : PadicAlgCl.FiniteIntermediateField ℓ ↦ F) _
        (fun F ↦ padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
          Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) V _ ?_
        (LatticeTree.qcqs_lattice_tree_reconstruction ℓ).2 ?_ M t d
      · intro F J K h
        obtain ⟨e⟩ := h
        have hφ : coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ F ≫
            Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) V =
            padicIntegersToPadicSubfield V ℓ F ≫ padicSubfieldRingObjToPadicAlgCl V ℓ F :=
          coefficientMap_comp _ _ V
        obtain ⟨ed⟩ := generator_derived_coeff_iso _ _ V _ _ hφ J.obj
        exact ⟨F, J, ⟨ed.symm ≪≫ e⟩⟩
      · intro W _ _ F
        exact (CondensedRing.qcqs_integral_scalar_extension_ctf ℓ F W).2.choose
    exact ⟨generator_finite_to_localizing _ hfinite, hfinite⟩

end AlgebraicGeometry.ProEtale
