/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.Topology.Stratification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Constructible
import Sheaf.Algebra.Homology.DerivedTensor
import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.Paper.ComparisonPullbackExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.OpenClosed.Complex
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Flat.EquationalCriterion
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.Algebra.Module.Projective
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.ConstructibleSheaf.Monoidal
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.SurjectiveClosedModuleInvariance
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
import Sheaf.SixFunctors.OpenClosedFlatness
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Ordered strata, sheaf filtrations, and thick generation over finite rings

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-sf-flat-model/det-sf-flat-model-generation.md
(blueprint: det-sf-flat-model-generation).

The six statements give the three clauses separately on the etale and pro-etale sites.
`Dctf` is expanded using constructible cohomology, finite cohomological bounds, and the
recorded Tor-amplitude predicates. In particular no etale-origin condition is imposed.
The auxiliary definitions spell out parts of this node: ordered tails, finite projective
lisse restrictions, the canonical locally closed extension, and a finite sheaf filtration.
All their data are explicit. The pro-etale site retains object universe u+1 and Hom universe u.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Closed tails and relative openness for an ordered finite stratification.
Source: blueprint det-sf-flat-model-generation, clause (1)
(blueprint: det-sf-flat-model-generation). -/
def FlatModelOrderedStratification {X : Scheme.{u}} (str : LocallyClosedStratification X) :
    Prop :=
  ∀ k : Fin str.n,
    IsClosed (⋃ k' : Fin str.n, if k ≤ k' then str.stratum k' else ∅) ∧
    IsOpen {x : (⋃ k' : Fin str.n, if k ≤ k' then str.stratum k' else ∅) |
      (x : X) ∈ str.stratum k}

/-- A finite extension filtration has zero first term, final term isomorphic to F,
and exactly one specified quotient per stratum, in the prescribed order.
Source: blueprint det-sf-flat-model-generation, clause (2)
(blueprint: det-sf-flat-model-generation). -/
def FlatModelExtensionFiltration {C : Type v} [Category.{w} C] [Abelian C]
    {m : ℕ} (G : Fin m → C) (F : C) : Prop :=
  ∃ M : Fin (m + 1) → C,
    IsZero (M 0) ∧ Nonempty (M (Fin.last m) ≅ F) ∧
    ∀ k : Fin m,
      ∃ (f : M k.castSucc ⟶ M k.succ) (g : M k.succ ⟶ G k)
        (h : f ≫ g = 0), (ShortComplex.mk f g h).ShortExact

/-- Local constancy and finite projective geometric stalks on the small etale site.
Source: blueprint det-sf-flat-model-generation, clauses (1) and (3)
(blueprint: det-sf-flat-model-generation). -/
def FlatModelEtaleLisseProjective {S : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) : Prop :=
  IsLocallyConstantSheaf L ∧
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S),
      Finite ((((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj L) : Type (u + 1)) ∧
      Module.Projective A (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj L)

/-- Local constancy and finite projective geometric stalks over the constant coefficient
ring on the small pro-etale site. The recorded stalk functor restricts scalars along the
actual constant-ring germ; projectivity is imposed over ULift A itself. Local constancy
uses module-sheaf isomorphisms, and does not assume etale origin.
Source: blueprint det-sf-flat-model-generation, clauses (1) and (3)
(blueprint: det-sf-flat-model-generation). -/
def FlatModelProEtaleLisseProjective (S : Scheme.{u}) (A : Type u) [CommRing A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf S A L ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
      Finite ((finiteCoefficientModuleStalkFunctor x A).obj L) ∧
      Module.Projective (ULift.{u + 1, u} A) ((finiteCoefficientModuleStalkFunctor x A).obj L)

/-- The ordinary locally closed extension a_! = g_* j_!, with j = a.toImage and
closed g = a.imageι. Its quasi-compactness follows from the embedding into Noetherian X.
Source: blueprint det-sf-flat-model-generation, conventions and clause (2)
(blueprint: det-sf-flat-model-generation). -/
def flatModelEtaleExtension {S X : Scheme.{u}} [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] (a : S ⟶ X) (ha : IsImmersion a) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) a.toImage ⋙
    Etale.lowerStar (ModuleCat.{u + 1} A) a.imageι

/-- The same canonical locally closed extension in intrinsic pro-etale modules.
The published realization equivalences extend fixed scalar actions to locally constant
scalar sections; they preserve the actual extension-by-zero and direct-image functors.
Source: blueprint det-sf-flat-model-generation, conventions and clause (2)
(blueprint: det-sf-flat-model-generation). -/
def flatModelProEtaleExtension {S X : Scheme.{u}} [IsNoetherian X]
    (A : Type u) [CommRing A] [Finite A] (a : S ⟶ X) (ha : IsImmersion a) :
    proEtaleRingModules S (proEtaleConstantRing S A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) := by
  letI : IsImmersion a := ha
  letI : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact (sfIntrinsicModuleEquivalence S A).inverse ⋙
    ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a.toImage ⋙
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a.imageι ⋙
    (sfIntrinsicModuleEquivalence X A).functor

/-- Clause (1) on the etale site: an ordered finite stratification with projective stalks.
Source: blueprint det-sf-flat-model-generation
(blueprint: det-sf-flat-model-generation).

Proof:
By the two constructibility definitions choose a finite locally closed partition adapted to F.
Refine it, rather than merely reorder its old strata, as follows. For each old stratum T include
the two closed sets \overline T and \overline T\setminus T, and let \mathcal Z consist of X, the
empty set and all intersections of this finite family. Set S_Z=Z\setminus\bigcup_{Z'\in\mathcal
Z,\ Z'\subsetneq Z}Z'. Each point belongs to the cell of the smallest member of \mathcal Z
containing it, so these cells partition X; their membership in every old \overline T and its
boundary shows that each cell lies in one old T. Order the nonempty cells by any linear order
extending reverse inclusion of their Z. Among the Z with nonempty cells, the unprocessed ones
form a downward closed family. If x lies in such a Z, the smallest member Z_x containing x is a
subset of Z and has the nonempty cell containing x, so its cell is also unprocessed. Thus the
union of the unprocessed cells equals the finite union of their Z, hence is closed; this also
handles Z whose own cell was empty. Thus every tail is closed and its first cell is open in it.
Give each cell the open subscheme structure inside the reduced induced closed subscheme on Z,
supplied by [lem-weil-pbc-reduced-induced-closed-subscheme]. It maps to its old stratum T:
locally where T is closed, its defining ideal is contained in the radical ideal of the reduced
cell, since every cell point belongs to T. The affine quotient description therefore factors the
cell immersion through T, and these local factorizations agree because immersions are
monomorphisms. Pulling the old trivializing covers and constant models back along these actual
maps gives finite locally constant restrictions. Each cell is constructible because it is a
difference of closed sets in the Noetherian space, by [def-weil-constructible-subset]. This
writes out the finite closed-set refinement argument. If X is empty use the empty partition.

For either site the geometric-stalk adjunction is a morphism of topoi by
[lem-fix-geometric-stalk-topos-point]. Apply the ringed-topos flat-pullback theorem to this
point with coefficient ring its stalk A: a flat F has flat geometric stalks. No conservativity
of pro-etale geometric points is used. Every finite local module model on a nonempty
trivializing object is isomorphic to such a stalk. If M is one of these finite A-modules, choose
a finite set of generators and a surjection A^n\to M. Its kernel is a finite set because A^n is
finite, hence is generated by finitely many of its elements. This supplies a finite presentation
A^r\to A^n\to M\to0. The existing finitely-presented-flat-module theorem makes M finite
projective. The same applies directly to every finite geometric stalk. This proves clause (1). -/
theorem etale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F) (_hf : ObjectProperty.flat F) :
    ∃ str : LocallyClosedStratification X,
      FlatModelOrderedStratification str ∧
      ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
        ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F) := by
  sorry

/-- Clause (1) on the pro-etale site, with intrinsic constructibility.
Source: blueprint det-sf-flat-model-generation
(blueprint: det-sf-flat-model-generation).

Proof:
By the two constructibility definitions choose a finite locally closed partition adapted to F.
Refine it, rather than merely reorder its old strata, as follows. For each old stratum T include
the two closed sets \overline T and \overline T\setminus T, and let \mathcal Z consist of X, the
empty set and all intersections of this finite family. Set S_Z=Z\setminus\bigcup_{Z'\in\mathcal
Z,\ Z'\subsetneq Z}Z'. Each point belongs to the cell of the smallest member of \mathcal Z
containing it, so these cells partition X; their membership in every old \overline T and its
boundary shows that each cell lies in one old T. Order the nonempty cells by any linear order
extending reverse inclusion of their Z. Among the Z with nonempty cells, the unprocessed ones
form a downward closed family. If x lies in such a Z, the smallest member Z_x containing x is a
subset of Z and has the nonempty cell containing x, so its cell is also unprocessed. Thus the
union of the unprocessed cells equals the finite union of their Z, hence is closed; this also
handles Z whose own cell was empty. Thus every tail is closed and its first cell is open in it.
Give each cell the open subscheme structure inside the reduced induced closed subscheme on Z,
supplied by [lem-weil-pbc-reduced-induced-closed-subscheme]. It maps to its old stratum T:
locally where T is closed, its defining ideal is contained in the radical ideal of the reduced
cell, since every cell point belongs to T. The affine quotient description therefore factors the
cell immersion through T, and these local factorizations agree because immersions are
monomorphisms. Pulling the old trivializing covers and constant models back along these actual
maps gives finite locally constant restrictions. Each cell is constructible because it is a
difference of closed sets in the Noetherian space, by [def-weil-constructible-subset]. This
writes out the finite closed-set refinement argument. If X is empty use the empty partition.

For either site the geometric-stalk adjunction is a morphism of topoi by
[lem-fix-geometric-stalk-topos-point]. Apply the ringed-topos flat-pullback theorem to this
point with coefficient ring its stalk A: a flat F has flat geometric stalks. No conservativity
of pro-etale geometric points is used. Every finite local module model on a nonempty
trivializing object is isomorphic to such a stalk. If M is one of these finite A-modules, choose
a finite set of generators and a surjection A^n\to M. Its kernel is a finite set because A^n is
finite, hence is generated by finitely many of its elements. This supplies a finite presentation
A^r\to A^n\to M\to0. The existing finitely-presented-flat-module theorem makes M finite
projective. The same applies directly to every finite geometric stalk. This proves clause (1). -/
theorem proEtale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F)
    (_hf : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F) :
    ∃ str : LocallyClosedStratification X,
      FlatModelOrderedStratification str ∧
      ∀ k : Fin str.n, FlatModelProEtaleLisseProjective (str.domain k) A
        (proEtaleConstantModulePullback (str.immersion k) A F) := by
  sorry

/-- Clause (2) on the etale site: the specified finite sheaf-extension filtration
and flat constructible degree-zero factors of finite Tor amplitude.
Source: blueprint det-sf-flat-model-generation
(blueprint: det-sf-flat-model-generation).

Proof:
The Noetherian hypothesis implies that the underlying space has the descending chain condition
on closed subsets. Thus every open subset is quasi-compact: a cover with no finite subcover
would give a strictly increasing chain of finite unions of its members, hence a strictly
decreasing chain of their closed complements. The same argument on every affine open makes every
open immersion below quasi-compact. For a closed immersion into X, its inverse image over an
affine chart Spec(B) is Spec(B/I) by the affine-quotient clause of the closed-immersion
definition. An ideal of B/I is the image of its inverse-image ideal in B, so generators of the
latter give generators of the former. Hence B/I is Noetherian, and the closed subscheme is
locally Noetherian; its closed underlying subspace is quasi-compact by the same finite-subcover
argument. Apply the locally Noetherian quasi-separatedness lemma to X and to these closed
subschemes: they are all qcqs. These facts verify the quasi-compact-complement hypotheses of the
pro-etale localization results used below.

We first record the sheaf calculation needed for clause (2), on both sites. For a complementary
open/closed pair j,i, restriction is exact and commutes with ordinary tensor: on the etale site
use the exact module inverse image, and on the pro-etale site use the
identified-constant-coefficient operations; the algebraic inverse-image tensor comparison
applies to both. The etale open-closed sequence is [lem-weil-pbc-open-closed-short-exact], and
its pro-etale counterpart, exact i_*, and all four restriction identities are
[lem-weil-pbc-proetale-ringed-open-closed]. In the etale case the open unit, closed counit, and
the two vanishing lemmas give the same identities j^*j_!=1, i^*i_*=1, i^*j_!=0, j^*i_*=0; the
maps are module-linear because their underlying adjunction maps are. Exactness of i_* in this
case is explicitly part of [lem-cbc-open-closed-recollement]. On either site the open-closed
sequence shows that a sheaf with both restrictions zero is zero. For any short exact sequence,
tensor with H and form its homology objects (including the outer kernel and cokernel). If j^*H
and i^*H are flat, exactness and the tensor comparison imply that each such homology object
restricts to zero on both sides, hence is zero. Thus tensor with H preserves short exact
sequences: flatness can be tested on this open/closed pair. In particular j_! and i_* preserve
flat sheaves, using their restriction identities. This argument works for all module sheaves,
including nonclassical pro-etale test sheaves. We also need to compare scheme structures, rather
than identify a topologically open immersion with an open immersion of schemes. If h:T→Y is a
surjective closed immersion, its open complement is empty. The same sequences give an
isomorphism of the unit H→h_*h^*H, and the closed counit gives h^*h_*≅1. Thus h^* and h_* are
inverse equivalences for ordinary module sheaves, and a constant A-module sheaf pulls back to
the same constant model. Finite local constancy is reflected by h^*: on the etale site h is a
universal homeomorphism by [lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism],
so [prop-weil-pbc-universal-homeomorphism-topos] identifies the topoi, constants and covering
epimorphisms. On the pro-etale site, apply
[new-lem-weil-pbc-proetale-surjective-closed-cover-refinement] to a trivializing cover of T. It
gives a cover B of Y whose pullback B×_Y T refines that cover. On each B, the unit and counit
just proved for the surjective closed immersion B×_Y T→B identify H|_B with the constant module
model on B, since their pullbacks are isomorphic. This proves reflection with the same finite
projective models; the empty complement is quasi-compact even when B is not Noetherian.

For a locally constant L with finite projective geometric stalks, each constant model on a
nonempty trivializing object is isomorphic to a geometric stalk: choose a geometric point of
that object and apply [lem-fix-geometric-stalk-topos-point]. Thus its models are finite
projective (empty objects can be discarded). Such L is flat: on a trivializing covering, a
displayed splitting M\oplus N=A^r gives L\oplus\underline N=A_S^r, so tensoring any short exact
sequence with L is a retract of its r-fold direct sum, which is short exact. Exactness can be
checked on the covering: kernels and cokernels restrict to zero, hence vanish by the sheaf axiom
and local lifting of sections. Factor a:S\hookrightarrow X as an open
j:S\hookrightarrow\overline S followed by a closed g:\overline S\hookrightarrow X, and put
a_!=g_*j_!. Step 4 makes a_!L flat. Its restrictions are L on S and zero on \overline S\setminus
S and X\setminus\overline S, by the same restriction identities. These three pieces are locally
closed and hence constructible in the Noetherian space by [def-weil-constructible-subset], so
a_!L is constructible on either site by the constructibility definitions. Finally a_!L[0] is a
bounded-above complex of flat sheaves, hence K-flat by
[lem-weil-pbc-independent-bounded-flat-kflat]. Its derived tensor with every module sheaf N[0]
is the degree-zero ordinary tensor a_!L\otimes_A N. It therefore has Tor amplitude [0,0] and
belongs to \Dctf. This proves the assertion about all generators, not only the strata of one F.

First verify closed/open interchange on either site. In a cartesian square with closed g:Z→X,
open u:W→X, open v:Z_W→Z and closed h:Z_W→W, the restriction formula for direct image gives
u^*g_*v_!L≅h_*L, so open adjunction gives a map u_!h_*L→g_*v_!L. Pulling back by g, the
open-extension base-change statements [lem-cbc-extension-zero-base-change] and
[lem-cbc-proetale-extension-zero-base-change] identify the left side with v_!h^*h_*L≅v_!L; the
right side is v_!L by the closed counit. The induced map is v_! of that counit and is
invertible. On the open complement of Z, the right side is zero; base change for u_! identifies
the left side with extension of the restriction of h_*L to W\Z, which is zero by the open/closed
vanishing identity. The exact open-closed sequence detects isomorphisms, so the map is an
isomorphism. Every complement here is quasi-compact by step 1. This also identifies the
definition g_*j_! using scheme-theoretic closure with u_!h_* in any open W where the immersion
is closed: the closure restricted to W is that closed subscheme, since its affine defining
kernel is the same quotient ideal. Induct on the number of ordered strata, allowing the given
strata to have arbitrary locally closed subscheme structures. With no strata the open-closed
sequence for the empty closed/open pair gives F=0 and the extension tower is empty. Otherwise
let U be the actual open subscheme of X with underlying set S_1, and let i:C→X be the reduced
induced closed subscheme on its complement, using
[lem-weil-pbc-reduced-induced-closed-subscheme]. Write u:U→X for the open immersion. The
immersion S_1→X factors as a surjective closed immersion h:S_1→U followed by u: in a
closed-then-open factorization, the latter open contains U and the defining ideal restricts to
U. Step 4 gives F|_U≅h_*L_1. The open-closed sequence is therefore 0→u_!h_*L_1→F→i_*i^*F→0. Here
u_!h_*L_1≅a_{1!}L_1 by the closed/open calculation just proved. For k≥2 use D_k=S_k×_X C with
maps b_k:D_k→C and p_k:D_k→S_k. Base change preserves immersions by
[lem-weil-pbc-immersion-base-change-lft]; p_k is closed by
[lem-weil-pbc-closed-immersion-base-change] and is surjective because C has precisely the closed
underlying tail, and a closed immersion has unchanged residue fields, so the fibre over any
point of S_k in the tail is that same point ([lem-weil-pbc-fibre-product-points]). The D_k give
the remaining ordered partition of C. The sheaf i^*F is flat by flat pullback and constructible:
its restriction to D_k is p_k^*L_k, with the pulled-back local trivializations. Apply the
induction hypothesis on C, which is Noetherian by step 1. Exact i_* gives a tower with factors
i_*b_{k!}p_k^*L_k. These factors equal a_{k!}L_k as follows. Use the closed/open calculation to
compute extension along an immersion in an open neighbourhood W in which its image is closed.
The intersection D_k→X has the same locally closed underlying image as S_k. In such a W the two
immersions are closed and the map D_k→S_k is the surjective closed immersion p_k. Step 4
identifies L_k≅p_{k*}p_k^*L_k. Closed direct images compose, since their values on V are
sections on V×_W D_k. Extending the resulting isomorphism by zero from W proves
i_*b_{k!}p_k^*L_k≅a_{k!}L_k; computing the left side inside C first agrees by closed/open
interchange for C→X and W→X, followed by composition of the closed direct images. Thus the first
sequence and the pushed-forward tower prove clause (2), including nonreduced strata, without
assuming that S_1→X itself is open. -/
theorem etale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F)
    (_hf : ObjectProperty.flat F)
    (str : LocallyClosedStratification X) (_ho : FlatModelOrderedStratification str)
    (_hp : ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
      ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) :
    FlatModelExtensionFiltration
      (fun k : Fin str.n ↦
        (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) F ∧
    ∀ k : Fin str.n,
      ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        G = (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F) ∧
        ObjectProperty.flat G ∧
        IsConstructibleEtaleModuleSheaf G ∧
        (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  sorry

/-- Clause (3) on the etale site: equality with the smallest replete full
subcategory closed under shifts, cones and direct summands.
Source: blueprint det-sf-flat-model-generation
(blueprint: det-sf-flat-model-generation).

Proof:
For a locally constant L with finite projective geometric stalks, each constant model on a
nonempty trivializing object is isomorphic to a geometric stalk: choose a geometric point of
that object and apply [lem-fix-geometric-stalk-topos-point]. Thus its models are finite
projective (empty objects can be discarded). Such L is flat: on a trivializing covering, a
displayed splitting M\oplus N=A^r gives L\oplus\underline N=A_S^r, so tensoring any short exact
sequence with L is a retract of its r-fold direct sum, which is short exact. Exactness can be
checked on the covering: kernels and cokernels restrict to zero, hence vanish by the sheaf axiom
and local lifting of sections. Factor a:S\hookrightarrow X as an open
j:S\hookrightarrow\overline S followed by a closed g:\overline S\hookrightarrow X, and put
a_!=g_*j_!. Step 4 makes a_!L flat. Its restrictions are L on S and zero on \overline S\setminus
S and X\setminus\overline S, by the same restriction identities. These three pieces are locally
closed and hence constructible in the Noetherian space by [def-weil-constructible-subset], so
a_!L is constructible on either site by the constructibility definitions. Finally a_!L[0] is a
bounded-above complex of flat sheaves, hence K-flat by
[lem-weil-pbc-independent-bounded-flat-kflat]. Its derived tensor with every module sheaf N[0]
is the degree-zero ordinary tensor a_!L\otimes_A N. It therefore has Tor amplitude [0,0] and
belongs to \Dctf. This proves the assertion about all generators, not only the strata of one F.

The category \Dctf is thick. On the etale site, bounded constructible complexes are triangulated
by [prop-constructible-derived-subcategory]. They are also closed under retracts: if e is the
idempotent on each constructible cohomology sheaf induced by a retract, its image is the kernel
of 1-e and is constructible by [thm-constructible-serre]; the same finite cohomological bounds
persist. Tensoring a triangle with any N[0] is triangulated by
[lem-kun-derived-tensor-triangulated], so its cohomology long exact sequence shows that an
extension of objects with intervals [a,b] and [c,d] has interval [min(a,c),max(b,d)]. A shift by
n replaces [a,b] by [a-n,b-n], and a retract retains the interval because its tensor cohomology
is a retract of the original tensor cohomology. These arguments prove the etale assertion. For
the pro-etale site use the exact comparison and its triangulated derived functor, the
equivalence of bounded constructible categories [sk-thm-pe-constructible-comparison], and the
interval-preserving equivalence [det-pe-finite-tor-comparison-noetherian]. Here X is qcqs by
step 1 and A is Noetherian since its finite set of ideals has no infinite increasing chain. This
transfer respects ambient cones: lift the connecting morphism between the two bounded
constructible ends by full faithfulness and take its etale cone. It respects ambient retracts
too: on each cohomology sheaf lift the associated idempotent by the sheaf equivalence, take its
etale image as above, and apply exact comparison. Thus the other cone or retract stays bounded
constructible before applying the Tor comparison. All these are ordinary constant-ring module
categories.

Let C\in\Dctf(X,A), with Tor interval [a,b], a\le b. On the etale site
[lem-sf-etale-flat-constructible] gives an isomorphic complex P, zero outside [a,b], whose terms
are flat constructible. On the pro-etale site first use
[det-pe-finite-tor-comparison-noetherian] to choose C_0\in D^b_{ctf}(X_{\mathrm{et}},A) with
\nu_X^*C_0\cong C and the same interval. Apply the same etale model theorem to C_0 and pull its
model back termwise. The comparison functor is exact and commutes with cohomology, so the
pulled-back complex represents C and remains zero outside [a,b]. Its terms are constructible by
the sheaf equivalence and flat by the ringed-topos flat-pullback theorem. Hence a bounded flat
constructible model exists on either site for the general finite ring and general Noetherian X
of this item. This cites the independent model theorem, not the parent sk-lem-sf-flat-model
which uses this item.

Let \mathcal G be the full replete subcategory generated by the a_!L under the three indicated
operations. By steps 5 and 7, \mathcal G\subseteq\Dctf. For the reverse inclusion use P from
step 8. Write P_{\ge q} for its brutal tail, with P^r in degrees r\ge q and zero below.
Inclusion of the next tail and projection onto degree q give a degreewise split short exact
sequence 0\to P_{\ge q+1}\to P_{\ge q}\to P^q[-q]\to0: in degree q it is 0\to0\to
P^q\xrightarrow{1}P^q\to0, above q it is 0\to P^r\xrightarrow{1}P^r\to0\to0, and below q every
term is zero. The complex maps commute with differentials since the tail differential only
points upwards and the target single complex has zero differential. The short-exact-sequence
triangle theorem supplies a distinguished triangle with these three terms. By steps 3 and 6 each
flat constructible P^q is a finite extension of a_!L; placing its short exact sequences in
degree zero and applying the same triangle theorem gives P^q[0]\in\mathcal G, hence
P^q[-q]\in\mathcal G. Start with P_{\ge b+1}=0 (a cone of an identity of a generator) and induct
down from b to a along these triangles. This gives P_{\ge a}=P\in\mathcal G, so C\in\mathcal G.
This proves clause (3). -/
theorem etale_flatConstructible_thickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A] :
    (fun K : Etale.DerivedCategoryModule A X ↦
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b K)) =
    ObjectProperty.triangEnvelope
      (fun K : Etale.DerivedCategoryModule A X ↦
        ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
          (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
          FlatModelEtaleLisseProjective A L ∧
          Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((flatModelEtaleExtension A a ha).obj L))) := by
  sorry

/-- Clause (2) on the proEtale site: the specified finite sheaf-extension filtration
and flat constructible degree-zero factors of finite Tor amplitude.
Source: blueprint det-sf-flat-model-generation
(blueprint: det-sf-flat-model-generation).

Proof:
The Noetherian hypothesis implies that the underlying space has the descending chain condition
on closed subsets. Thus every open subset is quasi-compact: a cover with no finite subcover
would give a strictly increasing chain of finite unions of its members, hence a strictly
decreasing chain of their closed complements. The same argument on every affine open makes every
open immersion below quasi-compact. For a closed immersion into X, its inverse image over an
affine chart Spec(B) is Spec(B/I) by the affine-quotient clause of the closed-immersion
definition. An ideal of B/I is the image of its inverse-image ideal in B, so generators of the
latter give generators of the former. Hence B/I is Noetherian, and the closed subscheme is
locally Noetherian; its closed underlying subspace is quasi-compact by the same finite-subcover
argument. Apply the locally Noetherian quasi-separatedness lemma to X and to these closed
subschemes: they are all qcqs. These facts verify the quasi-compact-complement hypotheses of the
pro-etale localization results used below.

We first record the sheaf calculation needed for clause (2), on both sites. For a complementary
open/closed pair j,i, restriction is exact and commutes with ordinary tensor: on the etale site
use the exact module inverse image, and on the pro-etale site use the
identified-constant-coefficient operations; the algebraic inverse-image tensor comparison
applies to both. The etale open-closed sequence is [lem-weil-pbc-open-closed-short-exact], and
its pro-etale counterpart, exact i_*, and all four restriction identities are
[lem-weil-pbc-proetale-ringed-open-closed]. In the etale case the open unit, closed counit, and
the two vanishing lemmas give the same identities j^*j_!=1, i^*i_*=1, i^*j_!=0, j^*i_*=0; the
maps are module-linear because their underlying adjunction maps are. Exactness of i_* in this
case is explicitly part of [lem-cbc-open-closed-recollement]. On either site the open-closed
sequence shows that a sheaf with both restrictions zero is zero. For any short exact sequence,
tensor with H and form its homology objects (including the outer kernel and cokernel). If j^*H
and i^*H are flat, exactness and the tensor comparison imply that each such homology object
restricts to zero on both sides, hence is zero. Thus tensor with H preserves short exact
sequences: flatness can be tested on this open/closed pair. In particular j_! and i_* preserve
flat sheaves, using their restriction identities. This argument works for all module sheaves,
including nonclassical pro-etale test sheaves. We also need to compare scheme structures, rather
than identify a topologically open immersion with an open immersion of schemes. If h:T→Y is a
surjective closed immersion, its open complement is empty. The same sequences give an
isomorphism of the unit H→h_*h^*H, and the closed counit gives h^*h_*≅1. Thus h^* and h_* are
inverse equivalences for ordinary module sheaves, and a constant A-module sheaf pulls back to
the same constant model. Finite local constancy is reflected by h^*: on the etale site h is a
universal homeomorphism by [lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism],
so [prop-weil-pbc-universal-homeomorphism-topos] identifies the topoi, constants and covering
epimorphisms. On the pro-etale site, apply
[new-lem-weil-pbc-proetale-surjective-closed-cover-refinement] to a trivializing cover of T. It
gives a cover B of Y whose pullback B×_Y T refines that cover. On each B, the unit and counit
just proved for the surjective closed immersion B×_Y T→B identify H|_B with the constant module
model on B, since their pullbacks are isomorphic. This proves reflection with the same finite
projective models; the empty complement is quasi-compact even when B is not Noetherian.

For a locally constant L with finite projective geometric stalks, each constant model on a
nonempty trivializing object is isomorphic to a geometric stalk: choose a geometric point of
that object and apply [lem-fix-geometric-stalk-topos-point]. Thus its models are finite
projective (empty objects can be discarded). Such L is flat: on a trivializing covering, a
displayed splitting M\oplus N=A^r gives L\oplus\underline N=A_S^r, so tensoring any short exact
sequence with L is a retract of its r-fold direct sum, which is short exact. Exactness can be
checked on the covering: kernels and cokernels restrict to zero, hence vanish by the sheaf axiom
and local lifting of sections. Factor a:S\hookrightarrow X as an open
j:S\hookrightarrow\overline S followed by a closed g:\overline S\hookrightarrow X, and put
a_!=g_*j_!. Step 4 makes a_!L flat. Its restrictions are L on S and zero on \overline S\setminus
S and X\setminus\overline S, by the same restriction identities. These three pieces are locally
closed and hence constructible in the Noetherian space by [def-weil-constructible-subset], so
a_!L is constructible on either site by the constructibility definitions. Finally a_!L[0] is a
bounded-above complex of flat sheaves, hence K-flat by
[lem-weil-pbc-independent-bounded-flat-kflat]. Its derived tensor with every module sheaf N[0]
is the degree-zero ordinary tensor a_!L\otimes_A N. It therefore has Tor amplitude [0,0] and
belongs to \Dctf. This proves the assertion about all generators, not only the strata of one F.

First verify closed/open interchange on either site. In a cartesian square with closed g:Z→X,
open u:W→X, open v:Z_W→Z and closed h:Z_W→W, the restriction formula for direct image gives
u^*g_*v_!L≅h_*L, so open adjunction gives a map u_!h_*L→g_*v_!L. Pulling back by g, the
open-extension base-change statements [lem-cbc-extension-zero-base-change] and
[lem-cbc-proetale-extension-zero-base-change] identify the left side with v_!h^*h_*L≅v_!L; the
right side is v_!L by the closed counit. The induced map is v_! of that counit and is
invertible. On the open complement of Z, the right side is zero; base change for u_! identifies
the left side with extension of the restriction of h_*L to W\Z, which is zero by the open/closed
vanishing identity. The exact open-closed sequence detects isomorphisms, so the map is an
isomorphism. Every complement here is quasi-compact by step 1. This also identifies the
definition g_*j_! using scheme-theoretic closure with u_!h_* in any open W where the immersion
is closed: the closure restricted to W is that closed subscheme, since its affine defining
kernel is the same quotient ideal. Induct on the number of ordered strata, allowing the given
strata to have arbitrary locally closed subscheme structures. With no strata the open-closed
sequence for the empty closed/open pair gives F=0 and the extension tower is empty. Otherwise
let U be the actual open subscheme of X with underlying set S_1, and let i:C→X be the reduced
induced closed subscheme on its complement, using
[lem-weil-pbc-reduced-induced-closed-subscheme]. Write u:U→X for the open immersion. The
immersion S_1→X factors as a surjective closed immersion h:S_1→U followed by u: in a
closed-then-open factorization, the latter open contains U and the defining ideal restricts to
U. Step 4 gives F|_U≅h_*L_1. The open-closed sequence is therefore 0→u_!h_*L_1→F→i_*i^*F→0. Here
u_!h_*L_1≅a_{1!}L_1 by the closed/open calculation just proved. For k≥2 use D_k=S_k×_X C with
maps b_k:D_k→C and p_k:D_k→S_k. Base change preserves immersions by
[lem-weil-pbc-immersion-base-change-lft]; p_k is closed by
[lem-weil-pbc-closed-immersion-base-change] and is surjective because C has precisely the closed
underlying tail, and a closed immersion has unchanged residue fields, so the fibre over any
point of S_k in the tail is that same point ([lem-weil-pbc-fibre-product-points]). The D_k give
the remaining ordered partition of C. The sheaf i^*F is flat by flat pullback and constructible:
its restriction to D_k is p_k^*L_k, with the pulled-back local trivializations. Apply the
induction hypothesis on C, which is Noetherian by step 1. Exact i_* gives a tower with factors
i_*b_{k!}p_k^*L_k. These factors equal a_{k!}L_k as follows. Use the closed/open calculation to
compute extension along an immersion in an open neighbourhood W in which its image is closed.
The intersection D_k→X has the same locally closed underlying image as S_k. In such a W the two
immersions are closed and the map D_k→S_k is the surjective closed immersion p_k. Step 4
identifies L_k≅p_{k*}p_k^*L_k. Closed direct images compose, since their values on V are
sections on V×_W D_k. Extending the resulting isomorphism by zero from W proves
i_*b_{k!}p_k^*L_k≅a_{k!}L_k; computing the left side inside C first agrees by closed/open
interchange for C→X and W→X, followed by composition of the closed direct images. Thus the first
sequence and the pushed-forward tower prove clause (2), including nonreduced strata, without
assuming that S_1→X itself is open. -/
theorem proEtale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F)
    (_hf : SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := proEtaleConstantRing X A) F)
    (str : LocallyClosedStratification X) (_ho : FlatModelOrderedStratification str)
    (_hp : ∀ k : Fin str.n, FlatModelProEtaleLisseProjective (str.domain k) A
      (proEtaleConstantModulePullback (str.immersion k) A F)) :
    FlatModelExtensionFiltration
      (fun k : Fin str.n ↦
        (flatModelProEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          (proEtaleConstantModulePullback (str.immersion k) A F)) F ∧
    ∀ k : Fin str.n,
      ∃ G : proEtaleRingModules X (proEtaleConstantRing X A),
        G = (flatModelProEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          (proEtaleConstantModulePullback (str.immersion k) A F) ∧
        SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
          (R := proEtaleConstantRing X A) G ∧
        IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) G ∧
        (∀ q : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A)
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (HasFiniteProEtaleTorAmplitude X A
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)) := by
  sorry

/-- Clause (3) on the proEtale site: equality with the smallest replete full
subcategory closed under shifts, cones and direct summands.
Source: blueprint det-sf-flat-model-generation
(blueprint: det-sf-flat-model-generation).

Proof:
For a locally constant L with finite projective geometric stalks, each constant model on a
nonempty trivializing object is isomorphic to a geometric stalk: choose a geometric point of
that object and apply [lem-fix-geometric-stalk-topos-point]. Thus its models are finite
projective (empty objects can be discarded). Such L is flat: on a trivializing covering, a
displayed splitting M\oplus N=A^r gives L\oplus\underline N=A_S^r, so tensoring any short exact
sequence with L is a retract of its r-fold direct sum, which is short exact. Exactness can be
checked on the covering: kernels and cokernels restrict to zero, hence vanish by the sheaf axiom
and local lifting of sections. Factor a:S\hookrightarrow X as an open
j:S\hookrightarrow\overline S followed by a closed g:\overline S\hookrightarrow X, and put
a_!=g_*j_!. Step 4 makes a_!L flat. Its restrictions are L on S and zero on \overline S\setminus
S and X\setminus\overline S, by the same restriction identities. These three pieces are locally
closed and hence constructible in the Noetherian space by [def-weil-constructible-subset], so
a_!L is constructible on either site by the constructibility definitions. Finally a_!L[0] is a
bounded-above complex of flat sheaves, hence K-flat by
[lem-weil-pbc-independent-bounded-flat-kflat]. Its derived tensor with every module sheaf N[0]
is the degree-zero ordinary tensor a_!L\otimes_A N. It therefore has Tor amplitude [0,0] and
belongs to \Dctf. This proves the assertion about all generators, not only the strata of one F.

The category \Dctf is thick. On the etale site, bounded constructible complexes are triangulated
by [prop-constructible-derived-subcategory]. They are also closed under retracts: if e is the
idempotent on each constructible cohomology sheaf induced by a retract, its image is the kernel
of 1-e and is constructible by [thm-constructible-serre]; the same finite cohomological bounds
persist. Tensoring a triangle with any N[0] is triangulated by
[lem-kun-derived-tensor-triangulated], so its cohomology long exact sequence shows that an
extension of objects with intervals [a,b] and [c,d] has interval [min(a,c),max(b,d)]. A shift by
n replaces [a,b] by [a-n,b-n], and a retract retains the interval because its tensor cohomology
is a retract of the original tensor cohomology. These arguments prove the etale assertion. For
the pro-etale site use the exact comparison and its triangulated derived functor, the
equivalence of bounded constructible categories [sk-thm-pe-constructible-comparison], and the
interval-preserving equivalence [det-pe-finite-tor-comparison-noetherian]. Here X is qcqs by
step 1 and A is Noetherian since its finite set of ideals has no infinite increasing chain. This
transfer respects ambient cones: lift the connecting morphism between the two bounded
constructible ends by full faithfulness and take its etale cone. It respects ambient retracts
too: on each cohomology sheaf lift the associated idempotent by the sheaf equivalence, take its
etale image as above, and apply exact comparison. Thus the other cone or retract stays bounded
constructible before applying the Tor comparison. All these are ordinary constant-ring module
categories.

Let C\in\Dctf(X,A), with Tor interval [a,b], a\le b. On the etale site
[lem-sf-etale-flat-constructible] gives an isomorphic complex P, zero outside [a,b], whose terms
are flat constructible. On the pro-etale site first use
[det-pe-finite-tor-comparison-noetherian] to choose C_0\in D^b_{ctf}(X_{\mathrm{et}},A) with
\nu_X^*C_0\cong C and the same interval. Apply the same etale model theorem to C_0 and pull its
model back termwise. The comparison functor is exact and commutes with cohomology, so the
pulled-back complex represents C and remains zero outside [a,b]. Its terms are constructible by
the sheaf equivalence and flat by the ringed-topos flat-pullback theorem. Hence a bounded flat
constructible model exists on either site for the general finite ring and general Noetherian X
of this item. This cites the independent model theorem, not the parent sk-lem-sf-flat-model
which uses this item.

Let \mathcal G be the full replete subcategory generated by the a_!L under the three indicated
operations. By steps 5 and 7, \mathcal G\subseteq\Dctf. For the reverse inclusion use P from
step 8. Write P_{\ge q} for its brutal tail, with P^r in degrees r\ge q and zero below.
Inclusion of the next tail and projection onto degree q give a degreewise split short exact
sequence 0\to P_{\ge q+1}\to P_{\ge q}\to P^q[-q]\to0: in degree q it is 0\to0\to
P^q\xrightarrow{1}P^q\to0, above q it is 0\to P^r\xrightarrow{1}P^r\to0\to0, and below q every
term is zero. The complex maps commute with differentials since the tail differential only
points upwards and the target single complex has zero differential. The short-exact-sequence
triangle theorem supplies a distinguished triangle with these three terms. By steps 3 and 6 each
flat constructible P^q is a finite extension of a_!L; placing its short exact sequences in
degree zero and applying the same triangle theorem gives P^q[0]\in\mathcal G, hence
P^q[-q]\in\mathcal G. Start with P_{\ge b+1}=0 (a cone of an identity of a generator) and induct
down from b to a along these triangles. This gives P_{\ge a}=P\in\mathcal G, so C\in\mathcal G.
This proves clause (3). -/
theorem proEtale_flatConstructible_thickGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A] :
    (fun K : proEtaleDerivedCategory X A ↦
      (∀ q : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A)
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (HasFiniteProEtaleTorAmplitude X A K)) =
    ObjectProperty.triangEnvelope
      (fun K : proEtaleDerivedCategory X A ↦
        ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
          (L : proEtaleRingModules S (proEtaleConstantRing S A)),
          FlatModelProEtaleLisseProjective S A L ∧
          Nonempty (K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((flatModelProEtaleExtension A a ha).obj L))) := by
  sorry

end AlgebraicGeometry
