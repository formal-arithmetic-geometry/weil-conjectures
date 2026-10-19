/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
public import Sheaf.Paper.PrimeFieldTensorDevissage
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.RingTheory.FiniteAlgebraExternalTensorFiltration
import Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent
import Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence
import Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor
import Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage

/-!
# Finite tensor generators for a directed Galois partition

Source: ILO, Travaux de Gabber, Expose XVII, Propositions 7.4.2, 7.4.3 and 7.4.6,
Definition 7.4.5 and Lemmas 7.4.4 and 7.4.7, pp. 305--308
(blueprint: lem-per-directed-galois-finite-tensor-generators).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GaloisPartition

/-- A finite prime-field list, chosen before the coefficient algebra, gives ambient
constructible tensor filtrations; arbitrary weakly constructible objects are small filtered
colimits of constructible subobjects. The scalar action in the ordinary mixed tensor is on N.
Source: ILO XVII, 7.4.2--7.4.7, pp. 305--308
(blueprint: lem-per-directed-galois-finite-tensor-generators).

Proof plan:
1. Put Z_i=X\setminus(S_1\cup\cdots\cup S_{i-1}) with its reduced structure, and factor
k_i:S_i\to X as its open inclusion into Z_i, followed by the closed inclusion into X. All
these schemes are Noetherian: a closed affine chart has ring R/J, whose increasing ideal
chains lift to those of R, and open subschemes are covered by
[lem-weil-pbc-noetherian-open-subscheme-noetherian]. Open extension is exact by
[lem-weil-pbc-extension-by-zero-exact]; closed direct image is exact and fully faithful by
[lem-trf-oriented-closed-base-localization]. Their stalks are the original stalks on the stratum
and zero off it, by [lem-weil-pbc-extension-by-zero-stalks, lemma-openclosed-stalk-lowerstar]
and the closed-support description in the closed-base lemma. Consequently k_{i!} preserves
constructibility and membership in the fixed partition class: on S_i it is the given sheaf,
and on every other stratum it is zero. It also preserves small filtered colimits. For open
extension this follows from its sheafified presheaf formula [def-weil-pbc-extension-by-zero]:
extend the sectionwise colimit by zero and sheafify. For a closed inclusion c, a colimit of
sheaves supported on Z_i is still zero on the complement, since inverse image preserves
colimits [prop-weil-pbc-inverse-image-modules-exact]. The closed-base lemma identifies it with
c_*c^{-1} of that colimit; applying c^{-1} and its counit identifies it with the colimit on
Z_i.

2. On a nonempty stratum S with cover V\to S, choose a geometric point above one on S. The
cover has a continuous surjection G\to\operatorname{Aut}_S(V) with kernel H=\pi_1(V) by
clause (1) of [lem-per-galois-descent-monodromy-tensor]; thus H is normal and open. By
[lem-per-torsion-local-system-monodromy], the sheaves defining \mathcal W are local systems
and correspond exactly to discrete continuous A-linear modules for G=\pi_1(S) which are
ind-unipotent for the normal open subgroup H=\pi_1(V). This uses the cover-descent, extension
and colimit clauses of that node. The coefficient ring is killed by \ell, as its hypotheses
require. By [lem-per-normal-subgroup-ind-unipotence], the class is closed under submodules, and
a finitely generated member is H-unipotent. Each finite set of elements of a discrete
continuous module has a finite union of G-orbits: the stabilizers are open, hence have finite
index. The A-span of those orbits is therefore a finitely generated G-stable submodule.
These submodules form a directed union of the whole module and remain H-ind-unipotent. The
monodromy equivalence identifies their sheaves with locally constant finite-type subobjects,
hence constructible ones. Submodules and quotients of a finitely generated member remain finite
over A by [lem-weil-pbc-noetherian-submodule-finite]. Its finite H-unipotent filtration
therefore has finitely generated successive quotients trivial on H. The same argument shows
that an object of \mathcal W on any of the finitely many strata is locally constant of finite
type precisely when its stalk module is finitely generated. In particular any subobject in
\mathcal W of an object with finite stalk modules has finite stalk modules and is
constructible on the fixed strata.

3. For each stratum write K_i=\operatorname{Aut}_{S_i}(V_i) and B_i=\Lambda[K_i]. Choose one
representative of each simple left B_i-module. There are only finitely many: B_i is a finite
set, so it has finitely many left ideals, and every simple module is a quotient of its regular
module by a maximal left ideal (send b to bv for a nonzero vector v). Each representative
is finite-dimensional over \Lambda, since it is such a quotient. The exact descent equivalence
[lem-per-galois-cover-module-descent] gives a locally constant finite-type sheaf T_i(L) on
S_i trivialized by V_i. Take as the fixed list all C_{i,L}=k_{i!}T_i(L). Step 1 proves
that they are constructible and belong to \mathcal W_{\mathcal P}(\Lambda). The list is finite
and was chosen before choosing A or E.

4. Let L be a locally constant finite-type A-module sheaf on S_i trivialized by V_i.
Under [lem-per-galois-cover-module-descent] it corresponds to a finitely generated A-module
M with K_i-action, or equivalently to a module for A\otimes_\Lambda B_i. A finite
A-generating set also generates it over that algebra. Apply
[lem-per-finite-algebra-external-tensor-filtration] with the finite-dimensional algebra B_i.
Its quotients are retracts of N\otimes_\Lambda L_0 for finite A-modules N and simple
B_i-modules L_0. Replace L_0 by its representative from Step 3. Exact additive descent
carries the filtration, inclusion and retraction to sheaves. Its mixed tensor clause identifies
the tensor with N_{S_i}\otimes_{\Lambda_{S_i}}T_i(L_0). Combining this filtration with the
finite unipotent filtration of Step 2 gives the corresponding tensor filtration for every
constructible member of the one-stratum class. All intermediate sheaves have finite stalk
modules and lie in that class by Step 2.

5. For the factors just obtained, the canonical projection map gives
N_X\otimes_{\Lambda_X}k_{i!}T_i(L_0)\ \simeq\
k_{i!}(N_{S_i}\otimes_{\Lambda_{S_i}}T_i(L_0)). Constant modules restrict to the same constant
modules by [lem-sfb-geometric-inverse-image-constant-module], and inverse image commutes with
tensor by [lem-weil-pbc-ringed-topoi-module-pullback-tensor], applied to the constant rings
identified in [prop-weil-pbc-inverse-image-modules-exact]. For the open part, construct the map
by the extension/restriction adjunction, restricting on S_i to the identity on pure tensors.
For the closed part, use the map to c_*c^{-1} followed by evaluation on pure tensors on the
closed subscheme; the closed-base counit is the identity there
[lem-trf-oriented-closed-base-localization]. The stalk tensor formula
[lem-pod-etale-stalk-tensor-scalar] and the extension stalk formulas from Step 1 identify both
maps with the ordinary module tensor identity on the stratum and 0\to0 off it. Hence
[lem-weil-pbc-sets-etale-iso-on-geometric-stalks] makes them isomorphisms. The maps are
A-linear, with A acting only on N. Thus the exact additive functor k_{i!} carries the
filtration and its retract data to the required ambient tensor filtration on X.

6. For constructible E, repeatedly apply the actual open/closed sequence
[lem-weil-pbc-open-closed-short-exact] 0\to j_!j^{-1}E\to E\to c_*c^{-1}E\to0 with
j:S_1\hookrightarrow X and c:Z_2\hookrightarrow X, then with the first stratum of Z_2, and
so on. This finite recursion gives a filtration with factors k_{i!}(E|_{S_i}). Each E|_{S_i}
lies in the one-stratum class and has finitely generated stalks, so Step 2 makes it locally
constant of finite type on that whole stratum. Steps 4 and 5 provide a finite tensor filtration
of each factor with the fixed C_{i,L}. Lift each factor's subobjects by inverse image along
the relevant quotient map and concatenate these finite filtrations. This is the elementary
refinement of a finite filtration in an abelian category. The exactness and extension closure of
[lem-per-galois-partition-exact-refinement], together with the finite stalk assertion of Step 2,
keep every intermediate term and quotient constructible and in the fixed class. This proves the
finite-filtration assertion for every A, without varying the list in Step 3.

7. We need the following extension argument for the filtered-union assertion. Suppose 0\to H\to
F\to G\to0 lies in the fixed class, G is constructible, and H is a directed union of
constructible subobjects H_a in that class. Apply
[lem-per-constructible-extension-finite-stage]. It gives 0\to H_a\to F_a\to G\to0 mapping into
the given sequence. The map F_a\to F is mono, so we view F_a as a subobject. For any b\geq
a, its sum with H_b is the pushout along H_a\to H_b, with exact sequence 0\to H_b\to
F_a+H_b\to G\to0. These subobjects are in the fixed class by
[lem-per-galois-partition-exact-refinement], and constructible by
[lem-sfb-discrete-noetherian-constructible-serre], [lem-sfb-noetherian-global-constructibility]
and [lem-sc-noetherian-finite-module-finite-presentation]. Their union contains H and surjects
onto G, hence is all of F. More explicitly F/(F_a+H)=0 by the displayed exact sequences.
Exactness of filtered colimits [lem-weil-pbc-module-sheaves-grothendieck-abelian] identifies
this union with the filtered colimit of the inclusions. This is the finite-stage extension
argument in the proof of 7.4.4.

8. Induct on the number of strata to show every E in the class is a union of constructible
subobjects in it. The empty case is zero; one stratum is Step 2. For more strata, the sequence
of Step 6 has kernel H=j_!j^{-1}E, which is such a union by Steps 1 and 2. By induction
c^{-1}E is a union of constructible subobjects in the remaining partition. Step 1 carries this
union to the quotient c_*c^{-1}E. For each constructible subobject G of that quotient in the
class, take its inverse image F\subseteq E. It fits into 0\to H\to F\to G\to0 in the class,
by its exactness and kernel closure [lem-per-galois-partition-exact-refinement]. Step 7
expresses F as the required union. The union of these F is E, by exact filtered colimits
[lem-weil-pbc-module-sheaves-grothendieck-abelian]. To obtain a single directed indexing set,
use all constructible subobjects of E in the class, ordered by inclusion. Finite sums remain
in the class and have finitely generated stalk modules; by the last assertion of Step 2 they are
constructible. Thus this poset is directed and nonempty (it contains zero). It is a set in the
site-and-coefficient universe: subobjects are represented by subsheaves of the fixed sheaf E
on a small site. Its colimit is E by the union just proved. This supplies the small filtered
colimit required in the statement.

9. If E=0, all filtrations may be empty. If X is empty, its module-sheaf category contains
only the zero object, the stratum list is empty, and take r=0; the singleton diagram on zero
supplies the filtered presentation. If A is the zero ring the same construction gives zero
throughout. No step requires \ell invertible on X, nor finite underlying sets for A or
N. -/
theorem finite_tensor_generators (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X] (P : GaloisPartition X) (hP : P.IsDirected) :
    ∃ (r : ℕ)
      (C : Fin r → Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))),
      (IsEmpty X → r = 0) ∧
      (∀ a, P.constructible (ULift.{u + 1} (ZMod ℓ)) (C a)) ∧
      ∀ (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
        [Algebra (ULift.{u + 1} (ZMod ℓ)) A],
        (∀ (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
          P.constructible A E →
          ∃ (n : ℕ) (H : Fin (n + 1) → Subobject E) (hH : Monotone H),
            IsZero (H 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ∧
            IsIso (H (Fin.last n)).arrow ∧ (IsZero E → n = 0) ∧
            (∀ j, P.constructible A (H j : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) ∧
            ∀ i : Fin n, ∃ (a : Fin r) (N : ModuleCat.{u + 1} A),
              Module.Finite A N ∧
              ∃ (ι : cokernel (Subobject.ofLE (H i.castSucc) (H i.succ)
                    (hH (Fin.castSucc_le_succ i))) ⟶
                  (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a))
                (π : (Etale.primeFieldTensorSheaf X ℓ A N).obj (C a) ⟶
                  cokernel (Subobject.ofLE (H i.castSucc) (H i.succ)
                    (hH (Fin.castSucc_le_succ i)))),
                ι ≫ π = 𝟙 _) ∧
        (∀ (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)), P.modules A E →
          ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
            (D : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
            (c : Cocone D),
            (∀ i, P.constructible A (D.obj i)) ∧
            (∀ i, Mono (c.ι.app i)) ∧ Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ E)) := by
  sorry

end AlgebraicGeometry.Scheme.GaloisPartition
