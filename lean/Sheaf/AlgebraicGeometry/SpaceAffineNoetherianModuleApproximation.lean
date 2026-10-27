/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentFilteredUnion
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleLocalNoetherianDescent

/-!
# Finite-presentation approximation over a Noetherian algebraic space

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 07UW,
lemma-direct-colimit-finite-presentation
(blueprint: lem-sfb-space-affine-noetherian-module-approximation).

The Noetherian target hypothesis is expressed by quasi-compactness of its point space,
absolute quasi-separatedness and a locally Noetherian surjective etale scheme atlas.
The colimit is taken in all module sheaves on the small etale ringed site of X.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every quasi-coherent module on a space affine over a Noetherian space is a small
filtered colimit of finitely presented quasi-coherent modules. Neither finite type of
f nor Noetherianity of X is assumed. The natural transformation records the compatible
maps, and its cocone is colimiting in all module sheaves, not just quasi-coherent ones.

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 07UW,
lemma-direct-colimit-finite-presentation
(blueprint: lem-sfb-space-affine-noetherian-module-approximation).

Proof:
1. By lem-sfb-qc-space-affine-etale-atlas choose an affine surjective etale chart
   V -> Y. Its pullback U -> X is affine by the hypothesis and surjective etale by
   lem-trf-space-fibre-products-etale-covers. Thus |X| is quasi-compact by
   def-a1-space-point-topology. Lem-sfb-space-affine-locality gives quasi-separatedness
   of X. Lem-pur-ringed-site-grothendieck-abelian supplies the abelian module category
   and its small colimits. Lem-sfb-space-affine-module-base-change makes f_*T
   quasi-coherent for every quasi-coherent T.
2. Every etale chart of Y is locally Noetherian: pull it back to the given atlas,
   use def-weil-etale-morphism and lem-weil-pbc-finite-type-over-noetherian, and descend
   by lem-trf-etale-local-noetherian-descent. Apply lem-sfb-space-coherent-filtered-union
   to f_*T, writing it as a small directed colimit of coherent submodules H_i.
   Lem-weil-pbc-coherent-local-finite-presentation and
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence turn their local coherent
   presentations into finite free etale presentations. The tensor left adjoint of
   lem-weil-pbc-ringed-topoi-module-adjunction preserves these cokernel presentations;
   lem-sfb-space-qcoh-affine-chart-calculus detects finite presentation on charts.
3. Put P_i = f^*H_i. The same left adjoint preserves their colimit and finite free
   presentations, giving colim P_i = f^*f_*T. Compatibility with etale restriction is
   lem-trf-space-etale-module-pushforward-restriction; quasi-coherence of P_i is
   lem-sfb-space-module-pullback-quasicoherent.
4. The counit colim P_i -> T is surjective. Restrict to the affine charts U -> V
   from step 1. Etale module pushforward restriction, affine chart calculus and
   lem-trf-space-chart-adjunction-tensor-realization identify it with
   B tensor_A N -> N, b tensor n |-> bn. Every n is the image of 1 tensor n.
   Surjectivity is local on the etale covering, so the counit is onto on X.
5. Apply this construction to M and then to the kernel N of P = colim P_i -> M.
   Lem-sfb-space-qcoh-kernels-colimits makes P and N quasi-coherent. The second
   application gives Q = colim Q_j surjecting onto N. Thus M is the cokernel of
   d : Q -> P in the abelian category of all module sheaves.
6. Let K consist of triples (i,j,a), where a : Q_j -> P_i and p_i a = d q_j.
   Order triples by increasing indices and commuting transition squares. This is a
   small partially ordered set in the bound of def-weil-size-convention.
   Lem-sfb-space-fp-module-hom-colimit factors each d q_j through some P_i, since X
   is qcqs and Q_j is finitely presented. Hence K is nonempty and every j occurs.
7. For two triples choose a common later j_0, factor d q_j_0 through some P_h,
   and enlarge h to dominate their first indices. The eventual-equality clause of
   lem-sfb-space-fp-module-hom-colimit makes both required squares commute after
   further enlarging h. The resulting triple is a common upper bound, so K is directed.
8. Put C_k = coker(a_k). Lem-sfb-space-qcoh-kernels-colimits makes C_k quasi-coherent.
   Locally choose a finite free presentation of P_i and finitely many generators of
   Q_j. On a further covering lift their images to the finite free generators of P_i.
   Adding these finitely many lifts to the existing relations gives a finite free
   presentation of C_k. Commuting squares induce compatible cokernel maps and maps
   C_k -> M, since the map P -> M kills d.
9. Both projections from K are cofinal: enlarge the first index to dominate any i;
   each j occurs by step 6; directedness supplies common upper bounds and proves
   independence of choices. Thus their colimits are P and Q. Compatible maps C_k -> L
   are exactly maps P -> L killing d, hence exactly maps M -> L. This is the colimit
   universal property in all module sheaves of def-weil-pbc-category-colimit.
   The small directed poset K, viewed as a category, is the required filtered J. -/
theorem exists_finitePresentation_filtered_colimit_of_affine_noetherian
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ha : MapIsAffine f)
    (hqc : CompactSpace (Point Y.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated Y)
    (hln : ∃ (V : Over S) (a : yoneda.obj V ⟶ Y.obj.obj),
      IsEtale a ∧ IsSurjective a ∧ IsLocallyNoetherian V.left)
    (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ X.Modules),
      (∀ j : J, (D.obj j).IsFinitePresentation ∧ (D.obj j).IsQuasicoherent) ∧
        ∃ ι : D ⟶ (Functor.const J).obj M,
          Nonempty (IsColimit (Cocone.mk M ι)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
