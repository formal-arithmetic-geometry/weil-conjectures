/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
import Sheaf.AlgebraicGeometry.RelativeSplitTorusMatrixSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus

/-! # A split Borel pair for a split semisimple group

Source: Milne, Algebraic Groups (2017), Corollaries 21.30 and 21.34,
Theorem 21.32 and Corollary 21.33, pp.434--435; Theorem 13.33(a),(b),(e), pp.265--266.
(blueprint: lem-sfb-split-semisimple-borel-pair)

The auxiliary predicate packages the requested properties of the specified maps.
The multiplication isomorphism is the actual scheme map (u,t) ↦ iU(u) j(t).
Normality gives conjugation by j(t), so its transported group law is
(u,t)(u',t') = (u (t u' t⁻¹), t t'). The same maps are pulled back in the theorem's
scalar-extension clause; new unrelated choices are not made after extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The properties of the chosen Borel, radical, inclusion and retraction maps.
The kernel square is in schemes over k, and maximality of the unipotent radical is
scheme-theoretic factorization of subgroup inclusions. Borel solvability uses the
recorded derived series; split solvability uses the recorded represented fppf series.
The matrix-unipotence predicate requires a faithful representation on every geometric
point. Source: Milne, 13.33(a),(b),(e), pp.265--266, and 21.30--21.34, pp.434--435.
(blueprint: lem-sfb-split-semisimple-borel-pair) -/
def IsSplitSemisimpleBorelPair {k : Type u} [Field k]
    {G T B U : Grp (Over (Spec (.of k)))}
    (iT : T ⟶ G) (iB : B ⟶ G) (j : T ⟶ B) (iU : U ⟶ B) (p : B ⟶ T) : Prop :=
  IsClosedSubgroupScheme iB.hom.hom ∧ IsClosedSubgroupScheme j.hom.hom ∧
    IsClosedSubgroupScheme iU.hom.hom ∧ IsNormalSubgroupScheme iU.hom.hom ∧
    Smooth T.X.hom ∧ GeometricallyConnected T.X.hom ∧
    Smooth B.X.hom ∧ GeometricallyConnected B.X.hom ∧
    Smooth U.X.hom ∧ GeometricallyConnected U.X.hom ∧
    j ≫ iB = iT ∧ IsSplitSolvable B ∧ SolvableGroupStructure.IsUnipotent U ∧
    j ≫ p = 𝟙 T ∧ IsPullback iU.hom.hom (toUnit U.X) p.hom.hom η[T.X] ∧
    IsIso ((fst U.X T.X ≫ iU.hom.hom) * (snd U.X T.X ≫ j.hom.hom)) ∧
    ∀ (F : Type u) [Field F] [Algebra k F] [IsAlgClosed F],
      IsBorelGroupScheme ((MultiplicativeType.baseChange (K := F)).map iB).hom.hom ∧
      ∀ (V : Grp (Over (Spec (.of F))))
        (iV : V ⟶ (MultiplicativeType.baseChange (K := F)).obj B),
        IsClosedSubgroupScheme iV.hom.hom → IsNormalSubgroupScheme iV.hom.hom →
        Smooth V.X.hom → ConnectedSpace V.X.left → SolvableGroupStructure.IsUnipotent V →
        ∃ f : V ⟶ (MultiplicativeType.baseChange (K := F)).obj U,
          f ≫ (MultiplicativeType.baseChange (K := F)).map iU = iV

/-- A split maximal torus in a semisimple group is contained in a split Borel over k,
with its geometric unipotent radical and specified semidirect-product projection.
All the properties hold for the scalar extensions of these very maps.
No characteristic, perfection or simple-connectedness hypothesis is imposed.

Source: Milne, Corollaries 21.30 and 21.34, Theorem 21.32 and Corollary 21.33,
pp.434--435; Theorem 13.33(a),(b),(e), pp.265--266.
(blueprint: lem-sfb-split-semisimple-borel-pair)

Proof plan (the six DAG steps):
1. The identity section and lem-sbc-connected-rational-point-geometrically-connected
make G geometrically connected. Over the algebraic closure semisimplicity gives
reductivity by lem-sfb-reductive-borel-pair-structure. The geometric-neutral-reductivity
field-invariance lemma gives reductivity over every algebraically closed extension.
2. Use lem-sfb-affine-group-dual-number-calculus for the adjoint group-scheme
representation and the split-torus weight-decomposition lemma for its finite nonzero
weight set. The relative-split-torus-matrix-sheaf lemma gives integer weight rows.
Choose N larger than 1 plus each row's sum of absolute coefficients; the cocharacter
(1,N,...,N^(r-1)) has nonzero pairing with every row, since the final nonzero term
dominates all preceding terms. For no roots use zero, also in rank zero. The tangent
scalar-extension and dual-number lemmas identify the same character weights after
extension. Pairings are integers, even in positive characteristic.
3. Apply lem-sfb-reductive-cocharacter-parabolic-geometry to this regular cocharacter.
It supplies smooth geometrically connected closed P and U, with U normal and split
unipotent. The maximal-torus-field-extension lemma gives maximality over k; regularity
identifies the centralizer with T. The limit retraction p has kernel U, is the identity
on T, and multiplication U × T → P is an isomorphism with the displayed semidirect law.
4. Over every algebraically closed extension, maximal-torus-field-extension and
lem-sfb-regular-cocharacter-borel-description identify P with a Borel. Formation of
limit subgroups and their retraction commutes with every field extension, by the
cocharacter-parabolic-geometry lemma, so all the chosen maps and the decomposition
remain the same after extension.
5. In split coordinates let T_j have its first j coordinates equal to 1. The inverse
images p⁻¹(T_j) descend from B to U. By lem-sfb-affine-normal-quotient-geometry they
are smooth connected closed subgroups, each normal in its predecessor, with the
coordinate projection presenting quotient G_m. Append the split additive series of U.
This is precisely def-sfb-split-solvable-right-torsors. These series persist after
extension: the connected-rational-point lemma preserves connectedness and smooth
base change (lem-pc-proper-base-change, clause (2)) preserves smoothness. Empty series
include rank zero and the trivial U.
6. Induct along U's additive series with lem-sfb-unipotent-extension-arbitrary,
starting with 1 and G_a in upper unitriangular matrices, to obtain faithful matrix
unipotence. It persists under extension. Any smooth connected normal unipotent V
in B_F maps trivially to the split torus by lem-sfb-unipotent-to-multiplicative-trivial.
Hence V factors scheme-theoretically through ker(p_F)=U_F, proving radical maximality.
-/
theorem split_semisimple_borel_pair {k : Type u} [Field k]
    (G T : Grp (Over (Spec (.of k))))
    (hGsmooth : Smooth G.X.hom) (hGconnected : ConnectedSpace G.X.left)
    (hGaffine : IsAffine G.X.left) (hGfinite : LocallyOfFiniteType G.X.hom)
    (hGqc : QuasiCompact G.X.hom)
    (hGsemisimple : IsSemisimpleGroupScheme
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X)
    (iT : T ⟶ G) (hTclosed : IsClosedSubgroupScheme iT.hom.hom)
    (hTsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (hTmaximal : ReductiveTorusCentralizer.IsMaximalTorus
      ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).map iT)) :
    ∃ (B U : Grp (Over (Spec (.of k))))
      (iB : B ⟶ G) (j : T ⟶ B) (iU : U ⟶ B) (p : B ⟶ T),
      IsSplitSemisimpleBorelPair iT iB j iU p ∧
      ∀ (L : Type u) [Field L] [Algebra k L],
        IsSplitSemisimpleBorelPair
          ((MultiplicativeType.baseChange (K := L)).map iT)
          ((MultiplicativeType.baseChange (K := L)).map iB)
          ((MultiplicativeType.baseChange (K := L)).map j)
          ((MultiplicativeType.baseChange (K := L)).map iU)
          ((MultiplicativeType.baseChange (K := L)).map p) := by
  sorry

end AlgebraicGeometry
