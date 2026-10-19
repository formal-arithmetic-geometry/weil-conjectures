/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.FiniteLocalAbelianForget
import Sheaf.AlgebraicGeometry.SetLocalSystemCalculus
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale

/-!
# Finite locally constant subsystems of a torsion local system

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVII, Lemma 7.2.6,
p. 303 (blueprint: lem-per-torsion-finite-subsystem).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A torsion local system is the filtered union of its finite locally constant
subgroup sheaves. Source: ILO XVII, Lemma 7.2.6, p. 303
(blueprint: lem-per-torsion-finite-subsystem).

Proof, following the node's steps.
1. (lem-per-set-local-system-calculus, lem-galois-flc-representable; ILO XVII Def. 7.2.1,
   Prop. 7.2.3, p. 301) The set-local-system calculus writes the underlying set sheaf of `G`
   as a filtered union of finite local-system subsheaves `E`, represented by finite étale
   `X`-schemes; by finite-étale representability each `E` is finite locally constant. So a
   section of `G` lies étale locally in one such `E` (no global factorization is claimed).
2. (lem-per-finite-torsion-generated-subgroup; ILO XVII Lemma 7.2.6, p. 303) For each
   inclusion `E ↪ G` of Step 1 (X Noetherian, `G` an ind-finite étale set local system with
   torsion geometric stalks, `E` finite locally constant) the generated-subgroup lemma gives
   a finite locally constant abelian subgroup `H ↪ G` containing `E`. Hence the finite
   subgroup sheaves cover `G` locally on sections.
3. (lem-weil-pbc-finite-local-abelian-forget, lem-galois-flc-representable,
   lem-per-set-local-system-calculus, lem-per-finite-torsion-generated-subgroup) The zero
   subgroup is finite locally constant, so the poset is nonempty. Given `H₁, H₂`, the
   finite-local-abelian comparison makes their underlying set sheaves finite locally
   constant; by representability they are finite local-system subsheaves of `|G|`; the
   filtered clause of the calculus gives a finite `E` containing both, finite locally
   constant by representability, and Step 2 gives `H ⊇ E ⊇ H₁, H₂`. Smallness: choose a
   small skeleton of the étale site; a subgroup subsheaf is determined by subsets of `G(U)`
   for `U` in it, and these choices form a set, giving the small index `I` order-isomorphic
   to the family.
4. (elementary; ILO XVII Lemma 7.2.6, p. 303) By Steps 1 and 2 every section `s` on `U` lies,
   on the members of an étale cover, in finite subgroup sheaves. Given a compatible family of
   maps from these subgroups to a set sheaf `F`, define the image of `s` locally; on overlaps
   directedness puts two chosen subgroups in a common one, so the local images agree, and the
   sheaf axiom glues them uniquely, compatibly with restriction: the set-sheaf colimit
   property. For abelian `F` and homomorphisms, refine a cover to represent two sections in a
   common upper bound; the glued map is additive, and the same uniqueness gives the
   abelian-sheaf colimit. The empty scheme and the zero sheaf are the zero-subgroup case.
-/
theorem torsion_local_system_finite_subsystem
    (X : Scheme.{u}) [IsNoetherian X]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsIndFiniteEtaleSheaf
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G))
    (htorsion : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X)
      (g : (pointedEtaleStalk G t : AddCommGrpCat.{u + 1})),
      ∃ n : ℕ, 0 < n ∧ n • g = 0) :
    ∃ (I : Type (u + 1)) (_ : PartialOrder I) (S : I ↪o Subobject G)
      (ι : S.monotone.functor ⋙ Subobject.underlying ⟶ (Functor.const I).obj G),
      IsFiltered I ∧
      (∀ i : I, ι.app i = (S i).arrow) ∧
      (∀ H : Subobject G,
        (∃ (𝒰 : Cover.{u} etalePrecoverage X),
          ∀ j : 𝒰.I₀,
            ∃ (A : AddCommGrpCat.{u + 1}) (_ : Finite A),
              Nonempty
                ((H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).over
                    (𝒰.etalePrecoverageToEtale j) ≅
                  (constantSheaf
                    (X.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale j))
                    AddCommGrpCat.{u + 1}).obj A)) ↔
          ∃ i : I, S i = H) ∧
      Nonempty (IsColimit (Cocone.mk G ι)) ∧
      Nonempty (IsColimit
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapCocone (Cocone.mk G ι))) := by
  sorry

end AlgebraicGeometry.Scheme
