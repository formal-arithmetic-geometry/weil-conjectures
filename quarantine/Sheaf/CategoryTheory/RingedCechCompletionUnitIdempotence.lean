/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.CategoryTheory.RingedExtendedCech
import Sheaf.Paper.RingedLocalizationRHomCalculus

/-! # Idempotence of the actual Cech completion unit

Source: Stacks Project, algebraization.tex, Tag 099B.
(blueprint: lem-weil-pbc-ringed-cech-completion-unit-idempotence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- Applying Cech completion to its unit and evaluating the unit on a completed
object both give isomorphisms. These are statements about the two actual maps,
not about an unspecified isomorphism between double and single completion.

Source: Stacks Project, algebraization.tex, Tag 099B, proof of lemma-derived-completion.
(blueprint: lem-weil-pbc-ringed-cech-completion-unit-idempotence).

Proof: write K in degree q as the finite sum over q-element subsets I of the
localizations S_I = O[1/(product of b_i for i in I)], with S_empty = O. These sheaves
are flat, and K is bounded, so K is K-flat. For a nonempty I, choose j in I. In
K tensor S_I the j-th localization factor has invertible differential: b_j is already
invertible in S_I. Contract it by that inverse differential. On a tensor summand,
put the sign (-1) to the sum of the degrees preceding j; the other differential terms
cancel in d h + h d, while the j-th term gives the identity.

Cancel the identity ring-term pair in the cone of the augmentation K -> O. The
remaining positive localization complex has a finite filtration by Cech degree, with
graded terms finite sums of shifted S_I for nonempty I. After tensoring with K these
graded terms are contractible by the preceding formula, so the tensor is acyclic.
The tensor/mapping-cone comparison shows that id_K tensor epsilon followed by the
right unit comparison is a quasi-isomorphism. Symmetry gives the other projection,
epsilon tensor id_K followed by the left unit comparison.

For a K-injective representative I of E, Hom(K,I) is K-injective since K is K-flat.
Compute the actual unit on these representatives using evaluation at one and the
fixed functorial-replacement comparison defining derived internal Hom. Tensor-Hom
currying identifies L(eta_E) with Hom of id_K tensor epsilon, and eta_(L E) with
Hom of epsilon tensor id_K, after the respective ring-unit identifications. The
K-injective comparison maps intertwine these actual units; their compatibility follows
from evaluation at one and naturality of precomposition. Both projections are
quasi-isomorphisms, and Hom into I inverts them, proving both assertions. This uses
neither enough points nor exactness of infinite products. For the empty list the
positive filtration is empty and the projections are unit isomorphisms. An all-zero
list gives identity completion; an invertible generator gives contractible K and zero
completion. The same formulas include the zero ring and the empty site. -/
theorem ringed_cech_completion_unit_idempotence (E : ringedSiteDerived O) :
    IsIso ((ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).map
      (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2 E)) ∧
    IsIso (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
      (ringedExtendedCech O r b).2
      ((ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj E)) := by
  sorry

end CategoryTheory
