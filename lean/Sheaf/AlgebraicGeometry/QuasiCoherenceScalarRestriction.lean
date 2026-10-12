/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Quasi-coherence and restriction of scalars

Source: Stacks Project, Morphisms, Lemma 0H88; EGA I, Proposition 9.6.1
(blueprint: lem-weil-pbc-quasi-coherence-scalar-restriction).

The quasi-coherent `𝒪_S`-algebra is the shared form `A : S.CommAlgebraSheaf`
(`= Under S.sheaf`, def-weil-pbc-comm-algebra-sheaf) with `A.toModule.IsQuasicoherent`;
`A`-modules are `SheafOfModules` over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj A.right` and their underlying
`𝒪_S`-modules are obtained by scalar restriction along `A.hom`, as in
`lem-weil-pbc-quasi-coherent-algebra-change-of-rings`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-coherent commutative algebra sheaf on a scheme, an algebra-module sheaf
is quasi-coherent exactly when its underlying structure-sheaf module is quasi-coherent.
The algebra is `A : S.CommAlgebraSheaf` with structure map `A.hom`; the hypothesis `hA`
requires its underlying module `A.toModule` to be quasi-coherent. Mathlib's
`IsQuasicoherent` is the local
presentation by arbitrary direct sums of copies of the ring sheaf (Stacks 01BE),
equivalent on schemes to the affine-local tilde condition of `pqf-def-coherent` (01IA).

Source: Stacks Project, Morphisms, Lemma 0H88; EGA I, Proposition 9.6.1
(blueprint: lem-weil-pbc-quasi-coherence-scalar-restriction).

Proof, following the six steps of the node:
1. Forgetting algebra scalars preserves direct sums and exact sequences, since both
module categories have exact forgetful functors to abelian sheaves preserving colimits
(`lem-weil-pbc-module-sheaves-colimits-forgetful`).
2. On an affine open `U = Spec R`, put `B = A(U)`. The tilde-Gamma adjunction identifies
the underlying module of each direct sum of copies of `A|U` with the tilde of the
corresponding direct sum of copies of `B`. Thus these sums are quasi-coherent, using
`lem-weil-pbc-module-restriction-open-immersion-colimits` and
`lem-weil-pbc-affine-tilde-gamma-adjunction`.
3. A local algebra-module presentation is therefore a presentation by quasi-coherent
structure-sheaf modules. Its cokernel is quasi-coherent by
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, giving the forward implication.
4. Conversely, on an affine open put `M = G(U)`, a `B`-module by its sectionwise action.
Its restricted `R`-action agrees with the structure-sheaf action. Present `M` by free
`B`-modules, taking all elements as generators and all kernel elements as relations.
5. Define the maps between direct sums of `A|U` and `G|U` from these sections. They are
`A|U`-linear by compatibility of the action with restriction
(`def-weil-sheaf-of-modules-category`).
6. Under the tilde-Gamma identifications the maps are the tildes of the free presentation.
The tilde functor preserves cokernels and direct sums, so the sequence is exact as a
structure-sheaf sequence, hence also as an algebra-module sequence by step 1. These
affine presentations give algebra-module quasi-coherence, proving the converse. -/
theorem quasiCoherent_iff_restrictScalars (S : Scheme.{u})
    (A : S.CommAlgebraSheaf) (hA : A.toModule.IsQuasicoherent)
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right)) :
    G.IsQuasicoherent ↔
      ((SheafOfModules.restrictScalars
        ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
          A.hom)).obj G).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme.Modules
