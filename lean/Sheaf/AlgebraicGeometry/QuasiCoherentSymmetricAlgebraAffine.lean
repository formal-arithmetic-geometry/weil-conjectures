/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
import Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Sheaf.RingTheory.SymmetricAlgebraBaseChange
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Affine comparison for the symmetric algebra sheaf

Source: Stacks Project, Schemes, Lemma 01I8 and Modules, Lemma 01CG.
(blueprint: lem-weil-pbc-quasi-coherent-symmetric-algebra-affine).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The ring sheafification of the sectionwise symmetric algebra is quasi-coherent and its
unit is bijective on affine sections. Source: Stacks Project, Modules, Lemmas 01CG, 01CH,
01CL and Schemes, Lemma 01I8; Algebra, Lemma 0C6F.
(blueprint: lem-weil-pbc-quasi-coherent-symmetric-algebra-affine).

Proof: fix an affine U with ring R and put A = Sym_R(F(U)). The sheafification unit on U,
viewed as an R-linear map, corresponds by the tilde adjunction to a map from the tilde of A
to the restriction of the sheafification. On any smaller affine V, quasi-coherence of F
identifies F(V) with O(V) tensor_R F(U). Symmetric algebra base change therefore identifies
the sectionwise symmetric algebra on V with O(V) tensor_R A. The same tensor product
computes the sections of the tilde of A. These identifications commute with restrictions
and intertwine the comparison with the sheafification unit. That unit is an isomorphism
on stalks: forgetting to abelian groups commutes with ring sheafification. Represent germs
on affine neighbourhoods. Surjectivity of the stalk comparison follows from surjectivity
of the stalk unit and the affine tensor identifications; for injectivity, a zero germ has
zero image under the unit after a further restriction, and injectivity of the tensor
identification makes its original germ zero. Thus the tilde comparison is an isomorphism.
The local tilde descriptions imply quasi-coherence, and taking sections on U identifies
the unit with a composite of two bijections (tilde global sections and the comparison). -/
theorem quasiCoherentSymmetricAlgebra_affine_comparison
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] :
    (SymmetricAlgebraSheaf.algebra F).toModule.IsQuasicoherent ∧
      ∀ U : X.affineOpens,
        Function.Bijective (SymmetricAlgebraSheaf.sectionMap F (op U.1)) := by
  sorry

end AlgebraicGeometry
