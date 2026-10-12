module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Global generators of algebra modules on an affine open

Source: Stacks Project, Morphisms, Lemma 0H88, proof, second paragraph;
EGA I, Proposition 9.6.1.
(blueprint: lem-weil-pbc-affine-algebra-module-generators).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Global generation is the first half of the affine algebra-module presentation.
Source: Stacks Project, Morphisms, Lemma 0H88, second paragraph; EGA I, Proposition 9.6.1.
(blueprint: lem-weil-pbc-affine-algebra-module-generators)

Proof: identify the open subscheme U with Spec O_S(U), and its slice site with the
opens of that subscheme. The underlying quasi-coherent module is the tilde of its
module of global sections. Those sections generate the tilde: on each principal open
every section is a fraction of a global section, and these opens form a basis. Give
these same global sections their A(U)-module structure. The A-linear evaluation map
from the free A-module sheaf on all sections contains the image of the O-linear
evaluation map. The latter is locally surjective, so the former is locally surjective
and hence epi. Transporting back to the slice gives the required generating sections.
This asserts only generation, not generation of the kernel or a presentation. -/
theorem nonempty_affine_algebraModule_generatingSections
    (S : Scheme.{u}) (A : S.CommAlgebraSheaf) (U : S.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u}
      (((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right).over U))
    (hM : ((SheafOfModules.restrictScalars
      (((Opens.grothendieckTopology S).overPullback RingCat U).map
        ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
          A.hom))).obj M).IsQuasicoherent) :
    Nonempty M.GeneratingSections := by sorry

end AlgebraicGeometry.Scheme.Modules
