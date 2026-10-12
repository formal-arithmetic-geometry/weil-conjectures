module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Finite-level internal Hom quotient annihilation

Source: Stacks Project, Cohomology of Schemes, Tag 0882, comparison-map construction.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-annihilation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Postcomposition with the level-n quotient kills the level-n ideal product
of the internal Hom.

Source: Stacks Project, Cohomology of Schemes, Tag 0882, construction of the
comparison map, and Section 0EHN, equation 0880. The finite-level assertion is
an explicit preliminary argument for that comparison, valid without coherence.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-annihilation).

Proof: Put J = I^n and Q = F/JF, the cokernel of the product inclusion.
The product JF is the image of multiplication J tensor F → F. Its sections
are locally finite sums of products ax. The cokernel projection kills this
image. Sections of Q locally lift to F, so multiplication by J on Q vanishes
locally and hence vanishes as a sheaf morphism. For a local section a of J
and a local linear map t : G → F, postcomposition sends at to the map
x ↦ a times the class of t(x) in Q. This is zero by the preceding annihilation.
Sections of J Hom(G,F) are locally finite sums of such products. Their images
are therefore locally zero, hence zero. This proves the displayed composite
vanishes. The argument uses local lifts, not surjectivity on all open sections. -/
theorem completion_internal_hom_quotient_annihilation {X : Scheme.{u}}
    (I : X.IdealSheafData) (F G : X.Modules) (n : ℕ) :
    Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2
        (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G F) ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 G) (formalModuleQuotientπ I n F) = 0 := by
  sorry

end AlgebraicGeometry
