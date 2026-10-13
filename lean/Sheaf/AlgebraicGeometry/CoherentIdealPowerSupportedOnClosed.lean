module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Concentrating an ideal-power product on a closed subset

Source: Stacks Project, Tags 01YD and 01Y9.
(blueprint: lem-pc-s3-coherent-ideal-power-supported-on-closed)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ideal-power product can be made to vanish away from a prescribed closed subset.

Source: Stacks Project, Tag 01YD, proof of Lemma 30.12.1, applying Tag 01Y9,
Lemma 30.10.2 (https://stacks.math.columbia.edu/tag/01YD).
(blueprint: lem-pc-s3-coherent-ideal-power-supported-on-closed)

Proof: Let V be the complement of C. It is a Noetherian open subscheme. Restrict
F and K to V. Coherence restricts to opens, and the support hypothesis identifies
the support of F on V as a subset of the zero set of the restricted ideal K.
On a finite affine cover of V, coherence gives finite section modules M over
Noetherian rings. The support containment implies I is contained in the radical
of Ann(M). Since I is finitely generated, some power I^n is contained in Ann(M).
Choose the maximum of these finitely many exponents; ideal powers are decreasing,
so it kills M on every member of the cover. The corresponding ideal-power product
sheaf therefore restricts to zero on V. Restriction commutes with multiplication,
tensor products and images, as checked on affine sections, so every stalk of
K^n F outside C is zero. This proves the support inclusion. K.toModules is
quasi-coherent because it is the ideal sheaf of a closed subscheme. Inductively
its powers are quasi-coherent: exponent zero is the structure sheaf, exponent
one is K, and each later power is the image of multiplication from the tensor
product of K and the previous power. Quasi-coherent sheaves on a scheme are
closed under tensors and images. For the empty open take n = 0; for F = 0 the
same exponent works. Neither coherence of the product or its quotient nor an
exact sequence or strict support containment is asserted here. -/
theorem coherent_ideal_power_supported_on_closed
    (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (K : X.IdealSheafData) (C : TopologicalSpace.Closeds X)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      (K.support : Set X) ∪ (C : Set X)) :
    ∃ n : ℕ, (idealSheafPower K.toModulesι n).1.IsQuasicoherent ∧
      {x : X | ¬ Subsingleton
        ((idealModuleProduct (idealSheafPower K.toModulesι n).2 F).presheaf.stalk x)} ⊆
        (C : Set X) := by sorry

end AlgebraicGeometry.Scheme.Modules
