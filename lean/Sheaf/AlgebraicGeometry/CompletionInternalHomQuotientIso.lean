module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Finite-level internal Hom quotient isIso

Source: Stacks Project, Cohomology of Schemes, Tag 0882, comparison-map construction.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-isIso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Precomposition with the level-m source quotient is an internal-Hom
isomorphism into the level-n target quotient when n ≤ m.

Source: Stacks Project, Cohomology of Schemes, Tag 0882, construction of the
comparison map, and Section 0EHN, equation 0880. This finite-level cokernel
argument requires neither coherence nor a Noetherian scheme.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-isIso).

Proof: Write Q = F/I^n F. Multiplication by I^n on Q is zero: the quotient
projection kills the image of multiplication I^n tensor F → F, and sections
of Q locally lift to F. Since n ≤ m, I^m is contained in I^n, so I^m also
annihilates Q. On any open U, an O_U-linear sheaf map G|U → Q|U therefore
kills I^m G|U: locally its generators ax map to a times the image of x,
which is zero. Restriction to U preserves cokernels of sheaves of modules,
so the cokernel universal property gives a unique map (G/I^m G)|U → Q|U
whose precomposition is the given map. Uniqueness makes these factorizations
compatible with restrictions, addition and scalar multiplication. Thus they
define a morphism between the internal-Hom sheaves in the reverse direction.
Precomposition after this morphism is the identity by its defining property;
the reverse composite is the identity by uniqueness in the cokernel property.
These two identities give the required isomorphism. -/
theorem completion_internal_hom_quotient_isIso {X : Scheme.{u}}
    (I : X.IdealSheafData) (F G : X.Modules) (m n : ℕ) (h : n ≤ m) :
    IsIso (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I m G) (𝟙 (formalModuleQuotient I n F))) := by
  sorry

end AlgebraicGeometry
