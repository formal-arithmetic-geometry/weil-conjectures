module

public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Restriction comparison for the canonical relative Proj

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC, affine-local comparison.
(blueprint: lem-trf-canonical-relative-proj-restriction-comparison).
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical relative Proj commutes with restriction to an affine open: the relative Proj
of Sym(E|_U) over U is isomorphic, over U, to the preimage of U in the relative Proj of Sym(E).

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC, affine-local comparison;
Constructions, Tag 01NQ.
Proof: for an affine open V ⊆ U, the sections of E|_U over V are the sections of E over the
image of V in S, so the canonical graded algebra of Sym(E|_U) on V is the canonical graded
algebra of Sym(E) on the image of V, compatibly with the restriction maps.  Both relative
Proj schemes are glued from the charts Proj(Sym(E)(V)) along the same transition maps, and
over each such V the preimage of V in the global relative Proj is the chart Proj(Sym(E)(V))
(`isPullback_relProjι`).  Hence the chart embeddings of the relative Proj over U into the
preimage of U glue to an isomorphism; on each chart it commutes with the structure maps
(`relProjι_relProjHom`), so `e.hom ≫ (relProjHom ∣_ U)` equals the structure map over U.
(blueprint: lem-trf-canonical-relative-proj-restriction-comparison). -/
theorem exists_canonicalRelativeProj_restrict_iso {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) (U : S.Opens) (hU : IsAffineOpen U)
    (hq : (E.restrict U.ι).IsQuasicoherent) :
    ∃ (e : (@SymmetricAlgebraSheaf.gradedAlgebraData U.toScheme (E.restrict U.ι) hq).relProj ≅
      ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ⁻¹ᵁ U).toScheme),
      e.hom ≫ ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ∣_ U) =
        (@SymmetricAlgebraSheaf.gradedAlgebraData U.toScheme (E.restrict U.ι) hq).relProjHom := by
  sorry

end AlgebraicGeometry

end
