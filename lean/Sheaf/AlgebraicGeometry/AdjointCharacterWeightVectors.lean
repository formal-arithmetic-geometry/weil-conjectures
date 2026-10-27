module

public import Sheaf.AlgebraicGeometry.RhoSectionModuleData
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring

/-! # Adjoint character weight vectors over arbitrary fields

Source: Milne, Algebraic Groups (2017), Theorem 12.12, Remark 12.13, pp.234--235,
and Definition 21.26, p.433 (blueprint: def-sfb-adjoint-character-weight-vectors).

The equations are tested on every commutative algebra. Testing only rational points
would identify different characters over a finite ground field.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.AdjointCharacter

/-- The A-valued tangent point of c times the scalar extension of v, obtained by
substituting epsilon ↦ c epsilon in the actual dual-number point of v.
Source: Milne, Chapter 10, tangent representation of conjugation
(blueprint: def-sfb-adjoint-character-weight-vectors). -/
def scaledTangentPoint {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k))))
    (A : Type u) [CommRing A] [Algebra k A] (c : A) (v : GrpObj.Lie G.X) :
    StandardGroupSchemes.affine k (DualNumber A) ⟶ G.X :=
  StandardGroupSchemes.map k
    (((DualNumber.scale c).restrictScalars k).comp (DualNumber.mapAlgebraMap A)) ≫
      GrpObj.tangentPoint v

/-- The actual character-weight vectors in Lie(G) for conjugation through i.
The point s is extended constantly to A[epsilon], and the vector is extended by
k[epsilon] → A[epsilon]. Thus this is the character-weight equation over every A,
including nonreduced algebras and finite fields, without differentiating the character.
Source: Milne, Theorem 12.12, pp.234--235, and Definition 21.26, p.433
(blueprint: def-sfb-adjoint-character-weight-vectors). -/
def weightVectors {k : Type u} [Field k]
    {T G : Grp (Over (Spec (.of k)))} (i : T ⟶ G)
    (chi : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)) :
    Set (GrpObj.Lie G.X) :=
  {v | ∀ (A : Type u) [CommRing A] [Algebra k A]
    (s : StandardGroupSchemes.affine k A ⟶ T.X),
    (StandardGroupSchemes.map k ((Algebra.ofId A (DualNumber A)).restrictScalars k) ≫
      s ≫ i.hom.hom) * scaledTangentPoint G A 1 v *
        (StandardGroupSchemes.map k ((Algebra.ofId A (DualNumber A)).restrictScalars k) ≫
          s ≫ i.hom.hom)⁻¹ =
      scaledTangentPoint G A (RhoSection.characterValue (s ≫ chi.hom.hom)) v}

end AlgebraicGeometry.AdjointCharacter
