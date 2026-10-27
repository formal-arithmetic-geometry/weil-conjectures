module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces

/-! # Full character weights of conjugation over an arbitrary field

Source: Conrad, Reductive group schemes, Corollary 5.2.7(2), p.155, and the
character decomposition in Section 4.1 (blueprint: def-sfb-universal-conjugation-weight).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.UniversalConjugationWeight

/-- The scalar-extension map k[ε] → B[ε], sending ε to bε.
Source: Conrad, Section 4.1 (blueprint: def-sfb-universal-conjugation-weight). -/
def scalarDualMap {k : Type u} [Field k] (B : CommAlgCat.{u} k) (b : B) :
    DualNumber k →ₐ[k] DualNumber B :=
  DualNumber.lift ⟨(Algebra.ofId k (DualNumber B), TrivSqZeroExt.inr b),
    TrivSqZeroExt.inr_mul_inr B b b, fun _ ↦ Commute.all _ _⟩

/-- The full scheme-theoretic χ-weight space for conjugation by i(T).
The eigenvector identity is tested on every k-algebra, including nonreduced ones.
The span is the eigenspace itself because conjugation acts linearly on tangents.
Source: Conrad, Section 4.1 and Corollary 5.2.7(2), p.155
(blueprint: def-sfb-universal-conjugation-weight). -/
def weight {k : Type u} [Field k] {T G : Grp (Over (Spec (.of k)))}
    (i : T ⟶ G) (χ : RankOneRoots.Character T) : Submodule k (GrpObj.Lie G.X) :=
  Submodule.span k {v | ∀ (B : CommAlgCat.{u} k) (t : points T.X B),
    ((points.map T.X (TrivSqZeroExt.inlAlgHom k B B) t) ≫ i.hom.hom) *
        points.map G.X (scalarDualMap B 1) (GrpObj.tangentPoint v) *
          ((points.map T.X (TrivSqZeroExt.inlAlgHom k B B) t) ≫ i.hom.hom)⁻¹ =
      points.map G.X
        (scalarDualMap B (RankOneRoots.multiplicativeValue B (t ≫ χ.hom.hom)))
        (GrpObj.tangentPoint v)}

end AlgebraicGeometry.UniversalConjugationWeight
