module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus

/-! # Geometric fibre conditions for reductive and split simply connected groups

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Theorem 9.7.5, printed p.527, and the split-group convention preceding Lemma 9.7.2.
(blueprint: def-sfb-relative-reductive-conditions)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped MonObj

namespace AlgebraicGeometry.RelativeReductive

/-- Reductive geometric fibres, using the recorded field-level definition.
Source: Alper, Theorem 9.7.5, p.527.
(blueprint: def-sfb-relative-reductive-conditions) -/
def HasReductiveFibres {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F] (s : Spec (.of F) ⟶ S),
    ReductiveTorusCentralizer.IsReductive ((Over.pullback s).mapGrp.obj G)

/-- Every geometric fibre is semisimple and every central isogeny onto it is an
isomorphism. Centrality is tested on all schemes, retaining nonreduced finite kernels.
Source: Alper, Theorem 9.7.5, p.527, simply connected covering reduction.
(blueprint: def-sfb-relative-reductive-conditions) -/
def HasSimplyConnectedSemisimpleFibres {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F] (s : Spec (.of F) ⟶ S),
    IsSemisimpleGroupScheme ((Over.pullback s).mapGrp.obj G).X ∧
    ∀ (H : Over (Spec (.of F))) [GrpObj H], IsSemisimpleGroupScheme H →
      ∀ (f : H ⟶ ((Over.pullback s).mapGrp.obj G).X) [IsMonHom f],
        Surjective f.left → IsFinite (GrpObj.ker f).hom →
        (∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker f) (h : T ⟶ H),
          (x ≫ GrpObj.kerι f) * h = h * (x ≫ GrpObj.kerι f)) → IsIso f

/-- A split maximal torus and a Borel containing it. The inclusions are closed subgroup
schemes, smooth over S; maximality and the Borel condition are tested on every geometric
fibre. The actual split torus is the recorded product of copies of G_m, including rank 0.
Source: Alper, convention before Lemma 9.7.2, p.526, and Theorem 9.7.5, p.527.
(blueprint: def-sfb-relative-reductive-conditions) -/
def HasSplitBorelPair {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  ∃ (r : ℕ) (B : Grp (Over S)) (iT : relativeSplitTorus S r ⟶ G)
    (iB : B ⟶ G) (j : relativeSplitTorus S r ⟶ B),
    j ≫ iB = iT ∧ IsClosedImmersion iT.hom.hom.left ∧
    IsClosedImmersion iB.hom.hom.left ∧ Smooth B.X.hom ∧
    ∀ (F : Type u) [Field F] [IsAlgClosed F] (s : Spec (.of F) ⟶ S),
      ReductiveTorusCentralizer.IsMaximalTorus ((Over.pullback s).mapGrp.map iT) ∧
      IsBorelGroupScheme ((Over.pullback s).mapGrp.map iB).hom.hom

end AlgebraicGeometry.RelativeReductive
