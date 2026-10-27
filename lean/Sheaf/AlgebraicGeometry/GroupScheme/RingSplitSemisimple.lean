module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing

/-! # Split simply connected semisimple groups over rings

Source: Alper, Adequate moduli spaces, Section 9.7, pp.526--527.
(blueprint: def-sfb-ring-split-semisimple)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.RingSemisimple

/-- Geometric scalar extension, retaining the group-object diagrams.
Source: Alper, Section 9.7 (blueprint: def-sfb-ring-split-semisimple). -/
def geometricChange {R : Type u} [CommRing R] (F : Type u) [Field F] [Algebra R F] :
    Grp (Over (Spec (.of R))) ⥤ Grp (Over (Spec (.of F))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).mapGrp

/-- Simple connectedness excludes every nontrivial central isogeny onto the group,
including inseparable isogenies. Centrality is tested on every algebra's points.
Source: Alper, Lemma 9.7.2 (blueprint: def-sfb-ring-split-semisimple). -/
def IsSimplyConnected {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) : Prop :=
  ∀ (D : Over (Spec (.of F))) [GrpObj D], IsSemisimpleGroupScheme D →
    ∀ (f : D ⟶ G.X) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (C : Type u) [CommRing C] [Algebra F C]
        (x : StandardGroupSchemes.affine F C ⟶ GrpObj.ker f)
        (g : StandardGroupSchemes.affine F C ⟶ D),
        (x ≫ GrpObj.kerι f) * g = g * (x ≫ GrpObj.kerι f)) → IsIso f

/-- Semisimple simply connected geometric fibres and a split maximal torus in a Borel.
The inclusions over R are closed, and torus maximality and the Borel property are
required on every geometric fibre. Rank zero is allowed.
Source: Alper, Lemmas 9.7.2 and 9.7.4
(blueprint: def-sfb-ring-split-semisimple). -/
def IsSplitSemisimpleSimplyConnected {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (.of R)))) : Prop :=
  (∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra R F],
    IsSemisimpleGroupScheme ((geometricChange F).obj G).X ∧
      IsSimplyConnected ((geometricChange F).obj G)) ∧
  ∃ (T B : Grp (Over (Spec (.of R)))) (i : T ⟶ G) (j : B ⟶ G) (k : T ⟶ B),
    IsClosedImmersion i.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left ∧
    k ≫ j = i ∧ (∃ r : ℕ, Nonempty (T ≅ RingGroupSchemes.splitTorus R r)) ∧
    ∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra R F],
      ReductiveTorusCentralizer.IsMaximalTorus ((geometricChange F).map i) ∧
        IsBorelGroupScheme ((geometricChange F).map j).hom.hom

end AlgebraicGeometry.RingSemisimple
