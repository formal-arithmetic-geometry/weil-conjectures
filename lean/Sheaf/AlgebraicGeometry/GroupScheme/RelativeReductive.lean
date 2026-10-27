module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Reductivity over arbitrary schemes

Source: Conrad, Reductive group schemes, Definition 3.1.1, printed p.81
(blueprint: def-sfb-relative-reductive-group).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.GroupScheme

/-- A reductive group scheme is smooth affine of finite presentation with reductive
geometric fibres. The existing field predicate includes geometric connectedness
and absence of a nontrivial smooth connected normal unipotent subgroup.
Source: Conrad, Definition 3.1.1, printed p.81
(blueprint: def-sfb-relative-reductive-group). -/
def IsReductive {S : Scheme.{u}} (H : Grp (Over S)) : Prop :=
  Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ LocallyOfFinitePresentation H.X.hom ∧
    QuasiCompact H.X.hom ∧ QuasiSeparated H.X.hom ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
        ReductiveTorusCentralizer.IsReductive ((Over.pullback s).mapGrp.obj H)

end AlgebraicGeometry.GroupScheme
