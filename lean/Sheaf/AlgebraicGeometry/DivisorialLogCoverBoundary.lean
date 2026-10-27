module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor

/-!
# Divisorial presentations and deletion of boundary components

Source: ILO VI 1.4; VIII 5.3.8, printed p.125, last paragraph
(blueprint: def-per-divisorial-log-cover-boundary).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Identify the actual log sheaf with the prescribed divisorial functions, over the
structural inclusion into regular functions. This excludes an unrelated log structure
having only the same support. Source: ILO VI 1.4
(blueprint: def-per-divisorial-log-cover-boundary). -/
def EtaleLogStructure.IsDivisorialFor {X : Scheme.{u}} (M : EtaleLogStructure X)
    (U : X.Opens) : Prop :=
  ∃ e : M.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι,
    e.hom ≫ divisorialStructuralMap U.ι = M.alpha

/-- A reduced union of selected global irreducible components. The selected set can
be empty; self-intersecting global components are not split or required regular.
Source: ILO VIII 5.3.8 (blueprint: def-per-divisorial-log-cover-boundary). -/
def Scheme.IdealSheafData.IsReducedComponentUnion {X : Scheme.{u}}
    (D B : X.IdealSheafData) : Prop :=
  D.radical = D ∧ ∃ S : Set (Set B.subscheme),
    S ⊆ irreducibleComponents B.subscheme ∧
      (D.support : Set X) = ⋃ C ∈ S, B.subschemeι '' C

end AlgebraicGeometry
