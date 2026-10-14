/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Degree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.AlgebraicGeometry.Picard.Defs
import WeilConjectures.AlgebraicGeometry.Picard.RationalPoint

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The existence part of fpqc descent for the fppf sheafification of a fixed fibrewise-degree
subfunctor. It is the gluing step for compatible degree-`d` Picard classes over an fpqc sieve.
To prove it, choose a closed point of the smooth geometrically integral curve with finite
separable residue field and base change to that field. The resulting rational point identifies
the relative Picard sheaf with normalized invertible modules. Trivialize each local class along
the section and normalize the transition maps on overlaps; the global-units property makes each
normalized transition unique, so the cocycle equation holds. Fpqc descent of invertible modules
and their morphisms then glues the normalized local classes. Fibrewise degree is preserved by
residue-field extension and is jointly local, so the glued class has degree `d`. Finally descend
the glued class and its compatibility from the finite separable extension by fppf descent, which
is an fpqc cover, obtaining the required amalgamation over the original sieve. Source: Stacks
Project, Tags 0D28, 0D2B and 023T.
(blueprint: lem-pd-degree-picard-sheaf-fpqc-existence) -/
theorem exists_amalgamation_fpqc_sheafify_picardDegree
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (d : ℤ) (S : Subfunctor (picardPresheaf f))
    (hS : ∀ (T : Over (Spec (.of k))) (L : (picardPresheaf f).obj (op T)),
      L ∈ S.obj (op T) ↔ ∀ t, picardPresheafDegree f L t = d)
    {T : Over (Spec (.of k))} (R : Sieve T)
    (hR : R ∈ (Scheme.fpqcTopology.over (Spec (.of k))) T)
    (x : Presieve.FamilyOfElements
      ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
        S.toFunctor).obj R.arrows)
    (hx : x.Compatible) :
    ∃ t, x.IsAmalgamation t := by sorry

end AlgebraicGeometry
