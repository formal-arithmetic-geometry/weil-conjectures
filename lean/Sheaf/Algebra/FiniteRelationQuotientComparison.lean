module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

/-- A lifted finite matrix presents a quotient whose scalar extension is the
quotient by the corresponding colimit matrix.

Source: Stacks Project, Algebra, Tag 05N7, proof of (1).
(blueprint: lem-pc-finite-relation-quotient-comparison).

Proof: put R = F.obj i, A = colimit F, and let R act on A through the
coprojection. The sequence R^m --qi--> R^n --> R^n / range qi --> 0 is
right exact by the definition of the quotient. Tensoring it with A over R
preserves right exactness, so its last term is the cokernel of A tensor qi.
For each finite free module the map a tensor x to (a * image(x_j))_j is an
A-linear equivalence, with inverse sending y to the sum of y_j tensor e_j.
Under these equivalences A tensor qi agrees with q: the coefficient hypothesis
identifies their values on each standard basis vector, hence on every vector
by linearity. Their cokernels are therefore A-linearly isomorphic. Finally,
ULift.down is a linear equivalence; its scalar extension and the inverse
ULift equivalence on the output transport this cokernel isomorphism to the
specified module universes. Empty bases have empty sums and give the same
argument for n = 0 or m = 0. No flatness is needed. -/
theorem finite_relation_quotient_comparison
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (n m : ℕ)
    (q : (Fin m → (colimit F : CommRingCat)) →ₗ[(colimit F : CommRingCat)]
      (Fin n → (colimit F : CommRingCat)))
    (i : I) (qi : (Fin m → F.obj i) →ₗ[F.obj i] (Fin n → F.obj i))
    (hcoeff : ∀ (j : Fin n) (k : Fin m),
      (colimit.ι F i).hom (qi (Pi.single k 1) j) = q (Pi.single k 1) j) :
    Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj
        (ModuleCat.of (F.obj i) (ULift.{v} ((Fin n → F.obj i) ⧸ LinearMap.range qi))) ≅
        ModuleCat.of (colimit F : CommRingCat)
          (ULift.{v} ((Fin n → (colimit F : CommRingCat)) ⧸ LinearMap.range q))) := by
  sorry

end ModuleCat
