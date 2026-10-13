/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces
public import Sheaf.AlgebraicGeometry.GradedSheafStructures

/-! # The associated graded ideal algebra

Source: Stacks Project, Cohomology of Schemes, Lemma 087Z.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The associated graded ideal pieces carry the multiplication induced by representatives.
Source: Stacks Project, Lemma 087Z and Section 0EHN,
https://stacks.math.columbia.edu/tag/087Z.
(blueprint: lem-weil-pbc-formal-associated-graded-algebra-exists).

Proof: On affine opens the ideal-power range formula identifies the inclusion of I^r
with I(U)^r; the quotient projection identifies B_r with I(U)^r/I(U)^(r+1).
Multiplication sends I(U)^m times I(U)^n into I(U)^(m+n). Changing either representative
changes the result by I(U)^(m+n+1), so it descends to a bilinear multiplication of the
quotients. For r=0 the power inclusion is the identity, and its quotient projection is
the unit. On smaller affine opens these maps commute with restrictions because the
inclusions and quotient projections do. The affine basis sheaf condition therefore
glues the maps to all opens: lift both quotient sections locally, multiply their
representatives, and glue the independent results. The unit and algebra laws are
checked after further local lifting of all the sections involved, where they are the
ring identities 1a=a, a1=a, (ab)c=a(bc), and ab=ba. The degree identifications give the
required HEq laws. For actual sections a and b of power ideals on any open, their
products locally lift uniquely through the monic inclusion of I^(m+n). Uniqueness
makes these lifts glue to the section c, and the constructed multiplication gives its
quotient class. This includes the empty open, the zero and unit ideals, and degree zero.
No finite-generation assertion or formal module is used. -/
theorem formalAssociatedGraded_algebra_exists {X : Scheme.{u}}
    (I : X.IdealSheafData) :
    ∃ A : GradedSheafAlgebra (formalAssociatedGradedPiece I),
      A.unit = formalAssociatedGradedπ I 0 ∧
      (∀ (m n : ℕ) (U : X.Opens)
        (a : (Scheme.idealSheafPower I.toModulesι m).1.val.obj (op U))
        (b : (Scheme.idealSheafPower I.toModulesι n).1.val.obj (op U)),
        ∃ c : (Scheme.idealSheafPower I.toModulesι (m + n)).1.val.obj (op U),
          (Scheme.idealSheafPower I.toModulesι (m + n)).2.val.app (op U) c =
            (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι m).2.val.app (op U) a)) *
              (@id Γ(X, U) ((Scheme.idealSheafPower I.toModulesι n).2.val.app (op U) b)) ∧
          A.mul m n U ((formalAssociatedGradedπ I m).val.app (op U) a)
            ((formalAssociatedGradedπ I n).val.app (op U) b) =
              (formalAssociatedGradedπ I (m + n)).val.app (op U) c) := by sorry

end AlgebraicGeometry
