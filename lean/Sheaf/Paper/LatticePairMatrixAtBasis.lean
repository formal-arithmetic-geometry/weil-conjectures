/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.LatticeSectionMatrix

/-!
# Continuous matrices for locally free integral lattice pairs

Source: Bhatt--Scholze, Proposition 6.8.4(6), local bases
(blueprint: lem-weil-pbc-lattice-pair-matrix-at-basis).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A specified finite local integral basis determines an invertible matrix in a
rational frame, with its embedded-image formula after arbitrary restriction.
Source: Bhatt--Scholze, Proposition 6.8.4(6), local integral bases
(blueprint: lem-weil-pbc-lattice-pair-matrix-at-basis).
Proof: the given basis of the integral module of P has finite rank r.
Its rationalization is free of rank r by the finite free scalar-extension isomorphism.
Compose that isomorphism with P's rationalization and the given rational frame.
At a point, evaluation of the two inverse linear maps gives inverse matrices over K,
so invariant basis number gives r = n when W is nonempty. If W is empty, all
coefficient rings and free-module section sets on its slice are singletons, and the
unique matrix and equality of the nonempty images suffice. Reindex the integral basis
by Fin n and let G
be its matrix of rational coordinate sections. The inverse sheaf isomorphism supplies
inverse coordinate sections, so G is invertible. A section is in the lattice precisely
when it is an integral linear combination of these basis columns. Naturality of both
frames gives the asserted formula on every further slice object. Rank zero uses the
unique empty matrix and the same free-module argument. -/
theorem integralLatticePair_matrixAtBasis (X : Scheme.{u})
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
    (U : X.ProEt) (n : ℕ) (e : L.over U ≅ latticeFreeSheaf X K U n)
    (V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V)
    (q : P.module.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (W : X.ProEt) (a : W ⟶ V) (t : Over.mk a ⟶ q.X i) :
    ∃ G : Matrix.GeneralLinearGroup (Fin n)
        ((latticeCoefficientSheaf X K).obj.obj (op W)),
      ∀ T : Over W,
        Set.image (e.hom.val.app (op (Over.mk (T.hom ≫ a ≫ f))))
          (P.image (op (Over.mk (T.hom ≫ a)))) =
        sectionMatrixLatticeImage X K A U n (op (Over.mk (T.hom ≫ a ≫ f)))
          (Matrix.GeneralLinearGroup.map
            (((latticeCoefficientSheaf X K).obj.map T.hom.op).hom) G) := by
  sorry

end AlgebraicGeometry.ProEtale
