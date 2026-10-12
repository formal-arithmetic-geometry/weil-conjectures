module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section
universe u
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- Local coordinate decompositions identify the leading determinant with the
restriction of the selected minor, and that restriction is a unit.

Source: `thm-pc-semicontinuity-base-change`, proof (3), pivot-minor step;
see the source argument retained in `exists_local_invertible_minor_block`.
(blueprint: lem-pc-local-invertible-minor-block-data)

Proof: Write A for the matrix in the given bases and delta for the selected
minor's determinant. Take V to be the intersection of D(delta) with the image
of j, and U its preimage in Z. The point z is in U. On V every germ of delta
is a unit; the germwise inverses glue uniquely to an inverse section, so its
restriction to U is a unit. The selected rows and columns are injective:
otherwise the determinant is zero by the repeated-row/column determinant
identity, contradicting its unit germ at j(z). Thus a is at most m and n.
Extend the selected lists to permutations by enumerating their complements,
which have cardinalities m-a and n-a. Pull back the given bases, restrict them
to U, and use these permutations and the free sum decomposition to obtain eS
and eT. Their leading matrix has entries A(rows i, cols k) restricted along
U.ι followed by j, after the ULift reindexing. Determinants commute with ring
homomorphisms and simultaneous reindexing, giving the asserted equality.
For a=0 the lists are empty and both determinants are 1; the same construction
uses the original full bases for the complementary factors. No inverse
sheaf morphism is asserted here. -/
theorem exists_local_invertible_minor_block_data
    {Y Z : Scheme.{u}} {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (z : Z)
    (rows : Fin a → ULift.{u} (Fin n)) (cols : Fin a → ULift.{u} (Fin m))
    (hminor : j.base z ∈
      Y.basicOpen ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det) :
    ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        (freeMatrix (X := U.toScheme) (I := ULift.{u} (Fin a))
          (J := ULift.{u} (Fin a)) (biprod.inl ≫ eS.inv ≫
          (restrictFunctor U.ι).map ((Modules.pullback j).map φ) ≫
          eT.hom ≫ biprod.fst)).det =
            (U.ι ≫ j).appTop
              ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det ∧
        IsUnit ((U.ι ≫ j).appTop
          ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
