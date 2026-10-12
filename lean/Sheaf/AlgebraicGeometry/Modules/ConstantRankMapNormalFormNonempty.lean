module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import Sheaf.LinearAlgebra.MatrixRankFieldExtension

@[expose] public section

universe u
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- The local normal form in the nonempty open-subscheme case.

Source: `thm-pc-semicontinuity-base-change`, proof (3), normal-form claim.
(blueprint: lem-pc-constant-rank-map-local-normal-form-nonempty)

Proof: Work around an arbitrary point of `Z` on an affine open.  The residue-field
ranks are all `a` by invariance under the field extensions supplied by `hrank`.
The `(a+1)`-minors therefore lie in every prime and vanish in the reduced affine
ring.  A nonzero `a`-minor at the point remains invertible after shrinking to its
principal open.  Row and column permutations and elementary invertible block
operations then give `diag (I a, 0)`: the Schur-complement entries are the
vanishing `(a+1)`-minors divided by the invertible pivot determinant.  Reordering
the resulting bases yields the displayed biproduct factorization.  The case
`a = 0` uses the empty minor, and the pointwise conclusion is assembled for each
point of the nonempty open subscheme. -/
 theorem exists_local_normal_form_of_constantRank_nonempty
    {Y Z : Scheme.{u}} [IsReduced Y] [Nonempty Z] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank = a) :
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin (m - a))) ⊞ free (ULift.{u} (Fin a)))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
          eS.hom ≫ biprod.snd ≫ biprod.inl ≫ eT.inv := by sorry

end AlgebraicGeometry.Scheme.Modules
