module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Residual calculation for explicit open base-change comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Compatibility of the pinned base-change arrow with the explicitly constructed
open comparisons. All comparison data are already constructed; this statement
is only the remaining mate calculation, with no existence claim.
Source: Stacks Project, cohomology.tex, Tags 08HY and 08FE; perfect.tex,
Tag 0DJ9, first paragraph.
(blueprint: lem-pc-n3-open-base-change-calculation).

Proof: Work on K-flat representatives for pullback and K-injective representatives
for direct image. Open restriction preserves K-injectives (Tag 08BS). The
underived direct-image comparison in singleComplexOpenDirectImageIso is the
sectionwise identity on inverse-image opens. It therefore identifies restriction
of the tensor-pullback adjunction counit with the restricted counit. The derived
comparison has the same equation by the factorization identities of
rightDerivedFunctorCompMapDerivedCategoryIso, rightDerivedFunctorNatIso,
rightDerivedFunctorCompIso and rightDerivedFunctorIsoMapDerivedCategory.
The adjunctions in schemeDerivedBaseChangeMap are pinned to the underived
adjunctions and the same derived counits, so this equation descends to their
counits. Explicitly, write L₀=L(f|V)*, R_X=restriction to U and
R_S=restriction to V. If c_f:L₀ R_S ≅ R_X Lf* is the comparison formed
from open pullback and the composition comparisons, and b_f is the constructed
direct-image comparison, the equation is
L₀(b_f.hom.app E) ≫ ε_f₀.app(R_X E) = c_f.hom.app(Rf*E) ≫ R_X(ε_f.app E).
Both sides are evaluation of the same restricted tensor-pullback counit on the
representatives. Apply the same equation for f'. Transpose both sides of the
claimed identity under the pinned adjunction for f' restricted to V'.
Tag 08HY identifies each transpose as pullback of the counit. Substitute the
restriction-counit equation and the explicit source comparison. Associativity
of the pinned pullback composition comparisons, the restricted square equation,
and hj identify the two pullback paths. Cancel inverse comparison factors.
The remaining factors are exactly singleComplexRestrictedCoefficient with
identity coefficient: inverse open pullback on X, composition along j and U.ι,
hj, inverse composition along U'.ι and g', and open pullback on X'. Transposing
back gives the equality. Every operation is a natural transformation identity,
so the proof also applies to zero coefficients, empty opens and unbounded
complexes. -/
theorem singleComplexOpen_baseChange_calculation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let δ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K) =
      (singleComplexOpenBaseChangeSourceIso f g K V V' hV').hom ≫
        schemeDerivedBaseChangeMap
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w K₀ ≫
        (schemeDerivedDirectImage (f' ∣_ V')).map δ ≫
        (singleComplexOpenDirectImageIso f' V').inv.app ((derivedPullback g').obj K)
    := by sorry

end AlgebraicGeometry
