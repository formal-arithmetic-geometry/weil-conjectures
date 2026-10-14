module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The union direct image admits a bounded-above complex representative.
Source: Stacks Project, Tags 08BV and 0DJ9, relative Mayer--Vietoris.
(blueprint: new-pc-standard-single-flat-counit-union-bounded-model).
Proof: Restrict N to U, V and U∩V inside U∪V. Open restriction preserves
quasi-coherence and relative flatness, so hPU, hPV and hPUV provide bounded
complex representatives of their direct images on B. Write their upper
bounds as bU, bV and bUV; their cohomology vanishes above these bounds.
Choose a termwise injective K-injective representative of N[0] on U∪V.
Apply the K-injective Mayer--Vietoris presentation to this two-open cover.
Its short exact sequence gives a distinguished triangle; apply derived
direct image to B and identify the other terms with the three restricted
direct images using composition of derived direct images. The long exact
cohomology sequence forces the union direct image to vanish above
b = max (max bU bV) (bUV + 1). Choose a complex representative L of that
object. Its good truncation at b has zero terms above b, and the inclusion
into L is a quasi-isomorphism because the cohomology above b vanishes.
Localizing this inclusion gives the required isomorphism. This argument
uses sheaf-module Mayer--Vietoris and needs no compactness of the opens;
empty or repeated opens and N=0 are included. -/
theorem exists_boundedAbove_union_model
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard A.Modules
    letI := HasDerivedCategory.standard B.Modules
    ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      Nonempty (((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
  sorry

end AlgebraicGeometry
