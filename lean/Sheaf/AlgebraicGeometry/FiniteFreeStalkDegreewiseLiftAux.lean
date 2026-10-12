module
public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite intersection gluing for a finite set of degrees, with explicit outside witnesses.
Source: finite-free-stalk-chain-map-lift-local, finite intersection step.
The proof intersects the finitely many neighbourhoods and transports each representative
along restriction composition; outside the finite set the supplied witnesses are used.
(blueprint: lem-pc-finite-free-stalk-degreewise-lift-core-aux) -/
theorem exists_degreewise_finite_aux
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (y : Y) (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n)
    (I : Finset ℤ)
    (hlocal : ∀ n : ℤ, n ∈ I → ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n)
    (hout : ∀ n : ℤ, n ∉ I → ∃ (g :
      (((restrictFunctor (⊤ : Y.Opens).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor (⊤ : Y.Opens).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback ((⊤ : Y.Opens).fromSpecStalkOfMem y (by simp))).map g =
        ((stalkRestrictionComplexIso (⊤ : Y.Opens) y (by simp)).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso (⊤ : Y.Opens) y (by simp)).app Q).inv.f n) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∀ n : ℤ, ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n := by sorry
end AlgebraicGeometry.Scheme.Modules
