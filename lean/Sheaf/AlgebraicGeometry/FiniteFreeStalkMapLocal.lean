module
public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- A map between canonical finite free sheaves over a stalk extends locally.
Source: lem-pc-perfect-locus, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2.

Proof: Pullback identifies each displayed free sheaf with the free sheaf of the
same rank on Spec O_{Y,y}. The free universal property identifies a morphism
between them with a finite matrix of global functions. Global functions on
Spec O_{Y,y} are O_{Y,y}; hence each coefficient is a germ of a structure-sheaf
section. Choose a section representing each coefficient and intersect their
finitely many neighbourhoods of y. Restrict the sections to that intersection.
Use the free universal property on the restricted free sheaves to form the
matrix morphism g. Restriction-as-pullback, pullback composition and the equality
U.fromSpecStalkOfMem y hyU ≫ U.ι = Y.fromSpecStalk y give the displayed comparison
E. Their naturality, and the fact that the chosen sections have the prescribed
germs, identify the pullback of g with E.hom ; t ; E.inv. If either rank is zero,
there are no matrix entries and the zero morphism on Y suffices.
(blueprint: lem-pc-finite-free-stalk-map-local) -/
theorem exists_local_free_stalk_map
    {Y : Scheme.{u}} (r s : ℕ) (y : Y)
    (t : (Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      (Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s)))) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s)))),
      let E := Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι)
          (Modules.pullback (U.fromSpecStalkOfMem y hyU)) ≪≫
        pullbackComp (U.fromSpecStalkOfMem y hyU) U.ι ≪≫
        pullbackCongr (U.fromSpecStalkOfMem_ι y hyU)
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        E.hom.app _ ≫ t ≫ E.inv.app _ := by sorry
end AlgebraicGeometry.Scheme.Modules
