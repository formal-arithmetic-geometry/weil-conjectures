module
public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Positive-rank finite-free stalk maps admit local representatives.
Source: lem-pc-perfect-locus, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2.
Proof: Identify the pulled-back free sheaves with free sheaves on Spec O_{Y,y}.
The free universal property and the identification of global functions on this
spectrum with O_{Y,y} identify t with a finite matrix of stalk elements. Choose
a structure-sheaf section representing each entry on a neighbourhood of y.
Intersect these finitely many neighbourhoods and restrict all representatives
to the intersection U. Identify the restricted free sheaves with free sheaves
on U and use these sections as matrix entries to construct g. Under the free
pullback isomorphisms, pulling back g gives the matrix of the chosen germs,
which is the matrix of t. Naturality of restriction-as-pullback, pullback
composition, and pullbackCongr identifies this matrix equality with
(Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
E.hom.app _ ≫ t ≫ E.inv.app _.
(blueprint: lem-pc-finite-free-stalk-map-local-positive) -/
theorem exists_local_free_stalk_map_of_nonempty
    {Y : Scheme.{u}} (r s : ℕ) (y : Y)
    (hr : Nonempty (Fin r)) (hs : Nonempty (Fin s))
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
