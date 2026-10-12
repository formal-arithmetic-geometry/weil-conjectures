module
public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite intersection combines degreewise local representatives into one neighbourhood.
Source: lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2, expanding
lem-pc-perfect-locus (sk-thm-picard-perfect).

Proof: Let I be the finite set of integers in [a,b] intersected with [c,e]. For each
n in I choose the neighbourhood and representative supplied by hlocal. Let U be
the intersection of these finitely many neighbourhoods, taking U to be the whole
scheme if I is empty; y belongs to U. Restrict each chosen map along U -> U_n and
conjugate by the natural restriction-composition isomorphisms to obtain a map
between the original terms restricted to U. Pullback composition and naturality
of stalkRestrictionComplexIso carry the equation on U_n to the equation on U.
For n outside I, one original term is zero by its strict bound. Its restrictions
and pullbacks are zero, so use the zero map and uniqueness of a map from or to a
zero object to verify the equation. This proves existence for every degree on U.
No freeness hypothesis is needed once hlocal has supplied the local maps.
(blueprint: lem-pc-finite-free-stalk-degreewise-lift-core) -/
theorem exists_degreewise_of_stalk_local_core
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (y : Y)
    (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n)
    (hlocal : ∀ n : ℤ, ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U),
      ∀ n : ℤ, ∃ (g :
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
          ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
            ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n := by sorry
end AlgebraicGeometry.Scheme.Modules
