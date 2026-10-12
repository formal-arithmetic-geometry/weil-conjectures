module
public import Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.Topology.PresheafModuleStalkFunctor
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Degreewise local representatives before taking a finite common intersection.
Source: lem-pc-finite-free-stalk-chain-map-lift-local, steps 1--2, expanding
lem-pc-perfect-locus (sk-thm-picard-perfect).

Proof: Fix a degree n. If either term is zero, restriction and pullback preserve
zero objects, so the unique zero map represents t n on the whole scheme. Otherwise
choose the two finite free isomorphisms in the hypotheses. Pullback preserves free
sheaves. On the affine scheme Spec O_{Y,y}, morphisms between these finite free
sheaves are finite matrices over O_{Y,y}, by the free universal property and the
identification of global functions on an affine spectrum with its ring. Each entry
is a germ of a structure-sheaf section near y. Intersect the finitely many entry
neighbourhoods and restrict these sections. Restrict the chosen free isomorphisms,
form the section matrix, and conjugate it to obtain g. The comparison is built from
restriction-as-pullback and pullback composition; its naturality identifies the
pulled-back matrix with the prescribed germ matrix. This gives the displayed
component equation. For a rank-zero term the matrix has no entries and the whole
scheme suffices. Repeat separately for each n; boundedness is unnecessary here.
(blueprint: lem-pc-finite-free-stalk-degreewise-local) -/
theorem exists_local_degreewise_of_stalk_local
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y)
    (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n) :
    ∀ n : ℤ, ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n := by sorry

end AlgebraicGeometry.Scheme.Modules
