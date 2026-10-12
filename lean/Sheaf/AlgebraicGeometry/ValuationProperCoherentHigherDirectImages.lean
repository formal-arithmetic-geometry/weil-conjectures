module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.LeraySpectralSequence
import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.RingTheory.CoherentRingPerfectComplexCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-! # Cohomology of a finite locally free module over a valuation ring

Source: literature/stacks-project/more-on-morphisms.tex, Tag 0EX8
(blueprint: lem-sc-valuation-proper-coherent-higher-direct-images).
-/

/-- For a valuation ring `A`, a proper, flat morphism `f : X ⟶ Spec A` of finite presentation
and an `O_X`-module `F` locally free of constant finite rank `d`, every cohomology module
`H^q(X, F)` (`RingedSpace.moduleCohomology`) is a finitely presented `A`-module, the
`A`-module structure being restriction of scalars along `A ≅ Γ(Spec A) → Γ(X, O_X)`.
Source: More on Morphisms, Tag 0EX8
(blueprint: lem-sc-valuation-proper-coherent-higher-direct-images).

Proof:
1. A finite affine trivializing cover shows `F` is finitely presented, and flat over `A`
   since `f` is flat; so `E := Rf_*F` is perfect on `Spec A` (lem-pc-rf-perfect-base-change).
2. `A` is a coherent ring (finitely generated ideals of a valuation ring are principal, hence
   free). As `A` is local, `E` is strictly perfect on `Spec A`, `E ≅ P^•~` for a bounded
   complex of finite projective `A`-modules (def-pc-perfect-complex), and
   `R^q f_* F ≅ H^q(P^•)~` (def-pc-derived-direct-image) has finitely presented sections
   (lem-sc-coherent-ring-perfect-complex-cohomology).
3. The Leray spectral sequence (pqf-lem-leray) degenerates on the affine base by
   lem-pc-affine-vanishing, so `H^q(X, F) ≅ Γ(Spec A, R^q f_* F) = H^q(P^•)`. -/
theorem finitePresentation_moduleCohomology_of_valuationRing
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (d : ℕ) (F : X.Modules) [F.IsFiniteLocallyFreeOfRank d] (q : ℕ) :
    Module.FinitePresentation A
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
