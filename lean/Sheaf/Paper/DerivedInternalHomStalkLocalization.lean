module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.Algebra.Homology.DerivedHomProjectiveResolution
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.CoherentAffineFreeResolution
import Sheaf.Paper.DerivedInternalHomRestrictOpen

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Stalk localization for derived internal Hom of a coherent sheaf.

Source: Stacks Project, Cohomology, Lemma 0GM8 (label lemma-stalk-internal-hom),
case (2) (blueprint: lem-sc-derived-internal-hom-stalk-localization).

Proof:
1. The assertion is local at `x`; restriction to an affine Noetherian neighbourhood
   commutes with derived internal Hom, cohomology, and stalks
   (lem-sc-derived-internal-hom-restrict-open).
2. On the affine neighbourhood, coherence gives a bounded-above finite-free
   resolution of `F` (lem-sc-coherent-affine-free-resolution).
3. The bounded-above finite-free Hom model computes the derived internal Hom
   (lem-sc-derived-hom-finite-free-model), and finite freeness identifies its stalk
   with the Hom complex of the stalk resolution.
4. Exactness of stalks preserves the resolution (lem-weil-pbc-module-stalk-exact);
   the projective-resolution calculation identifies this complex with the derived
   internal Hom on the one-point ringed site (lem-sc-derived-hom-projective-resolution).
5. Applying the degree-`i` cohomology functor gives the canonical local
   identification, for every integer `i`; the one-point cohomology object is
   evaluated as a module over `O_{X,x}`; both sides are `O_{X,x}`-modules and the
   identification is `O_{X,x}`-linear.
-/
theorem derivedInternalHom_stalk_localization
    (X : Scheme.{u}) [CompactSpace X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (x : X) (i : ℤ)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf
            (X.toRingedSpace.presheaf.stalk x))))] :
    Nonempty
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
            ((CategoryTheory.derivedInternalHom
              (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj
              (op ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F),
               (DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G))) ≃ₗ[
        X.presheaf.stalk x]
      (SheafOfModules.evaluation
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf
            (X.toRingedSpace.presheaf.stalk x)))
        (Opposite.op (Discrete.mk PUnit.unit))).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf
                (X.toRingedSpace.presheaf.stalk x)))) i).obj
          ((CategoryTheory.derivedInternalHom ⊥
              (CochainComplex.onePointRingSheaf
                (X.toRingedSpace.presheaf.stalk x))).obj
            (op ((DerivedCategory.singleFunctor _ 0).obj
              ⟨(PresheafOfModules.constFunctor
                  {pt := RingCat.of (X.toRingedSpace.presheaf.stalk x), ι := 𝟙 _}).obj
                ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F),
               Presheaf.isSheaf_bot _⟩),
             (DerivedCategory.singleFunctor _ 0).obj
              ⟨(PresheafOfModules.constFunctor
                  {pt := RingCat.of (X.toRingedSpace.presheaf.stalk x), ι := 𝟙 _}).obj
                ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G),
               Presheaf.isSheaf_bot _⟩)))) := by
  sorry

end AlgebraicGeometry
