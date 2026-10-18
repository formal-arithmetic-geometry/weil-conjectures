/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-!
# The uniform affine étale bound for ordinary finite-coefficient module sheaves

Source: blueprint, `sk-prop-pe-unbounded-classical-unit.proof.md`, Fixed-degree truncation;
Stacks Project, Tags 099W and 03FD (blueprint: lem-sfb-etale-module-affine-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Higher cohomology of any constant-ring module sheaf on an affine étale object vanishes
above the uniform bound `2 * d_X + 1`. The module inverse image is expressed using the
canonical constant-scalar restriction and extension equivalence around `Etale.upperStar`.
The conclusion evaluates an arbitrary injective resolution of that module inverse image
at the terminal étale object of W and takes its cohomology. Integer degrees above the
positive bound are nonnegative, so `q.toNat` retains precisely the stated degree.

Source: blueprint, `sk-prop-pe-unbounded-classical-unit.proof.md`, Fixed-degree truncation;
Stacks Project, Tags 099W and 03FD (blueprint: lem-sfb-etale-module-affine-bound).

Proof (the six steps of the node):
1. Put N = ℓ^a. The scalar N * 1 is zero, so N kills every section of the underlying
abelian sheaf of G. It is torsion, with no finiteness requirement on its sections.
2. By `det-pe-morphisms-etale-comparison`, w is weakly étale. The one-object constant
presentation of the affine scheme W is a pro-étale affine presentation over X in the
sense of `sk-def-pe-morphisms`; its only transition is the affine identity.
3. Apply `det-pe-unbounded-classical-bounds` (1) with Y = X and g = identity. It gives
vanishing on W's pro-étale site above exactly the displayed bound, including empty X.
4. `lem-weil-pbc-comparison-pullback` identifies the two pulled-back coefficients.
`lem-cbc-abelian-etale-proetale-cohomology-comparison` (Stacks 099W) transfers the
vanishing to abelian cohomology on W's étale site. The positive bound ensures q ≥ 0.
5. `lem-pe-constant-left-module-inverse-image` identifies the underlying abelian sheaf
of module inverse image with the abelian inverse image. In this statement the canonical
constant-ring module equivalence realizes that same ordinary inverse image explicitly.
6. `lem-weil-pbc-module-sheaves-enough-injectives` supplies injective resolutions.
Apply `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` (Stacks 03FD) at
W's terminal object to the chosen module injective resolution. Its evaluated cohomology
has zero underlying abelian group, hence is a zero module. No flatness, constructibility,
finite generation, or injectivity after forgetting scalars is needed. -/
theorem etaleModule_affine_cohomology_isZero
    {k : Type u} [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (a : ℕ) (ha : 1 ≤ a) (hA : (ℓ : A) ^ a = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (W : X.Etale) [IsAffine W.left]
    (G : ringedSiteModules.{u + 1} (Scheme.etaleConstantModuleRing X A))
    (q : ℤ) (hq : (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 : ℕ) < q)
    (I : InjectiveResolution
      ((Scheme.etaleConstantModuleFunctor W.left A).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj
          ((Scheme.etaleConstantModuleRestrictionFunctor X A).obj G)))) :
    IsZero ((((SheafOfModules.evaluation
      (Scheme.etaleConstantModuleRing W.left A)
      (op (Scheme.Etale.mk (𝟙 W.left)))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q.toNat) := by
  sorry

end AlgebraicGeometry
