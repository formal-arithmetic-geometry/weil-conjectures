/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.EtaleModuleAffineBound
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage

/-!
# Uniform affine evaluation bound for classical pro-etale module sheaves

Source: current Weil conjectures blueprint, Fixed-degree truncation paragraph of
`sk-prop-pe-unbounded-classical-unit.proof.md`; Stacks Project, Tags 099W and 03F3
(blueprint: lem-sfb-classical-module-affine-evaluation-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Evaluation at a pro-etale object as an ordinary module over the coefficient ring.
The scalar map is the sheafification unit on the constant ring presheaf, composed with
inverse universe lift. Thus its value on `a` is precisely the constant section `a`.
Source: the definition of E_W in the affine evaluation bound, and Stacks Tag 03F3
(blueprint: lem-sfb-classical-module-affine-evaluation-bound). -/
noncomputable abbrev proEtaleConstantModuleEvaluation
    (X : Scheme.{u}) (A : Type u) [CommRing A] (W : X.ProEt) :
    ringedSiteModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A))) ⥤ ModuleCat.{u + 1} A :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op W) ⋙
    ModuleCat.restrictScalars
      (((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))).app
          (op W)).hom.comp ULift.ringEquiv.symm.toRingHom)

/-- Every classical module sheaf has vanishing evaluation cohomology above `2 dim X + 1`,
uniformly over affine etale objects. Dimension of the empty scheme is assigned zero.
The conclusion is stated for every injective module resolution and takes cohomology
only after applying the A-linear evaluation functor. Since q is greater than the
nonnegative bound, q.toNat represents exactly that integer degree.

Source: current blueprint, Fixed-degree truncation paragraph of
`sk-prop-pe-unbounded-classical-unit.proof.md`; Stacks Tags 099W and 03F3
(blueprint: lem-sfb-classical-module-affine-evaluation-bound).

Proof:
1. By lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives,
the module categories have injective resolutions in the common larger universe.
By det-pe-classical-sheaves-modules, descend H to an etale module sheaf G.
No finite generation or constructibility is used.
2. By lem-weil-pbc-etale-inverse-image-restriction and
lem-pe-constant-left-module-inverse-image, etale inverse image on W is the ordinary
restriction, with the same A-action. Apply lem-sfb-etale-module-affine-bound to G;
its hypotheses and its dimension convention are exactly those here.
3. Apply the affine formula of sk-prop-sf-comparison to G[0] and the constant
one-object affine etale presentation of W. This is a bounded-below input, so the
comparison does not invoke unbounded comparison. By
lem-weil-pbc-right-derived-plus-injective, derived sections are computed by evaluating
injective module resolutions. Taking degree q gives vanishing on W_proet.
4. By lem-weil-pbc-proetale-restriction-injectives, restriction to W is exact and
preserves injectives. Its evaluated resolution at the final object has the terms
I^n(W), the same differentials and the same constant A-action. Thus it is the complex
in the conclusion. The same bound works for every W and every classical H. -/
theorem classical_module_affine_evaluation_bound
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) (_hℓ : ℓ.Prime) (_hℓk : IsUnit (ℓ : k))
    (A : Type u) [CommRing A] [Finite A]
    (a : ℕ) (_ha : 1 ≤ a) (_hA : (ℓ : A) ^ a = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (W : X.Etale) [IsAffine W.left]
    (H : ringedSiteModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} A))))
    (_hH : IsClassicalModuleSheaf H) (I : InjectiveResolution H)
    (q : ℤ)
    (_hq : (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 : ℕ) < q) :
    IsZero ((((proEtaleConstantModuleEvaluation X A (Scheme.ProEt.mk W.hom)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology q.toNat) := by
  sorry

end AlgebraicGeometry.ProEtale
