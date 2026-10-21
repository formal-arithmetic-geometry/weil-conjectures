/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.NatTrans
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.Paper.ContinuousCoefficientRealizations

/-!
# Pullback of continuous integral lattices

Source: blueprint main-20261015, six-functors basics, `sk-lem-stratified-lattice`,
proof, "Pushing down by the trace", restriction to a finite etale stratum;
Stacks Project, Modules on Sites, Tags 03D2 and 03EL
(blueprint: lem-sfb-lattice-pullback).

## Main definitions

- `latticePullbackScalarUnit`: the actual section `1 tensor m` in sheafified scalar extension.
- `continuousLatticePullbackSection`: the unit section of canonical coefficient pullback.

## Main statements

- `lattice_pullback`: the uniquely normalized pulled inclusion is monic, its source and
  target are locally finite free, and its own scalar-extension adjoint is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- Insertion into the existing scalar extension: apply its sheafification unit to `1 tensor m`.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sfb-lattice-pullback). -/
noncomputable def latticePullbackScalarUnit {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (V : X.ProEt) (m : M.val.obj (op V)) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M)).app (op V)
          ((1 : S.obj.obj (op V)) ⊗ₜ[R.obj.obj (op V), (a.hom.app (op V)).hom] m)

/-- The canonical pullback-unit section is inverse image of the section followed by insertion
into scalar extension along the adjunct of precomposition of continuous coefficient functions.
Source: Stacks Project, Tags 03D2 and 09A5; blueprint `sk-lem-stratified-lattice`,
"Pushing down by the trace" (blueprint: lem-sfb-lattice-pullback). -/
noncomputable def continuousLatticePullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (M : ringedSiteModules.{u + 1} (latticeModuleRing X T))
    (V : X.ProEt) (m : M.val.obj (op V)) :
    (continuousModulePullback g T M).val.obj (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  latticePullbackScalarUnit (continuousCoefficientInverseImageMap g T)
    ((Scheme.proEtaleModuleInverseImage g (latticeCoefficientSheaf X T)).obj M)
    ((Scheme.proEtaleBaseChange g).obj V)
    (ProEtaleTensorComparison.inverseSection g M V m)

/-- A lattice inclusion survives arbitrary scheme pullback, including its actual rationalization.
The hypothesis describes the scalar-extension adjoint by its defining unit formula. The
conclusion specifies the unique pulled inclusion on canonical inverse-image unit sections;
the final unit formula makes the rationalization the adjoint of this very inclusion.
`WithAbs` equips the field with its recorded extending absolute value, and
`latticeCoefficientIntegers` equips its valuation subring with the induced topology.

Source: blueprint main-20261015, `sk-lem-stratified-lattice`, proof,
"Pushing down by the trace", restriction of the universal lattice to each stratum;
Stacks Project, Modules on Sites, Tag 03EL (blueprint: lem-sfb-lattice-pullback).

Proof plan:
1. Put F = g inverse image, R = F(A_X), S = F(E_X). The continuous coefficient maps
   alpha_A and alpha_E are isomorphisms: compare the canonical continuous realizations
   of lem-weil-pbc-continuous-coefficient-realizations with lem-sfb-alpha-iso. Both
   adjuncts are precomposition with Y[K] -> X[K] -> K. Transport the naturality square
   lem-sfb-coefficient-pullback-square along these realizations. Scalar extension along
   alpha_A and alpha_E identifies both canonical coefficient pullbacks with F(M), F(L),
   and the normalized pulled inclusion becomes exactly F(i).
2. Forgetting module actions detects the sectionwise kernel. Exactness on abelian sheaves
   in det-pe-topos-functoriality-inverse-image makes F(i), hence the specified inclusion,
   monic. Its formula on unit sections determines it uniquely by inverse image and tensor.
3. Base change a pro-etale trivializing cover, using covering preservation in that node.
   Clause (1) of lem-sfb-proetale-object-inverse-image-restriction identifies restriction
   with inverse image. Composition and preservation of finite products pull each local
   finite basis to a basis over A_Y or E_Y. Ranks may vary and may be zero.
4. Apply the pure-tensor comparison in clause (1) of
   lem-pur-proetale-inverse-image-tensor-comparison to E_X tensor over A_X M.
   Transport its coefficient actions by the commuting alpha square from step 1.
   The given rationalization then gives an isomorphism E_Y tensor over A_Y g_A^*M -> g_E^*L.
5. The pure-tensor normalization sends 1 tensor p to the pulled inclusion of p.
   Linearity and local tensor generation determine the morphism, so the isomorphism
   is the scalar-extension adjoint of the specified inclusion itself.
-/
theorem lattice_pullback (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : ringedSiteModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (M : ringedSiteModules.{u + 1} (latticeModuleRing X (latticeCoefficientIntegers l E)))
    [L.IsFiniteLocallyFree] [M.IsFiniteLocallyFree]
    (i : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (integralLatticeCoefficientMap X l E))).obj L) [Mono i]
    (hi : ∃ phi : SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (integralLatticeCoefficientMap X l E) M ⟶ L,
      IsIso phi ∧ ∀ (V : X.ProEt) (m : M.val.obj (op V)),
        phi.val.app (op V) (latticePullbackScalarUnit (integralLatticeCoefficientMap X l E)
          M V m) = i.val.app (op V) m) :
    ∃! j : continuousModulePullback g (latticeCoefficientIntegers l E) M ⟶
        (SheafOfModules.restrictScalars
          ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              (integralLatticeCoefficientMap Y l E))).obj
                (continuousModulePullback g
                  (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L),
      (∀ (V : X.ProEt) (m : M.val.obj (op V)),
        j.val.app (op ((Scheme.proEtaleBaseChange g).obj V))
            (continuousLatticePullbackSection g (latticeCoefficientIntegers l E) M V m) =
          continuousLatticePullbackSection g
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L V (i.val.app (op V) m)) ∧
      Mono j ∧
      (continuousModulePullback g (latticeCoefficientIntegers l E) M).IsFiniteLocallyFree ∧
      (continuousModulePullback g
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L).IsFiniteLocallyFree ∧
      ∃ beta : SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (integralLatticeCoefficientMap Y l E)
            (continuousModulePullback g (latticeCoefficientIntegers l E) M) ⟶
          continuousModulePullback g (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L,
        IsIso beta ∧ ∀ (V : Y.ProEt)
          (m : (continuousModulePullback g (latticeCoefficientIntegers l E) M).val.obj (op V)),
          beta.val.app (op V) (latticePullbackScalarUnit (integralLatticeCoefficientMap Y l E)
            (continuousModulePullback g (latticeCoefficientIntegers l E) M) V m) =
              j.val.app (op V) m := by
  sorry

end AlgebraicGeometry.ProEtale
