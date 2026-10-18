module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Flatness on an open--closed decomposition

Source: literature/stacks-project/proetale.tex, Tag 09AH, together with
etale-cohomology.tex, Tag 095L, and sites-modules.tex, Tag 03ER
(blueprint: lem-sfb-open-closed-flatness).

The two declarations below spell out the ordinary module-sheaf assertion on the
small étale and small pro-étale sites.  The proof is the tensor argument from
the source: inverse image is exact and tensor-compatible, and the open--closed
sequence jointly detects the three exactness defects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Flatness is detected on the two members of a complementary pair on the
small étale site; extension by zero and closed direct image preserve flatness.
Source: Stacks Tags 095L, 03ER and 05VD (blueprint: lem-sfb-open-closed-flatness).

Proof: tensor a short exact sequence with the candidate sheaf.  Exactness of
the two inverse-image functors and the tensor comparison identify the restricted
complexes with tensors by the restricted sheaves.  The open--closed sequence
forces the kernel, middle homology, and cokernel to vanish.  The four
restriction identities for the two adjoint extensions then give the last two
clauses.
-/
theorem openClosedFlatness_etale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (CategoryTheory.ObjectProperty.flat H ↔
      (CategoryTheory.ObjectProperty.flat ((Etale.upperStar (ModuleCat.{u + 1} A) j).obj H) ∧
        CategoryTheory.ObjectProperty.flat ((Etale.upperStar (ModuleCat.{u + 1} A) i).obj H))) ∧
      (∀ L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        CategoryTheory.ObjectProperty.flat L →
          CategoryTheory.ObjectProperty.flat
            ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)) ∧
      (∀ M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A),
        CategoryTheory.ObjectProperty.flat M →
          CategoryTheory.ObjectProperty.flat
            ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M)) := by
  sorry

/-- The same assertion for ordinary module sheaves on the small pro-étale site.
Source: Stacks Tags 09AH, 03DI and 05VD (blueprint: lem-sfb-open-closed-flatness).

The coefficient is the constant finite ring sheaf.  The open object is the
canonical pro-étale object associated to `j`; its extension by zero and the
closed direct image are the ringed-site constructions used in the localization
sequence.

Proof: (1) the two constant-ring pullbacks are module pullbacks of morphisms of
ringed topoi and are exact for these immersions, so flat pullback (Stacks 05VD)
gives the forward implication.  (2) Conversely, tensor a short exact sequence
with `H`; the natural tensor-pullback comparison identifies both restrictions
of the tensored complex with the restricted sequence tensored with the flat
restriction of `H`, hence short exact.  Exact restriction preserves the kernel,
middle homology and cokernel, whose two restrictions therefore vanish, and the
ringed open--closed localization sequence (Tag 09AH) forces a module sheaf with
both restrictions zero to be zero.  (3) The ringed open--closed statement gives
`j^* j_! L ≅ L`, `i^* j_! L = 0`, `i^* i_* M ≅ M` and `j^* i_* M = 0` as
module isomorphisms; the zero sheaf is flat, so the equivalence of (1)--(2)
gives the last two clauses.
-/
theorem openClosedFlatness_proEtale
    (A : Type u) [CommRing A] [Finite A]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (H : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :
    (SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := Scheme.proEtaleConstantRing X A) H ↔
      (SheafOfModules.IsFlatOnSite (J := ProEt.topology U)
          (R := Scheme.proEtaleConstantRing U A)
          ((Scheme.proEtaleConstantRingPullback A j).obj H) ∧
        SheafOfModules.IsFlatOnSite (J := ProEt.topology Z)
          (R := Scheme.proEtaleConstantRing Z A)
          ((Scheme.proEtaleConstantRingPullback A i).obj H))) ∧
      (∀ L : Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology U)
          (R := Scheme.proEtaleConstantRing U A) L →
        SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
          (R := Scheme.proEtaleConstantRing X A)
          ((Scheme.sfIntrinsicExtensionByZero j A).obj L)) ∧
      (∀ M : Scheme.proEtaleRingModules Z (Scheme.proEtaleConstantRing Z A),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology Z)
          (R := Scheme.proEtaleConstantRing Z A) M →
        SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
          (R := Scheme.proEtaleConstantRing X A)
          ((Scheme.proEtaleConstantRingPushforward A i).obj M)) := by
  sorry

end AlgebraicGeometry
