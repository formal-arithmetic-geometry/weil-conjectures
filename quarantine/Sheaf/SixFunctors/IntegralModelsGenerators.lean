/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
public import Sheaf.Paper.CompletedCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ContinuousLocallyFreePullback
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CoefficientFiniteDescentObjects
import Sheaf.Paper.CoefficientHeartCommonStratification
import Sheaf.Paper.CoefficientHeartFiltration
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Paper.IntegralModelsOperations
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.Paper.StratifiedLattice
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Integral generators and their finite reductions

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-integral-models,
Integral generators, clauses (1)--(3) (blueprint: det-lem-integral-models-generators).

The generator classes use the existing canonical scalar extension and locally closed
extension by zero. Finite reductions use the total left derived extension of scalars.
Their etale origin is tested through the existing intrinsic finite-coefficient comparison,
after the explicit restriction to constant scalars.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.SixFunctors

open scoped CategoryTheory.Functor

universe u

/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralModel_coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  (coefficientRing X (Mon.mk Λ)).mon

/-- Canonical extension of scalars from the integral coefficient ring to a finite subextension.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def finiteCoefficientExtension (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) ⥤
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) X) :=
  Mod.extendScalars (AlgebraicGeometry.ProEtale.padicIntegersToPadicSubfield X ℓ E)
/-- Canonical extension of scalars from a finite subextension to the algebraic closure.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def qlbarCoefficientExtension (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) X) ⥤
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) :=
  Mod.extendScalars (AlgebraicGeometry.ProEtale.coefficientMap
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)

/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable abbrev integralCoefficientObject (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (coefficientRing X (Mon.mk (Profinite.padicIntegersRingObj ℓ E.1))).X
/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable abbrev finiteCoefficientObject (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  (coefficientRing X (Mon.mk (Profinite.continuousMapRingObj E.1))).X
/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable abbrev qlbarCoefficientObject (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] :=
  (coefficientRing X (Mon.mk (Profinite.padicAlgClRingObj ℓ))).X
/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralCoefficientObject_isComm (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsCommMonObj (integralCoefficientObject X ℓ E) := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)
/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance finiteCoefficientObject_isComm (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsCommMonObj (finiteCoefficientObject X ℓ E) := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)
/-- Canonical coefficient specialization used in the integral generator statement.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance qlbarCoefficientObject_isComm (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] : IsCommMonObj (qlbarCoefficientObject X ℓ) := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)

/-- The module obtained by extension by zero along a locally closed immersion written as
an open immersion followed by a closed immersion.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def integralLowerShriek (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    {S V : Scheme.{u}} (u : S ⟶ V) (i : V ⟶ X) [IsOpenImmersion u]
    [IsClosedImmersion i]
    (L₀ : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)) :
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  ((CondensedRing.openImmersionLowerShriek Λ u) ⋙ CondensedRing.lowerStar Λ i).obj L₀

/-- The class of integral generators after scalar extension to `E`.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def integralModelGenerator (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ObjectProperty (DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E))) := fun K ↦
  ∃ (S V : Scheme.{u}) (u : S ⟶ V) (i : V ⟶ X) (_ : IsOpenImmersion u)
    (_ : IsClosedImmersion i)
    (L₀ : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (integralCoefficientObject S ℓ E)),
    CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ ∧
    K = (DerivedCategory.singleFunctor _ 0).obj
      ((finiteCoefficientExtension X ℓ E).obj
        (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))

/-- The class obtained from integral generators after the further extension to `Q̄_ℓ`.
Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def qlbarModelGenerator (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ObjectProperty (DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (qlbarCoefficientObject X ℓ))) := fun K ↦
  ∃ (S V : Scheme.{u}) (u : S ⟶ V) (i : V ⟶ X) (_ : IsOpenImmersion u)
    (_ : IsClosedImmersion i)
    (L₀ : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (integralCoefficientObject S ℓ E)),
    CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ ∧
    K = (DerivedCategory.singleFunctor _ 0).obj
      ((qlbarCoefficientExtension X ℓ E).obj
        ((finiteCoefficientExtension X ℓ E).obj
          (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀)))

/-- Constant scalars act on continuous functions by constant functions.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def integralModelConstantScalars (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    ULift.{u + 1, u} (ULift.{u, 0} A) →+*
      (continuousMapRingSheaf X A).obj.obj (op (⊤_ X.ProEt)) where
  toFun a := ULift.up (ContinuousMap.const _ a.down.down)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Keep a continuous module's sheaf and restrict its action to constant scalars.
This is the actual restriction functor, with no arbitrary coefficient isomorphism.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def integralModelFixedScalars (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    SheafOfModules.{u + 1} (continuousMapRingSheaf X A) ⥤
      Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (ULift.{u, 0} A))) :=
  SheafOfModules.forgetToSheafModuleCat _ (op (⊤_ X.ProEt))
      (terminalIsTerminal (C := X.ProEt)).op ⋙
    sheafCompose _ (ModuleCat.restrictScalars (integralModelConstantScalars X A))

/-- Constant-scalar restriction is additive, section by section.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
instance integralModelFixedScalars_additive (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (integralModelFixedScalars X A).Additive where
  map_add {M N f g} := by
    ext U m
    rfl

/-- Canonical passage from internal finite continuous coefficients to intrinsic constant
coefficients. The first equivalence reconstructs the sectionwise action, the next functor
restricts to constant scalar functions, and the last is the existing intrinsic realization.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def integralModelIntrinsicRealization (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    [DiscreteTopology A] :=
  (CondensedRing.continuousRingModuleEquivalence X A).functor ⋙
    integralModelFixedScalars X A ⋙ finiteCoefficientIntrinsicRealization X (ULift.{u, 0} A)

/-- The canonical realization is additive, since each of its three factors is additive.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
instance integralModelIntrinsicRealization_additive (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Finite A]
    [DiscreteTopology A] : (integralModelIntrinsicRealization X A).Additive := by
  have : (CondensedRing.continuousRingModuleEquivalence X A).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold integralModelIntrinsicRealization
  infer_instance

/-- The pulled-back reduction modulo the actual exponent `n` (not `n+1`).

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable abbrev integralModelReductionMap (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (n : ℕ) :=
  completedCoefficientMap X (completedReduction ℓ E π (n - 1))

/-- The pulled-back continuous quotient ring retains its commutative ring structure.
Source: blueprint integral generators (3), the finite coefficient identification
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralModelFiniteCoefficient_isComm (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsCommMonObj (completedCoefficient X (Profinite.continuousMapRingSheaf A)).X := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)

/-- Finite reductions of this very extension by zero are bounded constructible and have
bounded constructible etale origin. `completedResidue` indexes powers by `m+1`, so at the
positive level `n` we use `m=n-1`. Finiteness and discreteness are conclusions, not assumptions.

Source: blueprint main-20261015, integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable def integralReductionHasEtaleOrigin (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    {S V : Scheme.{u}} (u : S ⟶ V) (i : V ⟶ X)
    [IsOpenImmersion u] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (integralCoefficientObject S ℓ E)) : Prop :=
  constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
    ((DerivedCategory.singleFunctor _ 0).obj
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀)) ∧
  ∀ n : ℕ, 1 ≤ n →
    Nonempty
      (((Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (integralLowerShriek X
            (Profinite.continuousMapRingObj (completedResidue ℓ E π (n - 1))) u i
            ((Mod.extendScalars (integralModelReductionMap S ℓ E π n).hom).obj L₀))) ∧
    constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (completedResidue ℓ E π (n - 1))) X
      ((Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))) ∧
    ∃ (_ : Finite (completedResidue ℓ E π (n - 1)))
      (_ : DiscreteTopology (completedResidue ℓ E π (n - 1))),
      (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} (ULift.{u, 0} (completedResidue ℓ E π (n - 1)))) X) ⋙
        finiteCoefficientIntrinsicDerivedComparison X
          (ULift.{u, 0} (completedResidue ℓ E π (n - 1)))).essImage
        ((integralModelIntrinsicRealization X
          (completedResidue ℓ E π (n - 1))).rightDerivedFunctor.obj
          ((Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))))

/-- Integral locally free models generate the bounded constructible categories using finitely
many cones and shifts. In the algebraic-closure clause a single finite E is fixed before
forming the closure. The third clause concerns the specified integral module and all of
its positive uniformizer-power derived reductions, including their etale origin.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-integral-models,
Integral generators, clauses (1)--(3)
(blueprint: det-lem-integral-models-generators).

Proof (the node's eight steps):
1. Preliminaries for the locally closed extensions used below. A standing scheme is separated of
finite type over the field in [sk-def-sfb-dc-setting]; the field is Noetherian since its only
ideals are zero and the unit ideal, and [pqf-lem-locnoeth-lft] makes X locally Noetherian.
Finite type gives a finite affine cover, hence X is Noetherian. Open subschemes and closed
subschemes have affine charts given by localizations and quotient rings, so the same holds for
all the locally closed subschemes used here. The Noetherian topology and constructibility facts
in [def-weil-constructible-subset] show that these schemes are qcqs, their open immersions are
quasi-compact, and their locally closed strata are constructible. For a locally closed immersion
$a=i\circ u$, use $a_!=i_*u_!$. By [lem-weil-pbc-proetale-ringed-open-closed], both factors are
exact for any sheaf of coefficient rings. Their coefficient restrictions are the required ones
by [sk-prop-sfb-cartesian-coefficients]. For locally closed $b:T\hookrightarrow S$, exactness,
factorization independence and the canonical isomorphism $a_!b_!\simeq(ab)_!$ are precisely the
statement of [lem-sfb-locally-closed-extension-coherence], applied with $R=\Lambda_X$. Its
coefficients agree with ours by [sk-prop-sfb-cartesian-coefficients]. The composite immersion is
locally closed: write $S$ closed in an open $V\subset X$, and $T$ closed in an open $W\subset
S$; lift $W$ to an open $V\prime\subset V$. Then $T$ is closed in $V\prime$ because the two
affine quotient maps compose, and $V\prime$ is open in $X$.
Uses: sk-def-sfb-dc-setting, lem-weil-pbc-proetale-ringed-open-closed,
sk-prop-sfb-cartesian-coefficients, pqf-lem-locnoeth-lft, def-weil-constructible-subset,
def-weil-open-immersion, def-weil-closed-immersion, lem-sfb-locally-closed-extension-coherence.
2. For any lisse finite free integral module $M_0$ on a locally closed $b:T\hookrightarrow X$,
apply [det-lem-integral-models-operations] (4) to $L=M_0$ and $M=E_X$, viewed as an integral
module. The coefficient restriction is $b^*E_X=E_T$ by [sk-prop-sfb-cartesian-coefficients]. By
[det-prop-sfb-qlbar-colimit-x-invert-ell], $E_X=\mathcal O_{E,X}[1/\ell]$ is flat, and the same
holds on $T$. Therefore this projection formula reads, in degree zero, $$E_X\otimes_{\mathcal
O_{E,X}}b_!M_0\simeq b_!(E_T\otimes_{\mathcal O_{E,T}}M_0)=b_!(M_0[1/\ell]).$$ Here exactness of
$b_!$ is step 1, so its application to the degree-zero tensor calculation introduces no higher
cohomology. This establishes the scalar-extension identity needed for every integral generator,
without presuming any unproved commutation with an infinite colimit.
Uses: det-lem-integral-models-operations, sk-prop-sfb-cartesian-coefficients,
det-prop-sfb-qlbar-colimit-x-invert-ell.
3. Let $K\in D^b_c(X,E)$. By [det-cor-coefficient-heart-ii-generation], it suffices to build
each sheaf $a_!L$, with $a:S\hookrightarrow X$ locally closed and $L$ lisse, from integral
generators. Apply [sk-lem-stratified-lattice] to the standing scheme $S$ and $L$. It gives a
finite locally closed stratification carrying lisse finite free lattices $L_{0,b}$ in
$L|_{S_b}$. Apply [det-lem-coefficient-heart-common-stratification] (1) to refine and order it
so that the successive unions are open in $S$. On a refined stratum restrict the old lattice: a
trivialization of a finite free module restricts to a trivialization, and its scalar extension
still equals the restricted $L$, since inverse image is exact and monoidal. This uses the
coefficient and exact-inverse-image identification of [sk-prop-sfb-cartesian-coefficients];
lisseness after restriction is also [det-lem-coefficient-heart-common-stratification] (2). Thus
the refinement retains the lattices.
Uses: det-cor-coefficient-heart-ii-generation, sk-lem-stratified-lattice,
det-lem-coefficient-heart-common-stratification, sk-prop-sfb-cartesian-coefficients.
4. The lisse sheaf $L$ is constructible by [sk-def-sfb-constructible], using its finite free
local models and the single stratum $S$. Apply [det-lem-coefficient-heart-filtration] on $S$ to
$L$ and the ordered stratification of step 3. It gives finitely many short exact sequences with
quotients $b_!(L|_{S_b})$. Push these sequences forward by the exact $a_!$ of step 1;
transitivity identifies their quotients with $(ab)_!(L|_{S_b})$. By step 2 and
$L|_{S_b}=L_{0,b}[1/\ell]$, each is $( (ab)_!L_{0,b})[1/\ell]\in\mathcal G_E$. By
[lem-sf-derived-ses-triangle], each short exact sequence of module sheaves gives a distinguished
triangle of their degree-zero complexes in the ambient derived category. Induct on the
filtration length: the zero first term is the rank-zero generator, and a triangle with earlier
term and quotient already constructed expresses the next term as a cone up to a shift. This
builds $a_!L$ by finitely many cones and shifts. Substitute these finite constructions into the
finite cone construction of $K$ from [det-cor-coefficient-heart-ii-generation]; there are only
finitely many such substitutions, proving (1).
Uses: det-lem-coefficient-heart-filtration, lem-sf-derived-ses-triangle,
det-cor-coefficient-heart-ii-generation, sk-def-sfb-constructible.
5. For $K\in D^b_c(X,\overline{\mathbf Q}_\ell)$ choose one finite $E$ and $K_E\in D^b_c(X,E)$
with $K\simeq(K_E)_{\overline{\mathbf Q}_\ell}$ by [det-lem-coefficient-finite-descent-objects].
The functor $T=\overline{\mathbf Q}_{\ell,X}\otimes_{E_X}-$ is exact: it is right exact as the
extension-of-scalars left adjoint in [sk-def-sfb-change-of-scalars], and preserves finite limits
by [lem-sfb-qlbar-flat]. Since $T$ is exact, the derived extension $T_{E,\Qlb}=L(T)$ used in
[det-lem-coefficient-finite-descent-objects] is the termwise functor $D(T)$, by the clause on
exact functors in [sk-def-sfb-derived-categories]. Hence
[lem-sf-exact-functor-derived-triangulated] shows that it preserves the cones and shifts in the
construction of (1) for $K_E$. Its value on a generator is $$\overline{\mathbf
Q}_{\ell,X}\otimes_{E_X}(E_X\otimes_{\mathcal O_{E,X}}a_!L_0)\simeq \overline{\mathbf
Q}_{\ell,X}\otimes_{\mathcal O_{E,X}}a_!L_0.$$ This is the associativity of the relative tensor
product: the maps on local pure tensors are $q\otimes(e\otimes m)\mapsto qe\otimes m$ and
$q\otimes m\mapsto q\otimes(1\otimes m)$, mutually inverse and compatible with all balancing
relations and restrictions. Thus all generators use this same $E$, proving (2).
Uses: det-lem-coefficient-finite-descent-objects, sk-def-sfb-change-of-scalars,
lem-sfb-qlbar-flat, lem-sf-exact-functor-derived-triangulated, sk-def-sfb-derived-categories.
6. For (3), a lisse finite free $L_0$ on $S$ has finite constant local models $\mathcal
O_{E,S}\otimes_{\mathcal O_E}\mathcal O_E^r$. This is precisely condition (1) of
[sk-def-sfb-constructible], with the single stratum $S$; the rank may vary between trivializing
opens. Hence the complex concentrated in degree zero is in $D^b_c(S,\mathcal O_E)$ by
[sk-def-sfb-bounded-constructible]. Apply [det-lem-integral-models-operations] (3) to get
$a_!L_0\in D^b_c(X,\mathcal O_E)$. This uses the blueprint's intrinsic category of bounded
complexes with constructible cohomology; the integral criterion is an equivalent
characterization, not an extra condition that must be proved anew here.
Uses: sk-def-sfb-constructible, sk-def-sfb-bounded-constructible,
det-lem-integral-models-operations.
7. Fix $n\ge1$ and put $A_n=\mathcal O_E/\pi_E^n$. By
[det-prop-integral-criterion-constant-coefficients] (1), $\mathcal O_{E,X}/\pi_E^n=(A_n)_X$, and
likewise on $S$. Apply [det-lem-integral-models-operations] (4) with $L=L_0$ and $M=(A_n)_X$;
its restriction to $S$ is $(A_n)_S$ by [sk-prop-sfb-cartesian-coefficients]. Finite free modules
are flat, and this is local on the trivializing cover, so $L_0\otimes^{\mathbf L}_{\mathcal
O_{E,S}}(A_n)_S=L_0/\pi_E^n$. The degree-zero formula and exactness from step 1 give
$$(a_!L_0)\otimes^{\mathbf L}_{\mathcal O_{E,X}}(A_n)_X\simeq a_!(L_0/\pi_E^n).$$ The elementary
flatness calculation here is that tensoring with $\mathcal O_{E,S}^r$ takes an exact sequence to
its $r$-fold direct sum, so no higher terms of a flat resolution contribute. In particular the
formula is derived reduction, not a claim that quotienting is exact on arbitrary integral
sheaves.
Uses: det-prop-integral-criterion-constant-coefficients, det-lem-integral-models-operations,
sk-prop-sfb-cartesian-coefficients.
8. On $S$, $L_0/\pi_E^n$ is locally the constant finite free $A_n$-module $A_n^r$. On $\overline
S\setminus S$ and $X\setminus\overline S$ the sheaf $a_!(L_0/\pi_E^n)$ restricts to zero, by
[lem-weil-pbc-proetale-ringed-open-closed]. These three locally closed pieces form a finite
constructible stratification (discard empty pieces). Thus this degree-zero sheaf is
constructible by [sk-def-sfb-constructible], so is in $D^b_c(X,A_n)$ by
[sk-def-sfb-bounded-constructible]. The coefficient datum
[def-weil-l-adic-coefficient-extension] (4) states that $A_n$ is finite for $n\ge1$. With its
quotient topology it is discrete; every ideal is a finite set and is generated by that set, so
$A_n$ is Noetherian. Also $X$ is qcqs by step 1. Consequently
[det-pe-constructible-comparison-classical] applies to this very stratification: its
restrictions are locally constant of finite type, and therefore the sheaf is classical, i.e. is
a pullback from $X_{\mathrm{et}}$. This proves the remaining assertions of (3), with the
cohomology of every reduction concentrated in the single interval $[0,0]$.
Uses: lem-weil-pbc-proetale-ringed-open-closed, sk-def-sfb-constructible,
sk-def-sfb-bounded-constructible, det-pe-constructible-comparison-classical,
def-weil-l-adic-coefficient-extension.
-/
theorem integral_models_generators
    (k : Type u) [Field k] (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    [CharP k p] (hℓp : ℓ ≠ p) (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) :
    (∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K →
      (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (qlbarCoefficientObject X ℓ)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
      ∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        (sInf {P | qlbarModelGenerator X ℓ E' ≤ P ∧ P.IsTriangulated ∧
          P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ (S V : Scheme.{u}) (u : S ⟶ V) (i : V ⟶ X)
      [IsOpenImmersion u] [IsClosedImmersion i]
      (L₀ : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E)),
      CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ →
      integralReductionHasEtaleOrigin X ℓ E π u i L₀) := by
  sorry

end WeilConjectures.SixFunctors
