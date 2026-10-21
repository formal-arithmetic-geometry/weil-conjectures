/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.FiniteComparisonCoefficients
public import Sheaf.Paper.FiniteComparisonModelRealization
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Coefficient presentation of the finite comparison predicates

Source: blueprint finite comparison, coefficient paragraph, and Stacks Tags 03CY,
09AJ and 09AL (blueprint: lem-ctf-finite-comparison-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

/-- The specified model realizations identify the two coefficient presentations of
bounded finite-Tor constructibility.
This is a change of coefficient presentation, independently of any equivalence between
the etale and pro-etale constructible subcategories.

Source: blueprint finite comparison, coefficient paragraph; Stacks Tags 03CY, 09AJ,
09AL and 08G1 (blueprint: lem-ctf-finite-comparison-presentation).

Proof: restriction to constant scalars is the exact equivalence proved in
coefficientModelFixedScalars_isEquivalence. Compose with the AsSmall site equivalences,
as in the definitions of the two model realizations. Their inverses identify the same
sections and scalar actions. On the etale site finite locally constant modules and
finite locally closed stratifications are unchanged by these equivalences. For the
pro-etale site use the finite-discrete coefficient ring isomorphism: a finite matrix
between regular condensed modules consists of constant scalar entries; its cokernel
is the constant sheaf of the corresponding finitely presented B-module. Conversely
any finitely generated B-module has such a finite presentation, since the finite ring
B is Noetherian. Pullback commutes with these presentations and with scalar transport,
so local trivializations on each stratum identify the two constructibility predicates.
The qcqs affine-local and finite global stratification conventions agree by finite
stratification gluing. Exactness identifies cohomology and reflects zero objects, hence
preserves the same finite cohomological bounds. These coefficient equivalences are
strong monoidal: sectionwise tensor products and their sheafifications agree on pure
tensors. Thus K-flat representatives and tensor tests in degree zero give the same Tor
interval on either side, including reflection by the inverse equivalence. This proves
the two replete-image equalities.

Empty schemes, zero rings, and zero complexes are covered by these constructions. -/
theorem finiteComparisonPresentation (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    let A := ULift.{u + 1} B
    letI : IsNoetherianRing A := inferInstance
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    let P : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale.{u, u + 1} X A K ∧
        ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b
    let Q : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      fun K ↦ coefficientBoundedConstructibleProEtale.{u, u + 1} X A K ∧
        Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u + 1} X A K
    P.map (finiteComparisonEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonEtaleGenerators B X ∧
    Q.map (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonProEtaleGenerators B eR X := by
  sorry

end AlgebraicGeometry.ProEtale
