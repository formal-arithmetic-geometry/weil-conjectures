/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf

/-! # Reflection of finite discrete constructibility by coefficient realization

Source: blueprint main-20261015, finite-discrete coefficient identification in
`sk-prop-ctf-finite-compact-proetale.proof.md`
(blueprint: lem-finite-discrete-ctf-realization).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The specified finite discrete coefficient realization reflects bounded
constructibility and finite Tor amplitude into ordinary fixed-scalar sheaves.

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-ctf-finite-compact/sk-prop-ctf-finite-compact-proetale.proof.md`, first paragraph;
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`, coefficient
identification step (blueprint: lem-finite-discrete-ctf-realization).

Proof. The functor is sheafification of the sectionwise scalar action, followed by
transport along finiteDiscreteSchemeRingIso. Restrict along constant scalar sections to
construct its inverse. Locally every section of the constant ring has a constant scalar
representative; the sheaf axiom makes the unit and counit isomorphisms on underlying
abelian sheaves. Both functors are exact and their termwise derived extensions commute
with cohomology, so boundedness is reflected. A finite presentation of a constant module
is a finite scalar matrix, and sheafification preserves its cokernel. Thus realization
and its inverse preserve finite constant local models on the same pro-etale covers and
on the same strata. Noetherian X is qcqs, so the internal and ordinary conditions both
use global finite constructible strata. Over finite A, finitely presented modules are
finite and finite modules are finitely presented. This identifies ordinary
IsConstructible with the internal constant-model condition. The two relative tensor
products represent the same balanced bilinear maps; their exact coefficient equivalence
preserves flat and K-flat resolutions and their total tensors. Consequently the derived
tensor comparison identifies the tests against every degree-zero module in both
directions and reflects each Tor interval. This proves finite Tor amplitude. If eR is
not the normalized ring isomorphism, compose with the corresponding automorphism of the
constant coefficient ring: scalar transport preserves finite presentation and the same
balanced tensor products. The zero ring and empty scheme require no exception. -/
theorem finiteDiscreteCtfRealization
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
        Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hK : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ DerivedCategory.finiteTorAmplitude _ M)
        ((finiteComparisonRealization A X eR).mapDerivedCategory.obj K)) :
    (DerivedCategory.TStructure.t.bounded K ∧
      ∀ q : ℤ, IsConstructible (ULift.{u + 1} A)
        ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      DerivedCategory.finiteTorAmplitude _ K := by
  sorry

end AlgebraicGeometry.ProEtale
