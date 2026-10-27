/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Topology.Irreducible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceDenseSchemeOpen
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.CoherentGenericLocalFreeModel

/-!
# Generic freeness on a reduced irreducible algebraic space

Source: Stacks Project, Spaces Cohomology, Tag 07UQ,
`lemma-prepare-filter-irreducible`, second proof paragraph
(blueprint: lem-sfb-space-generic-freeness).

The open subspace is presented by its representable open immersion. Its étale
restriction is the existing `pullback` functor. The finite free module is the
finite product of `r` copies of the structure module; in this additive module
category it is also their finite direct sum.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A full-support coherent module on a reduced irreducible Noetherian algebraic
space is free of positive finite rank on a nonempty open subspace.
Source: Stacks Project, Spaces Cohomology, Tag 07UQ,
`lemma-prepare-filter-irreducible`, second proof paragraph
(blueprint: lem-sfb-space-generic-freeness).

Proof:
1. Apply lem-sfb-quasiseparated-space-dense-scheme-open to the quasi-compact
   diagonal. The dense scheme open is nonempty. Choose a nonempty affine open
   inside it. The chartwise hypotheses make it reduced and Noetherian; it is
   irreducible as a nonempty open of an irreducible space, hence integral
   (def-pc-integral-scheme, pqf-def-locnoeth).
2. By lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, restriction of F
   corresponds to its Zariski module on that scheme. The chartwise coherence
   hypothesis makes this Zariski module coherent, and the equivalence respects
   further restriction to opens.
3. Its generic local ring is a field by
   lem-sc-integral-function-field-affine-fraction. The maximal ideal is zero,
   so lem-pc-c3-coherent-generic-local-free-model, with identity closed immersion,
   gives a finite free model on an open neighbourhood of the generic point.
4. Transport back by the same Zariski/étale equivalence. Tensor pullback sends
   the structure module and its finite sums to the corresponding étale modules.
   The open is nonempty because it contains the generic point. If the rank were
   zero, every geometric stalk on it would vanish, contradicting full support.
   Thus the finite rank is at least one. -/
theorem exists_generic_free_open
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hred : ∀ T : X.EtaleSite, IsReduced (X.etaleForget.obj T))
    (hirr : IrreducibleSpace (Point X.obj.obj))
    (F : X.Modules) [F.IsQuasicoherent]
    (hF : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F))
    (hsupp : moduleSupport F = Set.univ) :
    ∃ (U : AlgebraicSpace S) (j : U ⟶ X) (hj : IsEtale j.hom.hom),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom ∧
        Nonempty (Point U.obj.obj) ∧
        ∃ r : ℕ, 1 ≤ r ∧
          Nonempty ((pullback j hj).obj F ≅
            (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit U.structureSheaf)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
