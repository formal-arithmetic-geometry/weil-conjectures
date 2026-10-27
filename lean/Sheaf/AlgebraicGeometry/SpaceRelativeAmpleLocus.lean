/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.SpaceRelativeAmpleTest
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import WeilConjectures.AlgebraicGeometry.LimitResidueField
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.AmplePullback
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The relative ample locus of a proper algebraic space over a scheme

Source: Stacks Project, spaces-descent.tex, Tag 0D3D; spaces-divisors.tex, Tags 0D31
and 0D32 (blueprint: lem-sfb-space-relative-ample-locus).
The scheme-test definition includes representability and canonical tensor pullback.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper algebraic space with a line module has an open relative ample locus.
The first clause is its representing-open universal property. The second tests its
points on every algebraically closed field-valued point. The third gives the same
universal property after arbitrary base change, with open exactly the inverse image.
The last clause explicitly records that the space over the open is a scheme.

Source: Stacks Project, Tag 0D3D, including assertion (A) in its proof; Tags 0D31, 0D32
(blueprint: lem-sfb-space-relative-ample-locus).

Proof:
1. Interpret tensor pullback by the canonical ringed étale morphisms of
   lem-trf-space-enlarged-etale-ringed-site-model. Pulling back local trivializations
   preserves line modules. The comparison of
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence identifies their scheme
   restrictions with the ordinary invertible modules, for arbitrary scheme maps.
2. By lem-pc-field-extension-fpqc-cover and
   lem-sfb-space-relative-ampleness-fpqc-descent, an ample schematic fibre over a
   field extension descends to the residue field. The converse follows from
   lem-trf-scheme-relative-ample-base-change. Thus geometric and residue fibres agree.
3. Around an ample residue fibre choose an affine base open by
   lem-weil-pbc-affine-opens-basis. It is qcqs by lem-weil-pbc-affine-scheme-qcqs.
   Apply lem-sfb-space-proper-noetherian-approximation. By
   lem-sfb-space-affine-limits-schematic-stages the base stages are eventually affine
   schemes; the projections and transitions are affine, without cartesian squares.
4. Apply lem-sfb-space-invertible-limit-descent to descend the line to a stage and
   pull it to the tail, obtaining compatible lines with the original limit line.
5. By lem-weil-pbc-limit-residue-field the residue field is the colimit of stage
   residue fields. The fibres are consequently their inverse limit, by the
   universal property of pairs of compatible maps to space and residue-field spectra.
   Their transitions are affine: test over affine schemes, using
   lem-weil-pbc-morphism-affine-schemes-affine and
   lem-weil-pbc-affine-morphism-permanence. The fibres are qc separated. Apply
   lem-sfb-space-affine-limits-schematic-stages and then
   lem-trf-ample-affine-limit-descent to obtain an ample schematic stage fibre.
6. The stage base is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
   Apply lem-sfb-space-noetherian-ample-neighbourhood and shrink to an affine open.
   Its inverse image in the original base is affine. The inverse image of the
   corresponding schematic space open under the affine projection is schematic;
   lem-weil-pbc-pullback-ample-invertible makes its line ample, also over every
   affine subopen, by the affine-morphism permanence and affine-scheme map lemmas.
7. The set of ample geometric fibres is the union of these opens. By
   lem-trf-scheme-relative-ample-base-change no other fibres occur. The étale-local
   theorem lem-trf-algebraic-space-ample-local glues the relatively ample schemes
   on this arbitrary open cover. No finite cover or compact base is needed.
8. A scheme map factoring through this open has relatively ample pullback by base
   change. Conversely its ample fibres descend by the field-extension fpqc cover
   and relative-ampleness descent. Its image lies in the open, hence it factors
   uniquely through the open subscheme by restricting its map of ringed spaces.
9. For any base change, the inverse-image open has this same universal property:
   factoring through it is equivalent to factoring the composite through the
   original open. Uniqueness of a representing open identifies it with the new
   ample locus. Apply the universal property to the open's own inclusion to obtain
   the final schematicity assertion. -/
theorem exists_relativeAmpleLocus {T : Scheme.{u}} {X : AlgebraicSpace T}
    (f : X ⟶ schemeSpace (Over.mk (𝟙 T))) (hf : MapIsProper f)
    (L : X.Modules) (hL : X.IsLineModule L) :
    ∃ A : T.Opens,
      (∀ B : Over T, (∃ a : B.left ⟶ A.toScheme, a ≫ A.ι = B.hom) ↔
        IsAmpleSchemeBaseChange f L B) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ T)
        (x : Spec (.of K)), a x ∈ A ↔ IsAmpleSchemeBaseChange f L (Over.mk a)) ∧
      (∀ (B : Over T) (C : Scheme.{u}) (g : C ⟶ B.left),
        (∃ a : C ⟶ (B.hom ⁻¹ᵁ A).toScheme, a ≫ (B.hom ⁻¹ᵁ A).ι = g) ↔
          IsAmpleSchemeBaseChange f L (Over.mk (g ≫ B.hom))) ∧
      (∃ U : (enlargedFibreProduct f (ampleLocusBaseMap (Over.mk A.ι))).EtaleSite,
        IsIso U.obj.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
