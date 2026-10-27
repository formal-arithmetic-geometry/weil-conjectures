/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.AlgebraicGeometry.SpaceFppfHypercover
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Effective quasi-coherent descent using only face maps

Source: Stacks Project, spaces-simplicial.tex, Tag 0DHD,
lemma-descent-qcoh-for-fppf-hypercovering, with the face-only argument recorded in the DAG
(blueprint: lem-sfb-fppf-face-heart-descent).

The module category is the small-coefficient systems presentation of the ringed total
category. Its augmentation direct image is the ordinary degree-zero/degree-one equalizer.
Degeneracies occur in the geometric input but are never transitions of a module system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The full heart subcategory: quasi-coherent components and invertible face transitions.
Source: Stacks 0DHD, face-only adaptation
(blueprint: lem-sfb-fppf-face-heart-descent). -/
def spaceFaceQCohProperty (U : SimplicialObject (Over X)) :
    ObjectProperty (SpaceFaceModuleSystem U) :=
  fun M ↦ (∀ n : SemiSimplexCategory, (M.obj n).IsQuasicoherent) ∧
    ∀ {m n : SemiSimplexCategory} (a : m ⟶ n), IsIso (M.transition a)

/-- Tensor pullback is an equivalence onto the quasi-coherent cartesian heart, with
ordinary module direct image as inverse and the actual adjunction unit and counit invertible.
Source: Stacks Project, spaces-simplicial.tex, Tag 0DHD,
lemma-descent-qcoh-for-fppf-hypercovering, injective-order-map adaptation;
spaces-descent.tex, Tag 04W8 (blueprint: lem-sfb-fppf-face-heart-descent).

Proof:
1. Pullback preserves quasi-coherence by lem-sfb-space-module-pullback-quasicoherent.
Write q_n for the augmentation and c_v for the transition of a vertex. For a system F
in the indicated subcategory, put t = c_v1 inverse followed by c_v0 on U_1. On U_2 the
transition composition law gives t_02 = t_12 t_01. Pull this equality back along the
double degeneracy U_0 to U_2: e-star(t) is invertible and idempotent, hence the identity.
Degeneracies here only pull back equations; no degeneracy transition or flatness is used.
2. Put R = U_0 times_X U_0 and r : U_1 to R. Over D = U_1 times_R U_1, the boundary
with edges a, b and the degenerate identity at their common target defines a map to M_2.
Pull back the fppf matching cover U_2 to M_2. The triangle identity gives t_a = t_b on
this cover. Full faithfulness of lem-sfb-space-fppf-qcoh-descent first descends this
equality to D and then descends t and its inverse along r. Thus there is an invertible
ordinary descent map theta on R. Quasi-coherence is preserved under all pullbacks.
3. The degree-two matching object over U_0 times_X U_0 times_X U_0 is the fibre product
of the three base changes of r. By lem-sfb-space-fppf-covering-calculus it is fppf, so
U_2 covers this triple product. Full faithfulness descends the triangle equation to
the cocycle equation for theta. Ordinary effective descent gives G in QCoh(X) and a
degree-zero isomorphism q_0-star G to F_0 inducing theta.
4. Define every higher component by a vertex: c_v after pulling back the degree-zero
isomorphism. Every pair of vertices bounds an edge, so the descent identity makes this
independent of the vertex. Composition gives compatibility with every injection. Maps
of systems are determined in degree zero, and degree-one compatibility is exactly
compatibility with theta. Ordinary descent proves full faithfulness and essential
surjectivity onto all systems in the displayed heart.
5. For arbitrary module systems the ordinary right adjoint is the equalizer of the two
vertex arrows q_0-star F_0 to q_1-star F_1. Component module adjunction identifies its
maps from any module N with compatible maps from q_n-star N to F_n: the same vertex
argument assembles all higher components. This is precisely the normalized adjunction
in SpaceFaceAugmentationModel, supplied by lem-sfb-semisimplicial-ringed-total-category.
On enlarged etale objects its sections are the corresponding compatible-section
equalizers, by lem-trf-space-enlarged-etale-ringed-site-model.
6. Apply this equalizer to the descended G. Faithfulness of descent along the first
matching cover replaces agreement on U_1 by agreement on R. Ordinary section descent
then identifies the equalizer with G, compatibly with restrictions and scalars. Thus
the ordinary direct image is quasi-coherent. For the pullback of G this identification
is restriction of sections, hence exactly the adjunction unit, which is invertible.
The triangle identity makes the counit invertible on pullbacks; naturality and step 4
make it invertible on every object of the heart. Restrict the two functors and these
unit/counit isomorphisms to obtain the displayed equivalence. -/
theorem fppf_face_heart_descent (U : SimplicialObject (Over X))
    (hU : IsSpaceFppfHypercover U) (P : SpaceFaceAugmentationModel U) :
    (∀ N : X.QCoh, spaceFaceQCohProperty U (P.pullback.obj N.obj)) ∧
    (∀ M : SpaceFaceModuleSystem U, spaceFaceQCohProperty U M →
      (P.direct.obj M).IsQuasicoherent) ∧
    (∀ N : X.QCoh, IsIso (P.adjunction.unit.app N.obj)) ∧
    (∀ M : SpaceFaceModuleSystem U, spaceFaceQCohProperty U M →
      IsIso (P.adjunction.counit.app M)) ∧
    ∃ e : X.QCoh ≌ (spaceFaceQCohProperty U).FullSubcategory,
      Nonempty (e.functor ⋙ (spaceFaceQCohProperty U).ι ≅
        (SheafOfModules.isQuasicoherent X.structureSheaf).ι ⋙ P.pullback) ∧
      Nonempty (e.inverse ⋙ (SheafOfModules.isQuasicoherent X.structureSheaf).ι ≅
        (spaceFaceQCohProperty U).ι ⋙ P.direct) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
