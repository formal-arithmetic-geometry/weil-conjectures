/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.AmplePullback
import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.TraceFormula.SpaceLineModuleProjMap
import Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange

/-!
# Relative ampleness on an affine open cover

Source: literature/stacks-project/morphisms.tex, Tag 01VJ, implication (3) implies (1)
(blueprint: lem-trf-scheme-relative-ample-affine-cover).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u v

/-- Relative ampleness is detected on an affine open cover of the target.

Source: Stacks Project, morphisms.tex, Tag 01VJ, implication (3) implies (1)
(blueprint: lem-trf-scheme-relative-ample-affine-cover).

Proof, following the seven DAG steps:
1. Set `Z_i = h⁻¹(U_i)` and restrict `h` and `N`. Every affine open of `U_i`
   maps affinely to `U_i` (lem-weil-pbc-morphism-affine-schemes-affine), so its inverse
   image maps affinely to `Z_i` (lem-weil-pbc-affine-morphism-permanence). Tensor
   pullback is restriction (def-pc-module-pullback), and preserves ampleness for this
   affine map (lem-weil-pbc-pullback-ample-invertible). The restricted morphism is
   quasi-compact by def-weil-finite-type-morphism, since these affine opens are also
   affine opens of `S`. Thus `N_i` is relatively ample in the quasi-compact sense.
2. Apply lem-trf-scheme-ample-canonical-proj-criterion locally. It gives
   quasi-separatedness, the section algebra and evaluation, full generation locus,
   an open canonical Proj map, and separatedness of the restricted morphism.
3. View schemes as representable spaces (def-trf-algebraic-space). After each affine
   scheme test, quasi-compactness is preserved by base change
   (lem-weil-pbc-qcqs-morphism-permanence), so the identity gives a quasi-compact
   atlas. The diagonal is closed (def-weil-proper-morphism), and all its tests are
   closed by lem-weil-pbc-closed-immersion-base-change. Hence each restricted space
   morphism is quasi-compact and separated in lem-trf-space-qc-separated-etale-local.
4. The cover inclusions are jointly surjective and etale
   (lem-weil-pbc-etale-composition-cancellation). By
   lem-trf-space-qc-separated-etale-local, `h` is separated as a space morphism.
   Testing its diagonal by the identity recovers the closed scheme diagonal
   (def-weil-proper-morphism). A closed immersion is affine (def-weil-closed-immersion)
   and hence quasi-compact (lem-weil-pbc-affine-morphism-permanence), giving
   quasi-separatedness by def-weil-quasi-separated-morphism. Retain the given
   quasi-compactness of `h`.
5. Use lem-trf-scheme-zariski-etale-quasi-coherent-equivalence to view `N` as a line
   module on the small etale site. The canonical graded section algebra and evaluation
   of lem-trf-space-section-algebra-etale-base-change restrict to the local algebras
   and maps of step 2, and agree with the ordinary scheme constructions.
6. By lem-trf-space-line-module-proj-map, the generation locus and canonical Proj map
   have these same restrictions. The local generation loci are all of `Z_i`, which
   cover `Z`, so the global generation locus is `Z`. The induced etale cover of Proj
   remains jointly surjective (lem-weil-pbc-etale-covering-base-change). Its base
   changes of the canonical map are the local open immersions, so
   lem-trf-space-open-immersion-etale-local makes the global map an open immersion.
7. Apply the reverse direction of lem-trf-scheme-ample-canonical-proj-criterion using
   the original quasi-compactness, step 4's quasi-separatedness, and steps 5 and 6.
   Relative ampleness unfolds to the asserted ampleness on every affine base open.
-/
theorem scheme_relative_ample_affine_cover
    {Z S : Scheme.{u}} (h : Z ⟶ S) [QuasiCompact h]
    (N : Z.Modules) [N.IsInvertible]
    {I : Type v} (U : I → S.Opens)
    (hU : ∀ i : I, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hample : ∀ i : I,
      @Scheme.Modules.IsAmple (h ⁻¹ᵁ U i).toScheme
        ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ U i).ι).obj N)
        ((Scheme.Modules.invertible_pullback_tensor (h ⁻¹ᵁ U i).ι).1 N).2) :
    ∀ (V : S.Opens), IsAffineOpen V →
      @Scheme.Modules.IsAmple (h ⁻¹ᵁ V).toScheme
        ((Scheme.Modules.tensorPullback (h ⁻¹ᵁ V).ι).obj N)
        ((Scheme.Modules.invertible_pullback_tensor (h ⁻¹ᵁ V).ι).1 N).2 := by
  sorry

end AlgebraicGeometry
