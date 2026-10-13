/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.HomologyEvaluationDefinitions
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.Paper.DerivedHomMayerVietoris
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Local tensor comparison of augmented K-flat resolutions

Source: Stacks Project, Tag 06YJ, independence of K-flat representatives;
Tag 06YI, derived pullback and its compatibility with restriction.
(blueprint: new-s1-local-kflat-tensor-roof). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Two resolutions of the same complex on U have a common quasi-isomorphism
roof after tensor pullback and restriction to V intersect i^{-1}(U).

Source: Stacks Project, Tag 06YJ, proof of independence of K-flat representatives,
and Tag 06YI, composition of derived pullbacks, applied to open restriction.
(blueprint: new-s1-local-kflat-tensor-roof).

Proof: Write F for restriction to U. The supplied augmentations a and b identify
F(P) and F(K) with the same object F(S) in D(U), and both sources are K-flat.
Apply `DerivedCategory.right_fac` to this isomorphism to obtain actual chain
maps from a common vertex. Its first map is a quasi-isomorphism by construction;
the second is one because its image in D(U) is an isomorphism. Replace the
vertex by a K-flat resolution and compose with both maps. The maps out of this new vertex
are quasi-isomorphisms between K-flat complexes. Tag 06YJ shows that tensor
pullback along the restricted morphism preserves both maps: exact inverse
image preserves the quasi-isomorphisms and K-flatness, and tensor with the new
structure sheaf preserves quasi-isomorphisms between K-flat complexes.
Restrict this roof to V intersect i^{-1}(U) and then to the over site; those
restrictions are exact and hence preserve quasi-isomorphisms. The termwise
restriction/base-change isomorphisms identify its two ends with G(P) and G(K).
Compose the roof maps with these isomorphisms to get the claimed q and p.
No immersion, affine, regularity, boundedness, freeness or zero-differential assumption is
needed. The vertex is chosen after both augmentations are supplied. In
particular K=0 is permitted only if F(S) is acyclic, because b must be a
quasi-isomorphism. Empty opens give the zero roof. -/
theorem exists_local_kflat_tensor_roof
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [(Scheme.Modules.tensorPullback i).Additive]
    (V : Z.Opens) (U : Y.Opens) (P K S : CochainComplex Y.Modules ℤ) :
    let F := (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)
    let G := (Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ) ⋙
      moduleOpenOverComplexFunctor Z V (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U))
    ∀ (a : F.obj P ⟶ F.obj S) (b : F.obj K ⟶ F.obj S),
      CochainComplex.IsKFlatResolution (R := U.toScheme.sheaf) a →
      CochainComplex.IsKFlatResolution (R := U.toScheme.sheaf) b →
      ∃ (L : CochainComplex
          (SheafOfModules (V.toScheme.ringCatSheaf.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U)))) ℤ)
        (q : L ⟶ G.obj P) (p : L ⟶ G.obj K), QuasiIso q ∧ QuasiIso p := by sorry

end AlgebraicGeometry
