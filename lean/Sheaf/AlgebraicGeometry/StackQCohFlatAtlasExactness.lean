/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Sheaf.AlgebraicGeometry.StackSmallEtaleRestriction
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Quasi-coherent modules and flat scheme tests on an algebraic stack

Source: Stacks Project, stacks-sheaves.tex, Tags 06WN and 06WV(3)--(5);
stacks-cohomology.tex, Tag 0GQF; descent.tex, Tag 06VE
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness).

The small étale restriction is the existing literal restriction along cartesian
lifts, with its existing regular-function rings. The combined functor uses the
ordinary category of families. No kernel preservation is part of the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory

/-- Evaluate a scheme chart at its identity test. The equation that a based functor
commutes with projection identifies its base with U.
Source: Stacks 0GQF (blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness). -/
def moduliAtlasTest {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) C) : C.obj :=
  a.toFunctor.obj (CostructuredArrow.mk (𝟙 (yoneda.obj U)))

/-- Restrict the existing small étale module restriction to the quasi-coherent
full subcategory. This is precomposition on sheaves, with no chosen comparison map.
Source: Stacks 0GQF (blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness). -/
def moduliQCohEtaleRestriction {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    (hC : IsFibredInGroupoids C) (x : C.obj) :
    ModuliQCoh C hC ⥤ ringedSiteModules.{max (u + 1) v w}
      (moduliEtaleModuleRings C hC x) :=
  ObjectProperty.ι _ ⋙ moduliEtaleRestriction C hC x

/-- The combined actual restriction to a small family of scheme charts.
Source: Stacks 0GQF (blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness). -/
def moduliQCohAtlasRestriction {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    (hC : IsFibredInGroupoids C) {I : Type (max (u + 1) v w)} (U : I → Over S)
    (a : ∀ i, BasedFunctor (discreteModuli (yoneda.obj (U i))) C) :
    ModuliQCoh C hC ⥤ ∀ i, ringedSiteModules.{max (u + 1) v w}
      (moduliEtaleModuleRings C hC (moduliAtlasTest (a i))) :=
  Functor.pi' (fun i ↦ moduliQCohEtaleRestriction C hC (moduliAtlasTest (a i)))

/-- Local surjectivity of a restricted module map means lifting every section
after an étale covering, using Mathlib's existing covering-sieve definition.
Source: Stacks 0GQF, 03DA
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness). -/
abbrev IsLocallySurjectiveModuliEtaleMap {S : Scheme.{u}}
    {C : BasedCategory.{v, w} (Over S)} {hC : IsFibredInGroupoids C}
    (x : C.obj) {F G : ModuliQCoh C hC} (f : F ⟶ G) : Prop :=
  Presheaf.IsLocallySurjective (schemeTestBase C x).smallEtaleTopology
    ((SheafOfModules.toSheaf (moduliEtaleModuleRings C hC x)).map
      ((moduliQCohEtaleRestriction C hC x).map f)).hom

/-- The structure module and the sheafified tensor product are quasi-coherent.
Source: Stacks 06WN(2), 06WV(5)
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness).

Proof: the structure module has its identity free presentation. For F and G,
restrict to the slice at each scheme test. The scheme-test comparison identifies
them with the associated big-fppf sheaves of their Zariski modules. Localized
restriction commutes with tensor by lem-sfb-localized-site-tensor-restriction;
lem-sfb-scheme-big-fppf-quasicoherent-equivalence identifies this tensor with the
associated sheaf of the ordinary tensor. The scheme tensor-closure theorem
lem-weil-pbc-quasi-coherent-tensor-product-affine-sections applies. The slice
local-presentation criterion then gives quasi-coherence on the total site. -/
theorem moduliQCoh_unit_tensor {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    (hC : IsAlgebraicModuliStack C) :
    (SheafOfModules.unit (moduliModuleRings C hC.1.1)).IsQuasicoherent ∧
      ∀ F G : ModuliQCoh C hC.1.1,
        ((SheafOfModules.siteSheafTensorRight G.obj).obj F.obj).IsQuasicoherent := by
  sorry

/-- Ambient cokernels are quasi-coherent and their universal property is unchanged
in the full quasi-coherent category. The equivalence for every cokernel cofork
expresses both preservation and reflection of this universal property.
Source: Stacks 06WN(1), 06WV(3),(4)
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness).

Proof: for f:F to G, take its ambient cokernel Q. Restriction to a scheme slice
preserves ambient cokernels by lem-sfb-fibred-fppf-ringed-inverse-image. The
scheme-test comparison and lem-sfb-scheme-big-fppf-quasicoherent-equivalence
identify the restriction with the associated sheaf of the ordinary cokernel.
That cokernel is quasi-coherent by lem-weil-pbc-quasi-coherent-module-cokernel-image.
The local-presentation criterion on every slice makes Q quasi-coherent. Fullness
restricts the ambient universal property to QCoh. Conversely any QCoh cokernel
is uniquely isomorphic, with its quotient arrow, to this lifted ambient one,
so its inclusion is again an ambient cokernel. No assertion about kernels is used. -/
theorem moduliQCoh_cokernels {S : Scheme.{u}} (C : BasedCategory.{v, w} (Over S))
    (hC : IsAlgebraicModuliStack C) {F G : ModuliQCoh C hC.1.1} (f : F ⟶ G) :
    (∃ Q : CokernelCofork f.hom,
      Nonempty (IsColimit Q) ∧ Q.pt.IsQuasicoherent) ∧
      ∀ c : CokernelCofork f, Nonempty (IsColimit c) ↔
        Nonempty (IsColimit ((ObjectProperty.ι
          (SheafOfModules.isQuasicoherent.{max (u + 1) v w}
            (moduliModuleRings C hC.1.1))).mapCocone c)) := by
  sorry

/-- An epimorphism of big-fppf module sheaves is exactly a locally surjective map.
Source: Stacks 03DA, 03CN
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness).

Proof: the underlying abelian-sheaf functor preserves cokernels and is faithful
by lem-weil-pbc-module-sheaves-colimits-forgetful. It reflects zero objects since
a module whose groups are zero has only zero sections. A map is epi exactly
when its cokernel is zero, hence exactly when the underlying abelian-sheaf map
is epi. Apply lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective to identify
that condition with local lifting for fppf covering sieves. -/
theorem moduliModule_epi_iff_locallySurjective {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsAlgebraicModuliStack C)
    {F G : ringedSiteModules.{max (u + 1) v w} (moduliModuleRings C hC.1.1)}
    (f : F ⟶ G) :
    Epi f ↔ Presheaf.IsLocallySurjective (moduliFppfTopology C)
      ((SheafOfModules.toSheaf (moduliModuleRings C hC.1.1)).map f).hom := by
  sorry

/-- Each individual flat scheme-test restriction preserves epimorphisms.
Source: Stacks 0GQF, 06VE(1),(5)
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness).

Proof: the quasi-coherent ambient cokernel is also the QCoh cokernel, so an epi
has zero ambient cokernel. The scheme-test comparison identifies its Zariski
restriction with the ordinary cokernel. The small-étale comparison is exact on
quasi-coherent Zariski modules: factor through the quasi-coherent image and use
the two short exact sequences, with the quasi-coherent scheme kernel and cokernel.
Thus its small-étale restriction has zero cokernel and is epi. These comparisons
are lem-sfb-stack-quasi-coherent-scheme-restriction,
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
lem-sfb-scheme-etale-module-exact-finiteness-comparison. -/
theorem moduliQCoh_flat_test_preserves_epi {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsAlgebraicModuliStack C)
    (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) C)
    (hflat : ModuliSpaceTest (@Flat) a)
    {F G : ModuliQCoh C hC.1.1} (f : F ⟶ G) :
    Epi f → Epi ((moduliQCohEtaleRestriction C hC.1.1 (moduliAtlasTest a)).map f) := by
  sorry

/-- Flat jointly surjective scheme tests give a faithful conservative restriction
and detect epimorphisms by local étale lifting of sections.
Source: Stacks 0GQF; 06WV(3),(4)
(blueprint: lem-sfb-stack-qcoh-flat-atlas-exactness).

Proof:
1. Use the preceding structure/tensor and cokernel assertions. On each scheme
test, the scheme-test comparison identifies the ambient cokernel with the
ordinary quasi-coherent cokernel. The exact Zariski-to-small-étale comparison
then identifies its étale restriction with the restricted map's cokernel.
2. For x:T to C, the representable diagonal gives algebraic spaces
P_i = T times_C U_i by lem-sfb-stack-diagonal-space-source-representability.
Choose étale scheme atlases W_i of P_i. Their maps to T are flat by hflat.
For any residue-field point of T, hsurj supplies a lift to some U_i after a
field extension. This is a point of P_i. A residue field on the pulled-back
étale atlas supplies a further extension and a point of W_i over it. Thus
the W_i are jointly surjective over T, without a finiteness hypothesis.
3. The cartesian scheme-test comparisons identify pullback of f_x to W_i with
pullback of f_(a_i). If every atlas restriction is an isomorphism, full
faithfulness of the small-étale comparison gives this for each Zariski f_(a_i).
Apply lem-sc-flat-cover-module-isomorphism-reflection to obtain that f_x is an
isomorphism. This holds for every x. The formula F(x) = Gamma(T,F_x) makes
every component of f bijective; their inverses are natural by naturality of f.
4. For faithfulness subtract two maps with equal restrictions, obtaining psi.
Its quasi-coherent ambient cokernel map q restricts to the cokernel of zero,
hence an isomorphism everywhere on the family. Step 3 makes q an isomorphism.
Since q psi = 0, psi = 0. This uses cokernels and no ambient kernel closure.
5. Epi in QCoh is equivalent to zero ambient cokernel: cancel through its
quasi-coherent cokernel map, which is ambient epi. If the cokernel is zero,
every individual restriction is epi and thus locally surjective on the small
étale site. Conversely local surjectivity on the atlas makes all restricted
cokernels zero. Step 3 applied to 0 to Q makes Q zero. The epi/local lifting
equivalence follows from the underlying abelian-sheaf cokernel criterion. -/
theorem moduliQCoh_flat_atlas_exactness {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsAlgebraicModuliStack C)
    {I : Type (max (u + 1) v w)} (U : I → Over S)
    (a : ∀ i, BasedFunctor (discreteModuli (yoneda.obj (U i))) C)
    (hflat : ∀ i, ModuliSpaceTest (@Flat) (a i))
    (hsurj : ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
      (y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) C),
      ∃ (L : Type u) (_ : Field L) (e : K →+* L) (i : I)
        (l : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ b) ⟶ U i),
        Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map l)).comp (a i))
          ((discreteModuliMap (yoneda.map
            (Over.homMk (Spec.map (CommRingCat.ofHom e))))).comp y))) :
    (moduliQCohAtlasRestriction C hC.1.1 U a).Faithful ∧
      (moduliQCohAtlasRestriction C hC.1.1 U a).ReflectsIsomorphisms ∧
      ∀ (F G : ModuliQCoh C hC.1.1) (f : F ⟶ G),
        Epi f ↔ ∀ i, IsLocallySurjectiveModuliEtaleMap (moduliAtlasTest (a i)) f := by
  sorry

end CategoryTheory
