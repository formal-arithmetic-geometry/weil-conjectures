/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStrictTransformPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

import WeilConjectures.Blowup.AdmissibleBlowup
import Sheaf.AlgebraicGeometry.ModuleStrictTransform
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Module flattening by an admissible blowup of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 087C,
theorem-flatten-module; Divisors on Spaces, Tag 0862
(blueprint: lem-sfb-space-module-flattening-by-admissible-blowup).

The statement retains the finite-type centre and the defining quotient of the module
strict transform. The ambient fibre product X ×_T T' is the one carried by a space
strict-transform presentation; the module quotient lives on it. Relative flatness is
tested on all compatible etale scheme charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-type quasi-coherent module, flat and finitely presented over the indicated
quasi-compact open, becomes flat and finitely presented after admissible blowup.
The base is qcqs; the source is quasi-compact and locally finitely presented over it.
Source: Stacks Project, More on Morphisms of Spaces, Tag 087C,
theorem-flatten-module; Divisors on Spaces, Tag 0862
(blueprint: lem-sfb-space-module-flattening-by-admissible-blowup).

Proof:
1. Choose affine etale surjective atlases V -> X and W -> T by
   lem-trf-space-qc-finite-affine-atlas-refinement. The second atlas is quasi-compact
   and separated by lem-sfb-space-affine-source-qc-separated. The inverse image U_W
   is quasi-compact: cover U by a quasi-compact affine atlas U_0, test the second
   atlas on U_0, and descend compactness along the resulting surjective etale map.
   Fibre-product and representable-etale scheme tests give the scheme Y = V times_T W
   and its surjective etale map to X times_T W.
2. Affine qcqs and lem-sfb-space-qcqs-source-products make Y qcqs. Scheme morphism
   permanence gives quasi-compactness of Y -> W; the chart test gives local finite
   presentation. Restrict M to Y and use the scheme Zariski-etale quasi-coherent
   equivalence and lem-sfb-scheme-etale-module-exact-finiteness-comparison. The resulting
   Zariski module N is finite type, finitely presented and flat over U_W on that open.
   Pullback quasi-coherence is lem-sfb-space-module-pullback-quasicoherent.
3. Apply lem-trf-flattening-module-by-admissible-blowup to Y -> W and N. Its centre I
   is finite type and unit on U_W. The atlas satisfies the chartwise etale condition
   by etale cancellation in lem-trf-space-representable-etale-scheme-tests. Apply
   lem-sfb-space-etale-ideal-factor to get finite-type J on T and I' on W with J unit
   on U and J O_W = I I'. The scheme/etale comparison preserves these ideals.
4. Blow up T in J. By lem-sfb-space-blowup-chart-properties its pullback to W is the
   ordinary blowup in I I', and it is the identity over U. Thus it is U-admissible.
5. Apply lem-trf-factorized-centres-product-transform with a singleton index and
   identity chart maps. The I I' transform N_2 is the ordinary pullback of the flat
   I transform N_1 along the second blowup, compatibly with quotient maps. It is flat
   over that blowup and finitely presented by lem-pc-tensor-pullback-finite-presentation.
6. On an affine chart, vanishing off V(t) is equivalent to vanishing after localization,
   hence to annihilation by a power of t. The locally principal supported-kernel lemma
   makes this kernel quasi-coherent. Under the scheme Zariski-etale equivalence its
   kernel and quotient agree with the etale torsion quotient: etale test rings are
   flat, so tensoring preserves ker(P -> P_t). Now apply
   lem-sfb-space-strict-transform-etale-localization to identify the restriction of M'
   with N_2, including the quotient maps.
7. The transformed charts cover both base and source by the fibre-product cover lemma
   and transform localization. Their N_2 descriptions descend quasi-coherence and
   finite presentation by the local-presentation definitions. Finally
   lem-sfb-space-module-flat-arbitrary-charts transfers flatness on these compatible
   charts to every compatible pair of charts. This is ModuleIsFlatOver over T'. -/
theorem exists_flat_finitePresentation_moduleStrictTransform_admissibleBlowup
    {S : Scheme.{u}} (X T U XU : AlgebraicSpace S) (f : X ⟶ T) (j : U ⟶ T)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (fU : XU ⟶ U) (qU : XU ⟶ X)
    (hU : IsPullback qU.hom fU.hom f.hom j.hom)
    (hTqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ T.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (hTqs : IsAbsolutelyQuasiSeparated T)
    (hUqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ U.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (hXqc : ∃ (V : Over S) (a : yoneda.obj V ⟶ X.obj.obj),
      CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a)
    (hflfp : MapIsLocallyOfFinitePresentation f)
    (M : X.Modules) (hMqc : M.IsQuasicoherent) (hMft : M.IsFiniteType)
    (hMUfp : SheafOfModules.IsFinitePresentation ((moduleTensorPullback qU).obj M))
    (hMUflat : ModuleIsFlatOver fU ((moduleTensorPullback qU).obj M)) :
    ∃ I : QuasiCoherentIdeal T, (I.val : T.Modules).IsFiniteType ∧
      (∀ V : T.EtaleSite,
        (∃ a : yoneda.obj V.obj.left ⟶ U.obj.obj, a ≫ j.hom.hom = V.obj.hom) →
          idealSectionImage I.val.arrow V = ⊤) ∧
      ∃ (B : BlowupPresentation I) (P : StrictTransformPresentation f I B)
        (D : ModuleStrictTransformPresentation f I B P M),
        SheafOfModules.IsFinitePresentation D.module ∧
        ModuleIsFlatOver P.toBlowup D.module := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
