/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology

/-! # Open module cohomology and cohomology of the restricted abelian sheaf

Source: Stacks Project, Tags 01E1 and 03FD
(blueprint: lem-pqf-open-module-cohomology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Module-derived sections over an open agree with abelian-sheaf cohomology of the
restricted module on its induced open subscheme. No affine or quasi-coherence
hypothesis is needed, and degree zero is included.

Source: Stacks Project, Cohomology, Tag 01E1 (2), and Cohomology on Sites, Tag 03FD
(blueprint: lem-pqf-open-module-cohomology-comparison).

Proof:
1. Choose an injective module resolution I of F. By
lem-sc-ringed-space-restrict-injective-resolution, I restricted to U is an injective
resolution of F.over U. Transport this resolution through Scheme.Modules.overEquiv U;
Mathlib's overFunctorEquiv identifies its augmentation and terms with restriction
along U.ι. Equivalences preserve injectivity and exactness.
2. The sections of each term on U are precisely the global sections of its restriction.
These identifications commute with the differentials, by naturality of restriction of
sections. Thus the two complexes of additive groups are isomorphic. The definition of
openModuleCohomology, Mathlib's InjectiveResolution.isoRightDerivedObj, and the
resolution computation of moduleCohomology give the
isomorphism between open cohomology and the underlying additive group of module
cohomology of the restricted module.
The exact forgetful functor from modules over the global ring to additive groups
preserves this homology, since it preserves kernels and cokernels.
3. Apply lem-sc-module-abelian-zariski-cohomology to the scheme U.toScheme and the
restricted module. Injective module sheaves are acyclic after forgetting to abelian
sheaves, as in Stacks 03FD; they need not be injective as abelian sheaves. Hence the
abelian cohomology is computed by the same section complex. At the terminal open,
Ext from the sheafified free abelian representable is Ext from the constant integer
sheaf, by the constant-sheaf adjunction; this identifies Sheaf.H' at top with Sheaf.H.
The latter is Scheme.Modules.H by definition. Compose the additive isomorphisms.
For the empty open both section complexes are zero. In degree zero the comparison is
ordinary restriction of sections, so no positive-degree assumption is required. -/
theorem nonempty_openModuleCohomology_addEquiv_restrict_H (X : Scheme.{u})
    (F : X.Modules) (U : X.Opens) (p : ℕ) :
    Nonempty (((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F) ≃+
      ((Scheme.Modules.restrictFunctor U.ι).obj F).H p) := by
  sorry

end AlgebraicGeometry
