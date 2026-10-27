/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.QcohCohomologyEtalePullbackNaturality
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import Sheaf.Topology.SpectralSpaceCohomologyDimension
import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.CategoryTheory.KInjectiveComputes

/-! # Quasi-coherent cohomology of algebraic spaces vanishes above dimension

Source: Stacks Project, Spaces Cohomology, Tag 0A4R(1), and its preceding dimension paragraph
(blueprint: lem-sfb-space-qcoh-vanishing-above-dimension).

Cohomology is computed by applying module global sections `Hom(O_X, -)` to an injective
resolution in all module sheaves on the existing equivalent small affine etale model.
The actual restriction equivalence preserves the coefficient universe and global sections.
Extending the resolution by zero retains integer degrees.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-coherent module cohomology on a qcqs algebraic space vanishes above its dimension.
The atlas hypothesis is quasi-compactness, and absolute quasi-separatedness puts no
restriction on the base scheme. The integer bound is nonnegative, so its natural part
represents the same finite dimension bound. The conclusion holds for every injective
resolution in all module sheaves on the equivalent small affine etale model, not just
in the quasi-coherent subcategory. Its restriction functor retains the actual sections.

Source: Stacks Project, Spaces Cohomology, Tag 0A4R(1)
(blueprint: lem-sfb-space-qcoh-vanishing-above-dimension).

Proof:
1. Apply lem-sfb-space-change-base-to-integers to replace the base by Spec Z, retaining
charts, fibre products, point topology, the small etale ringed site and cohomology.
Lemma lem-sfb-qcqs-space-splitting-filtration supplies a finite open filtration U_p and
quasi-compact separated scheme atlases V_p -> U_p, isomorphic over the reduced
complements of U_{p+1}. These give elementary distinguished squares with intersections W_p.
2. Absolute quasi-separatedness restricts to U_p by base change of the diagonal
(lem-sfb-space-quasicompact-affine-tests). Point open calculus identifies its topology
with an open subspace. Open-subspace dimension monotonicity and
lem-sfb-space-etale-atlas-topological-dimension bound the dimensions of V_p by d.
By lem-sfb-space-qcqs-permanence, U_{p+1} -> U_p is quasi-compact; its base change W_p
is therefore quasi-compact. Point open calculus identifies W_p as an open subscheme of
V_p, so its dimension is also at most d. Separated schemes are quasi-separated by
lem-pc-separated-quasi-separated; hence V_p and W_p are spectral by
lem-weil-pbc-qcqs-scheme-spectral.
3. Etale restrictions of G are quasi-coherent by lem-sfb-space-module-pullback-quasicoherent.
The localized ringed-site identifications of lem-trf-space-enlarged-etale-ringed-site-model
identify restriction with tensor pullback. Apply
lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
lem-sfb-qcoh-cohomology-etale-pullback-naturality to compare scheme-chart cohomology with
Zariski module cohomology. Lemma lem-sc-zariski-module-abelian-cohomology-agree and
lem-sfb-spectral-space-cohomology-dimension give vanishing on V_p and W_p above d.
Lemma lem-sfb-spectral-module-top-degree-restriction makes the degree-d restriction
from V_p to W_p surjective; the same natural comparison transports this restriction map.
The bottom stratum U_n is isomorphic to V_n and has the same vanishing.
4. A module map O -> I is the compatible section family given by its values on 1,
with inverse s |-> (a |-> a*s), so Hom(O,I) computes global sections termwise.
Use def-pur-ringed-site-zeroth-hypercohomology and
lem-sfb-derived-internal-hom-sections-model to identify derived Hom from O with module
cohomology, compatibly with restriction. An ordinary injective resolution is K-injective
by lem-sp-kinjective-computes. Specialize lem-sfb-space-derived-hom-mayer-vietoris to
O and G to obtain the exact segment
H^(q-1)(U_{p+1},G) + H^(q-1)(V_p,G) -> H^(q-1)(W_p,G) -> H^q(U_p,G)
-> H^q(U_{p+1},G) + H^q(V_p,G), with the difference of restrictions as first arrow.
5. Descend from U_n to U_1=X. For q>d+1 the middle-left group and final term vanish,
so exactness gives the result. For q=d+1 the V_p summand surjects onto H^d(W_p,G),
so the boundary is zero; the final term still vanishes, giving the result again.
This includes d=0 and empty strata, whose section and cohomology groups are zero. -/
theorem isZero_moduleCohomology_of_dimension_le
    {B : Scheme.{u}} (X : AlgebraicSpace B)
    (hqc : ∃ (U : Over B) (a : yoneda.obj U ⟶ X.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : IsAbsolutelyQuasiSeparated X)
    (d : ℤ) (hd : 0 ≤ d)
    (hdim : topologicalKrullDim (Point X.obj.obj) ≤ (d.toNat : WithBot ℕ∞))
    (G : X.QCoh) (I : InjectiveResolution (X.smallModuleRestriction.obj G.obj))
    (q : ℤ) (hq : d < q) :
    IsZero ((((preadditiveCoyoneda.obj
      (op (SheafOfModules.unit X.smallStructureRings))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat)).homology q) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
