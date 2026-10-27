/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Blowup.Affine.ChartAlgebra
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.CategoryTheory.SiteCechComplex

/-!
# Globally generated modules on the blowup of a regular local surface

Source: Stacks Project, resolve.tex, Tag 0AGS, clause (3), globally generated case
(blueprint: lem-sfb-maximal-point-blowup-generated-cohomology).

The centre is the kernel ideal of the canonical residue-field map on spectra.
The free sheaf map indexed by all global sections is the evaluation map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A globally generated quasi-coherent module on the maximal-ideal blowup of a
two-dimensional regular local ring has zero first Zariski module-sheaf cohomology.

Source: Stacks Project, resolve.tex, Tag 0AGS (lemma-cohomology-of-blowup), clause (3),
globally generated case (blueprint: lem-sfb-maximal-point-blowup-generated-cohomology).

Proof:
1. Apply lem-sfb-point-blowup-local-chart-package to Spec A and its reduced closed point.
   Regular-local localization makes Spec A regular; its dimension is two by
   lem-weil-pbc-spec-topological-krull-dimension-ring. A neighbourhood of the closed point
   is all of Spec A, and localization at the maximal ideal is A. Thus the package gives
   charts U = Spec A[m/s], V = Spec A[m/t] of this very blowup, with s,t nonzero parameters.
   Their intersection W is D(t/s) in U and D(s/t) in V.
2. Put q = t/s and p = s/t. The chart rings are A[q] and A[p], respectively, by
   def-nagata-blowup-chart-ring. By lem-weil-pbc-spec-module-tilde-sections the overlap
   ring is A[q][1/q]. Its map to A[1/(st)] is injective because A is a domain and s,t
   are nonzero. Hence p restricts to q inverse on W. Every overlap coefficient is a
   finite Laurent sum in q with coefficients in A. Split it into nonnegative and
   negative powers: it is the sum of restrictions of one element from each chart ring.
3. Let P be the free structure module indexed by the global sections of F, and e its
   evaluation epimorphism. Restriction preserves coproducts and epimorphisms by
   lem-weil-pbc-module-restriction-open-immersion-colimits. The affine tilde adjunction
   (lem-weil-pbc-affine-tilde-gamma-adjunction) and the basic-open section formula identify
   P on every affine chart with the tilde of the corresponding free section module.
   In particular P is quasi-coherent, and its sections on W are finite linear sums.
4. The affine image assertion of lem-weil-pbc-quasi-coherent-module-cokernel-image
   makes the map on sections over W surjective. Write any w as a finite sum of global
   generators with overlap coefficients. Split each coefficient as in step 2. Taking
   the negative of the U sum and the positive V sum gives u,v with v|W - u|W = w.
5. The cover U,V and all its nonempty repeated intersections are affine. Apply
   lem-pc-cech-computes, with the Cech differential of def-weil-pbc-site-cech-complex.
   A degree-one cocycle has diagonal entries zero and opposite off-diagonal entries.
   Step 4 expresses its 01 entry as v|W - u|W, so the entire cocycle is a boundary.
   Thus first Cech cohomology, and therefore first Zariski module cohomology, is zero.
-/
theorem subsingleton_moduleCohomology_one_maximalPointBlowup_of_generated
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2)
    (F : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).ker.blowup.Modules)
    [F.IsQuasicoherent]
    (hgen : Epi (F.freeHomEquiv.symm (id : F.sections → F.sections))) :
    Subsingleton ((RingedSpace.moduleCohomology
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).ker.blowup.toRingedSpace 1).obj
        F) := by
  sorry

end AlgebraicGeometry
