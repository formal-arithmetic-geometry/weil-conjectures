/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.FlatModuleAtPrime

/-! # Flat closure of a generic subgroup over a DVR

Source: Conrad, *Reductive group schemes*, Theorem 5.3.5, proof, printed p.166,
the schematic closure paragraph (blueprint: lem-sfb-dvr-flat-generic-subgroup-closure).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The closure of a closed generic subgroup is a separated flat finitely presented group,
and receives a unique factorization from every flat source whose generic map factors.
The affine kernel formula specifies the closure itself, and the isomorphism over the
ambient generic fibre specifies equality as closed subschemes, including their embeddings.

Source: Conrad, *Reductive group schemes*, Theorem 5.3.5, proof, printed p.166,
expanded by the affine kernel and flat-source arguments of the accepted split
(blueprint: lem-sfb-dvr-flat-generic-subgroup-closure).

Proof:
1. On an affine open Spec B of G, contract the ideal J of the given generic subgroup
   from B tensor K to B. This is the kernel of restriction to the inverse image in H.
   Contraction commutes with localization: b/t vanishes exactly when some multiple
   ub lies in the kernel. The ideals therefore glue to a quasi-coherent ideal sheaf;
   lem-weil-pbc-quasi-coherent-ideal-closed-subscheme constructs its closed subscheme.
2. Localizing the contracted ideal back to K recovers J: if b/r belongs to J, then
   b/1 belongs to J. The affine fibre-product formula identifies the generic closed
   subscheme with H, compatibly with the embeddings (lem-weil-pbc-fibre-product-affine-spectra).
3. B/I injects into the K-vector space (B tensor K)/J, hence is R-torsion-free.
   A DVR is a PID, so lem-weil-pbc-pid-torsion-free-module-flat gives flatness.
   Lem-pc-affine-flat-module-local-criterion gives flatness on stalks, hence on C.
   This argument uses no flatness of B or of G.
4. For a flat source X, work on affine opens Spec D above Spec B. By the flat affine
   criterion and lem-trf-flat-module-torsionfree-domain, D is R-torsion-free. Each
   element of I vanishes generically by the given factorization, so a nonzero element
   of R kills its image in D; that image is zero. The resulting quotient maps glue,
   uniquely since a closed immersion is monic. No finiteness condition on X is used.
5. C times_S C is flat: on affine charts tensoring with its coordinate ring is
   successive tensoring with two flat R-algebras. The identity source S is flat too.
6. Apply step 4 to multiplication, inverse, and identity of G on these flat sources.
   Step 2 and the subgroup hypothesis give the generic factorizations. The group
   diagrams hold after composing with the monic inclusion, hence hold on C itself.
   The inclusion is consequently a homomorphism with the restricted operations.
7. Quotients of the finite-type affine charts of G give a finite-type finite affine
   cover of C. The diagonal of C is a base change of that of G, so C is separated
   and thus quasi-separated (lem-pc-separated-quasi-separated).
8. A DVR is Noetherian. The finite-type quotient algebras are finitely presented by
   lem-weil-pbc-finite-type-noetherian-finite-presentation. Together with the finite
   cover and quasi-separatedness this gives finite presentation in the sense of 01TP.
-/
theorem exists_dvr_flat_generic_subgroup_closure
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Grp (Over (Spec (.of R))))
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (H : Grp (Over (Spec (.of K))))
    (j : H ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj G))
    [IsClosedImmersion j.hom.hom.left] :
    ∃ (C : Grp (Over (Spec (.of R)))) (i : C ⟶ G),
      IsClosedImmersion i.hom.hom.left ∧
      (∀ V : G.X.left.affineOpens,
        i.hom.hom.left.ker.ideal V =
          RingHom.ker ((j.hom.hom.left ≫
            pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V).hom) ∧
      (∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj C.X ≅ H.X,
        e.hom ≫ j.hom.hom =
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map i.hom.hom) ∧
      IsSeparated C.X.hom ∧ Flat C.X.hom ∧
      LocallyOfFinitePresentation C.X.hom ∧ QuasiCompact C.X.hom ∧ QuasiSeparated C.X.hom ∧
      ∀ (X : Over (Spec (.of R))) (v : X ⟶ G.X), Flat X.hom →
        (∃ w : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ H.X,
          w ≫ j.hom.hom =
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map v) →
        ∃! w : X ⟶ C.X, w ≫ i.hom.hom = v := by
  sorry

end AlgebraicGeometry
