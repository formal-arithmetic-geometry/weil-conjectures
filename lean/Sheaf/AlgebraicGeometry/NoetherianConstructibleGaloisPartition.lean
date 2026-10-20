/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic

/-!
# Simultaneous Galois partitions for constructible module sheaves

Source: Stacks Project, Tags 095N, 03S0 and 03SF; ILO, Expose XVII,
Definition 7.3.1 and proof of Theorem 7.6.1, p. 314
(blueprint: lem-per-noetherian-constructible-galois-partition).

We use the recorded arbitrary-coefficient module-sheaf encoding and local finite-type
predicate. On a Noetherian scheme every locally closed subset is constructible, so the
existing global constructibility predicate is precisely the hypothesis in this node.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A finite family of constructible module sheaves over a commutative Noetherian ring
has one finite locally closed partition into nonempty connected reduced strata and one
connected finite etale Galois cover of each stratum simultaneously trivializing all members,
with finitely presented module values. Neither flatness nor finite underlying sets are needed.
Source: Stacks Project, Tags 095N, 03S0 and 03SF; ILO XVII, Definition 7.3.1 and proof of
Theorem 7.6.1, p. 314 (blueprint: lem-per-noetherian-constructible-galois-partition).

Proof plan:
1. Refine the finitely many constructible stratifications using
lemma-constructible-common-refinement, reduce their nonempty strata using
def-weil-pbc-scheme-reduction, and map reduced refined strata to the original ones using
lem-weil-pbc-reduced-source-factors-through-closed-subscheme after restriction to the open
part of each immersion.
2. The strata remain Noetherian: localization and quotient preserve finite generation of
ideals. The nodes lem-weil-pbc-noetherian-scheme-closed-subsets-minimal and
lem-sfb-noetherian-space-compact-subsets give quasi-compactness, and
lem-weil-pbc-locally-noetherian-quasi-separated gives quasi-separatedness.
3. Pull back the local finite-module descriptions to each refined stratum using
lem-weil-pbc-etale-covering-base-change, lem-sfb-geometric-inverse-image-constant-module,
and the composition compatibility of lem-pe-constant-left-module-inverse-image.
Choose finitely many affine trivializing charts: their images are open by
lem-weil-pbc-etale-morphism-open-map and the stratum is quasi-compact.
4. Apply lem-weil-pbc-etale-stratified-finite to every chart and refine simultaneously.
Reduce again, and partition into finitely many nonempty open connected components by
lem-sfb-noetherian-connected-components-open. All the restricted charts are finite etale,
and the charts for each sheaf still cover each stratum by etale covering base change.
5. Form their finite coproduct W by lem-weil-pbc-scheme-coproduct-family. It is finite etale.
The equivalence thm-galois-lc-etale and lem-weil-pbc-finite-set-monodromy-torsor produce a
connected finite etale torsor V trivializing its represented finite set sheaf. The torsor
makes the automorphisms transitive on a geometric fibre. By
lem-galois-finite-etale-connected-object, lem-fet-galois-category and part 6 of
lem-galois-axioms, evaluation on that fibre is injective, hence simply transitive.
6. For each family member choose a chart point over a geometric point of V. Constancy of
the represented pullback extends it to a global section. Connectedness forces this section
to lie entirely in that chart's clopen summand, providing a map V to the trivializing chart.
7. Pull back its constant-module description using
lem-sfb-geometric-inverse-image-constant-module and
lem-pe-constant-left-module-inverse-image. The same V works for every family member.
The values are finitely generated; lem-sc-noetherian-finite-module-finite-presentation makes
them finitely presented over the original ring R.
8. For the empty scheme take the empty partition. For an empty family take the nonempty
connected components of the reduction and their identity Galois covers. Zero modules and
the zero coefficient ring require no extra assumption. -/
theorem exists_noetherian_constructible_galois_partition
    (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (m : ℕ) (E : Fin m → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    (_hE : ∀ j : Fin m, Scheme.IsConstructibleSheaf (E j)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i : Fin S.n, IsReduced (S.domain i)) ∧
      ∀ i : Fin S.n, ∃ hS : ConnectedSpace (S.domain i),
        ∃ V : (S.domain i).FiniteEtale,
          @PreGaloisCategory.IsGalois _ _
            (@Scheme.FiniteEtale.galoisCategory (S.domain i) hS) V ∧
          ConnectedSpace V.obj.left ∧
          ∀ j : Fin m, ∃ M : ModuleCat.{u + 1} R, Module.FinitePresentation R M ∧
            Nonempty
              ((upperStar (ModuleCat.{u + 1} R) V.obj.hom).obj
                  ((upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj (E j)) ≅
                (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  sorry

end AlgebraicGeometry.Etale
