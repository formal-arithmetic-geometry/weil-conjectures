/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPart
import Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import WeilConjectures.AlgebraicGeometry.PerfectComplex

/-! # Quasi-coherence of internal derived Hom on algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 0A8A, cases (1) and (2),
applied etale locally for the locally bounded-below formulation.
(blueprint: lem-sfb-space-pseudocoherent-rhom-quasicoherent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace

/-- Internal derived Hom preserves quasi-coherence in the perfect-source case and
in the pseudo-coherent-source, locally bounded-below-target case.
Source: Stacks Project, Tag 0A8A
(blueprint: lem-sfb-space-pseudocoherent-rhom-quasicoherent).
Proof:
1. Choose jointly surjective etale scheme charts, refining them by the local lower
bounds in case (ii). Exact etale restriction and the chart criterion preserve
quasi-coherent cohomology (lem-sfb-space-derived-etale-chart-calculus). Finite-free
terms, their summands, and their kernels and cokernels are quasi-coherent by
lem-sfb-space-qcoh-kernels-colimits, so K also has quasi-coherent cohomology.
2. Use lem-sfb-derived-etale-zariski-equivalence to write each restricted pair as
pullbacks of Zariski quasi-coherent derived objects. Exact faithful pullback reflects
lower cohomological bounds. Apply lem-sfb-etale-detects-perfect or
lem-sfb-etale-pseudocoherence-descent; bounded-above finite-free models have the
required strictly perfect truncations in every degree.
3. Apply lem-sc-rhom-supported-qcoherent-perfect-part or
lem-sc-rhom-supported-qcoherent-pseudo-part to the Zariski pair on each chart.
4. For perfect K, work on Zariski opens carrying bounded strictly perfect models
(def-pc-perfect-complex). The etale site of each open is the corresponding slice.
By lem-weil-pbc-ringed-internal-hom-exact-restriction and
lem-sfb-ringed-site-strict-perfect-hom, compute both Homs by ordinary Hom complexes.
Pullback commutes with Hom from a finite free term and with its split summands;
only finitely many source degrees occur. The termwise identifications respect the
signed Hom differential, giving the local comparison without a bound on L.
5. In the pseudo-coherent case use lem-sfb-zariski-etale-pseudocoherent-rhom with
the lower bound on that chart. In either case the compared Hom is quasi-coherent;
for the perfect case apply the chart criterion once more on the chosen opens.
6. Restrict RHom on X to each chart using
lem-weil-pbc-ringed-internal-hom-exact-restriction, and descend quasi-coherence by
lem-sfb-space-derived-etale-chart-calculus. Every local lower bound is used separately;
no Noetherian, separation, quasi-compactness or uniform bound is required. -/
theorem pseudoCoherent_rhom_quasiCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] (K L : X.DerivedModules)
    (hL : X.derivedQCohProperty L)
    (hcase : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf K ∨
      X.IsPseudoCoherent K ∧
        ∀ V : X.SmallEtaleModel, ∃ T : Sieve V, T ∈ X.smallEtaleModelTopology V ∧
          ∀ (U : X.SmallEtaleModel) (f : U ⟶ V), T f →
            ∃ c : ℤ, ∀ n : ℤ, n < c →
              IsZero ((SheafOfModules.overFunctor.{u} X.smallStructureRings U).obj
                ((DerivedCategory.homologyFunctor X.SmallModules n).obj L))) :
    X.derivedQCohProperty (X.derivedHom.obj (op K, L)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
