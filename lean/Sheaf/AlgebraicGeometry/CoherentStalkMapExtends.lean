/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation
import Sheaf.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# A map of stalks of coherent modules comes from a map on a neighbourhood

Source: Stacks Project, Cohomology of Schemes, Lemma 01Y4 (label
`lemma-map-stalks-local-map`), using Lemma 01XZ and Modules Lemma 01CP
(blueprint: lem-weil-pbc-coherent-stalk-map-extends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A homomorphism between stalks of coherent modules is induced by a morphism on
some open neighbourhood.

Source: Stacks Project, Cohomology of Schemes, Lemma 01Y4
(label `lemma-map-stalks-local-map`), using Lemma 01XZ and Modules, Lemma 01CP
(blueprint: lem-weil-pbc-coherent-stalk-map-extends).

Proof:
1. The coherent source `G` is of finite type (`pqf-lem-coherent-ft-locnoeth`).
   Locally choose finitely many generating sections, giving a surjection from a
   finite free module. Its kernel is of finite type by coherence (`pqf-def-coherent`).
   Shrink again and choose finitely many kernel generators. This gives a finite
   presentation of `G` (`def-weil-pbc-module-finite-type-presentation`), as in 01XZ.
2. Apply `lem-weil-pbc-stalk-internal-hom-finite-presentation` (01CP) to `G` and `F`.
   The canonical map from the stalk of internal Hom to Hom of stalks is an
   isomorphism, so `ψ` has a preimage germ. Internal-Hom sections are morphisms
   between the restricted modules (`def-pur-sheaf-hom`). Represent the germ by
   a morphism `φ` on an open neighbourhood `U` of `x` (`def-weil-pbc-module-stalk`).
3. The canonical map sends that representative germ to the induced stalk map `φ_x`
   (`lem-weil-pbc-stalk-internal-hom-finite-presentation`). Its value is `ψ` by
   construction. The restriction stalk isomorphisms identify this induced map
   with the displayed elementwise equality, yielding the required `U` and `φ`. -/
theorem exists_open_hom_of_coherent_stalk_map
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (x : X)
    (ψ : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G ⟶
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :
    ∃ (U : X.Opens) (hx : x ∈ U)
      (φ : (Scheme.Modules.restrictFunctor U.ι).obj G ⟶
        (Scheme.Modules.restrictFunctor U.ι).obj F),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G,
        ψ m =
          ConcreteCategory.hom ((Scheme.Modules.restrictStalkNatIso U.ι
            ((⟨x, hx⟩ : (U : Scheme)))).hom.app F)
            ((RingedSpace.moduleStalkFunctor (U : Scheme).toRingedSpace ⟨x, hx⟩).map φ
              (ConcreteCategory.hom ((Scheme.Modules.restrictStalkNatIso U.ι
                ((⟨x, hx⟩ : (U : Scheme)))).inv.app G) m)) := by
  sorry

end AlgebraicGeometry
