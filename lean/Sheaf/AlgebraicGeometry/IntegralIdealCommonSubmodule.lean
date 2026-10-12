/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism

/-! # A common submodule with generically vanishing cokernels

Source: Stacks Project, Cohomology of Schemes, Tag 01YH,
`lemma-property-irreducible`, proof, generic ideal inclusion and ideal intersection.
(blueprint: lem-pc-a2-integral-ideal-common-submodule)
-/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero ideal pushforward and a coherent module of generic rank one admit
monomorphisms from a common module, with coherent cokernels of strictly smaller support.
No filtration is asserted here.

Source: Stacks Project, Cohomology of Schemes, Tag 01YH,
`lemma-property-irreducible`, proof, paragraphs beginning "Let G" and "Next, suppose".
(blueprint: lem-pc-a2-integral-ideal-common-submodule)

Proof: The closed subscheme W of the Noetherian X is Noetherian. Every quasi-coherent
ideal on W is coherent, since its affine section modules are ideals in Noetherian
rings, and closed pushforward preserves coherence. The nonzero pushforward hypothesis
implies I is nonzero. Apply the coherent generic-point ideal inclusion to G. On the
generic stalk it identifies G with a finite sum of copies of the generic stalk of an
ideal J. G has dimension one over the residue field, so J is nonzero and the number
of summands is one. Thus obtain a monomorphism i_*J into G which is an isomorphism
near the generic point. The intersection L = I inf J is a quasi-coherent ideal. On
any nonempty affine open both ideals contain nonzero elements, whose product is
nonzero in the domain and belongs to L. Hence L is nonzero, and the generic stalks
of L, I and J are the full generic field. Set K = i_*L and take its inclusion into
i_*I and its inclusion into i_*J followed by the map into G. Both are monomorphisms.
Their sources and targets are coherent, so their cokernels are coherent and
finitely presented on the locally Noetherian scheme X. Exactness
of stalks and the generic stalk identifications make both cokernels zero at the image
of genericPoint W; outside i(W) all source and target stalks are zero. Each cokernel's
support is therefore contained in i(W) but omits its generic point, giving strict
inclusion. The argument also covers zero cokernels, whose supports are empty. -/
theorem exists_integral_ideal_common_submodule (X W : Scheme.{u})
    [IsNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (hGsupp : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hGann : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint W))),
      ∀ v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G, a • v = 0)
    (hGrank : ∃ inst : Module (X.residueField (i.base (genericPoint W)))
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G),
      (∀ (a : X.presheaf.stalk (i.base (genericPoint W)))
        (v : (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).obj G),
        a • v = (X.residue (i.base (genericPoint W))) a • v) ∧
      Module.finrank (X.residueField (i.base (genericPoint W)))
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint W))).obj G)
        = 1)
    (I : W.IdealSheafData) (hI : ¬ IsZero ((pushforward i).obj I.toModules)) :
    ∃ (K : X.Modules) (a : K ⟶ G) (d : K ⟶ (pushforward i).obj I.toModules),
      Mono a ∧ Mono d ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel a) ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel d) ∧
      (cokernel a).IsFinitePresentation ∧ (cokernel d).IsFinitePresentation ∧
      {x : X | ¬ Subsingleton ((cokernel a).presheaf.stalk x)} ⊂ Set.range i.base ∧
      {x : X | ¬ Subsingleton ((cokernel d).presheaf.stalk x)} ⊂ Set.range i.base := by sorry


end AlgebraicGeometry.Scheme.Modules
