/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge
import Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Ideal subobjects of finite affine pushforwards

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YQ, steps using
Tags 01YP, 089W and 01XB
(blueprint: lem-weil-pbc-finite-affine-pushforward-ideal-devissage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The ideal product in a finite pushforward from an affine scheme provides the
coherent, generically full, acyclic subobject required for coherent devissage.
No support or generic-point hypothesis is required: the full-stalk conclusion holds
at any point where the ideal has full stalk.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YQ, the paragraph
beginning "Let J be a quasi-coherent sheaf of ideals", using Tags 01YP, 089W and 01XB.
(blueprint: lem-weil-pbc-finite-affine-pushforward-ideal-devissage).

Proof:
Put G = f_*F and K = JG, constructed as the image of multiplication. Finite
pushforward preserves coherence (01Y6); on the locally Noetherian schemes X and Y,
coherent modules are quasi-coherent of finite type (01XZ). Tensor products and images
of quasi-coherent modules are quasi-coherent (01I8), so K is quasi-coherent. Its
inclusion into coherent G is monic, hence K is coherent (01Y0). Take G' to be the
subobject represented by this inclusion. The canonical underlying isomorphism
identifies its arrow with the inclusion of K.
Stalks commute with tensor products and images (01AG, 01CB). Thus the range of
K_x → G_x is J_x G_x. Surjectivity of J_x → O_X,x says J_x is the unit ideal,
so that range is all G_x. The underlying isomorphism gives surjectivity for G'.
By the affine projection formula for ideals (01YP), K is isomorphic to f_*L,
where L = (f^*J)F is quasi-coherent. The subobject equality in 01YP, together
with the image-of-monomorphism isomorphisms, gives this isomorphism of modules.
Affine-morphism cohomology comparison (089W) identifies H¹(X,f_*L) with
H¹(Y,L), which vanishes because Y is affine and L is quasi-coherent (01XB).
Transport zero cohomology along the two module isomorphisms to obtain H¹(X,G') = 0.
The argument also covers zero F, the empty scheme, and the unit ideal. -/
theorem finite_affine_pushforward_ideal_devissage
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsAffine Y]
    [IsLocallyNoetherian X] (F : Y.Modules)
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) (x : X)
    {J : X.Modules} (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf)
    [Mono ι] [J.IsQuasicoherent]
    (hι : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) :
    ∃ G' : Subobject ((pushforward f).obj F),
      RingedSpace.IsCoherent X.toRingedSpace (G' : X.Modules) ∧
      (∃ h : (G' : X.Modules) ⟶ idealModuleProduct ι ((pushforward f).obj F),
        G'.arrow = h ≫ idealModuleProductι ι ((pushforward f).obj F)) ∧
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map G'.arrow).hom ∧
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (G' : X.Modules)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
