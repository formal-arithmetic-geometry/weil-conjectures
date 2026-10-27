/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.RingTheory.RingHom.Flat

/-!
# Relative flatness through an etale diagram and a closed support

Source: Stacks Project, Flat Modules, Tag 057U, `lemma-devissage-flat`, the comparisons
(1) with (4), (4) with (2), and the first two stalk conditions
(blueprint: lem-trf-etale-closed-support-flatness).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness has the same neighbourhood and stalk conditions through an etale
source/base diagram and a closed support. The four equivalences express two independent
triples, without equating flatness at one point with flatness on a neighbourhood.

Source: Stacks Project, Flat Modules, Tag 057U, `lemma-devissage-flat`
(blueprint: lem-trf-etale-closed-support-flatness).

Proof:
1. The pullback `H = g^* F` is quasi-coherent by
   lem-weil-pbc-module-pullback-quasi-coherent. At each `w : U`, apply
   lem-trf-relative-flatness-source-cover to the flat morphism `g`, then
   lem-trf-etale-local-ring-flatness to `e` at `a w`. This compares `F` at `g w`
   with `H` at `w`. The equality `g ≫ f = a ≫ e` identifies the base scalar actions;
   no cartesian square is required.
2. Pulling an open neighbourhood back by `g` transfers neighbourhood flatness from `F`
   to `H`. Conversely, g is open by lem-weil-pbc-etale-morphism-open-map; the image of
   any suitable neighbourhood of `i z` is an open neighbourhood of `g (i z)`.
   Applying Step 1 to a lift of each point of this image transfers flatness back.
   Use the stalk characterization in def-pc-scheme-module-flat-over in both directions.
3. By lem-weil-pbc-closed-pushforward-stalks, the stalk of `i_* G` at `i q` is
   canonically isomorphic to `G_q`, linearly over the stalk ring of `U` through `i`.
   Apply def-pc-module-stalk-functor to the given isomorphism and restrict scalars
   through `a`. Functoriality identifies the resulting action on `G_q` with that
   through `i ≫ a`. Flatness is invariant under a linear isomorphism by the tensor
   injectivity characterization in def-weil-pbc-flat-ring-map. Off the closed image
   the stalk of `H` is zero and hence flat.
4. A neighbourhood of `i z` restricts to one of `z`. Conversely, the subspace topology
   in def-weil-closed-immersion writes every open neighbourhood `W` of `z` as
   `i⁻¹(V)` for an open `V` containing `i z`. Step 3 transfers flatness on the image;
   off the image the stalks are zero. The stalk characterization gives flatness on V.
5. Steps 2 and 4 give the neighbourhood equivalences. Step 1 at `i z` and Step 3 at
   `z` give the two stalk equivalences separately. No openness of a flat locus is used. -/
theorem etale_closed_support_flatness {X S U T Z : Scheme.{u}}
    (f : X ⟶ S) (a : U ⟶ T) (g : U ⟶ X) (e : T ⟶ S)
    (_hcomm : g ≫ f = a ≫ e) [Etale g] [Etale e]
    (i : Z ⟶ U) [IsClosedImmersion i]
    (F : X.Modules) (G : Z.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (_hiso : (tensorPullback g).obj F ≅ (pushforward i).obj G) (z : Z) :
    ((∃ V : X.Opens, g (i z) ∈ V ∧
        ((tensorPullback V.ι).obj F).IsFlatOver (V.ι ≫ f)) ↔
      (∃ V : U.Opens, i z ∈ V ∧
        ((tensorPullback V.ι).obj ((tensorPullback g).obj F)).IsFlatOver (V.ι ≫ a))) ∧
    ((∃ V : U.Opens, i z ∈ V ∧
        ((tensorPullback V.ι).obj ((tensorPullback g).obj F)).IsFlatOver (V.ι ≫ a)) ↔
      (∃ V : Z.Opens, z ∈ V ∧
        ((tensorPullback V.ι).obj G).IsFlatOver (V.ι ≫ (i ≫ a)))) ∧
    (Module.Flat (S.presheaf.stalk (f (g (i z))))
        ((ModuleCat.restrictScalars (f.stalkMap (g (i z))).hom).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g (i z))).obj F)) ↔
      Module.Flat (T.presheaf.stalk (a (i z)))
        ((ModuleCat.restrictScalars (a.stalkMap (i z)).hom).obj
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace (i z)).obj
            ((tensorPullback g).obj F)))) ∧
    (Module.Flat (T.presheaf.stalk (a (i z)))
        ((ModuleCat.restrictScalars (a.stalkMap (i z)).hom).obj
          ((RingedSpace.moduleStalkFunctor U.toRingedSpace (i z)).obj
            ((tensorPullback g).obj F))) ↔
      Module.Flat (T.presheaf.stalk ((i ≫ a) z))
        ((ModuleCat.restrictScalars ((i ≫ a).stalkMap z).hom).obj
          ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj G))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
