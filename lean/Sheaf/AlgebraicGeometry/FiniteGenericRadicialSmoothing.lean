/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.GenericGeometricallyReducedPreparation
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import Sheaf.RingTheory.SingularIdeal
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Topology.IrreducibleOpenComplementDimension
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.RingTheory.SingularIdeal

/-! # Generic smoothing after a finite radicial base change

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-fin-generic-radicial-smoothing (blueprint: lem-fin-generic-radicial-smoothing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- After shrinking an integral finite type base over a field, a finite radicial
surjection makes the reduced pullback admit a dense smooth open. An optional
constructible finite sheaf becomes locally constant there. The parameter `none`
expresses the assertion without a sheaf, and `some F` its sheaf refinement.
The complement in the generic fibre is written using the subspace of points over
its generic point; `Scheme.Hom.fiberHomeo` identifies this with the scheme fibre.
Its components are compared with every containing component of the unreduced pullback.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
lem-fin-generic-radicial-smoothing (blueprint: lem-fin-generic-radicial-smoothing).

Proof:
1. Apply lem-pur-generic-geometrically-reduced-preparation (Stacks 0550).
The resulting finite universal homeomorphism is surjective and universally injective,
hence radicial by def-weil-radicial-morphism.
2. Apply lem-pur-geometrically-reduced-dense-smooth-open on the generic fibre.
Use lem-weil-pbc-flat-smooth-fibre-smooth-at-prime (00TF) and
def-weil-pbc-singular-ideal to lift its points to smooth open charts. Their union
is smooth by def-sbc-smooth-morphisms. Flat finite presentation makes the map open
(lem-weil-pbc-flat-lfp-open), so this union is dense in the total reduced pullback.
3. Finite type over the original field gives Noetherian affine rings by
lem-weil-pbc-finite-type-algebra-noetherian. Finite affine covers give Noetherian
spaces, and lem-weil-pbc-noetherian-finite-components gives finitely many components.
4. Pull back the optional sheaf using prop-constructible-pullback. The interiors of
its finite strata (def-constructible-constructible) contain every generic point.
On each interior the stratum immersion is a nilpotent closed immersion, hence a
universal homeomorphism. Use lemma-constructible-pullback-locally-constant and
lemma-constructible-universal-homeomorphism-invariance to descend local constancy.
Intersect their dense union with the smooth open. Without a sheaf keep the smooth open.
5. A component Z of the generic-fibre complement lies in the proper closed complement
of the open in every containing component C. By lem-kun-dimension-finite-type, C has
finite dimension. Apply new-node-irreducible-open-complement-dimension to C.
Chains in Z inject into chains of their closures in that complement, so dim Z < dim C.
The generic fibre has the subspace topology by def-pc-scheme-fibre, and reduction
preserves the underlying space by def-weil-pbc-scheme-reduction. Empty generic fibres
and empty complements give a vacuous dimension assertion. -/
theorem exists_finite_generic_radicial_smoothing
    (k : Type u) [Field k] (S : Scheme.{u}) [IsIntegral S]
    [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    [Nonempty X]
    (F : Option (Sheaf X.smallEtaleTopology (Type (u + 1))))
    (hF : ∀ E ∈ F, Scheme.IsConstructibleEtaleSheafOfSets E) :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      ∃ (T : Scheme.{u}) (q : T ⟶ U.toScheme),
        IsFinite q ∧ UniversallyInjective q ∧ Surjective q ∧
        ∃ V : (pullback f (q ≫ U.ι)).nilradical.subscheme.Opens,
          Dense (V : Set (pullback f (q ≫ U.ι)).nilradical.subscheme) ∧
          Smooth (V.ι ≫ (pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
            pullback.snd f (q ≫ U.ι)) ∧
          (∀ E ∈ F, Scheme.IsLocallyConstantEtaleSheafOfSets
            ((Scheme.etaleSetPullback
              (V.ι ≫ (pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
                pullback.fst f (q ≫ U.ι))).obj E)) ∧
          ∀ η : T, IsGenericPoint η Set.univ →
            ∀ Z : Set {y : (pullback f (q ≫ U.ι)).nilradical.subscheme |
              ((pullback f (q ≫ U.ι)).nilradical.subschemeι ≫
                pullback.snd f (q ≫ U.ι)) y = η ∧ y ∉ V},
              Z ∈ irreducibleComponents _ →
              ∀ (C : Set ↥(pullback f (q ≫ U.ι))),
                C ∈ irreducibleComponents ↥(pullback f (q ≫ U.ι)) →
                (∀ z ∈ Z, (pullback f (q ≫ U.ι)).nilradical.subschemeι z.1 ∈ C) →
                topologicalKrullDim Z < topologicalKrullDim C := by
  sorry

end AlgebraicGeometry
