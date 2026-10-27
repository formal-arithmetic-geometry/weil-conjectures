module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Descent of quasi-compact immersions over affine bases

Source: Stacks Project, Descent, Tag 02L8
(lemma-descending-property-quasi-compact-immersion), the singleton affine covering case
(blueprint: lem-sfb-scheme-qc-immersion-fpqc-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism that becomes a quasi-compact immersion after a flat surjective base change
between affine `S`-schemes is a quasi-compact immersion. The structure maps `sU`, `sV`
and their compatibility `_hp` record that `p` is an `S`-morphism. No Noetherian or
finite-presentation hypothesis is required.

Source: Stacks Project, Descent, Tag 02L8
(blueprint: lem-sfb-scheme-qc-immersion-fpqc-descent).

Proof:
1. Affine schemes are quasi-compact and quasi-separated
   (lem-weil-pbc-affine-scheme-qcqs), so `p` is quasi-compact by
   lem-weil-pbc-qcqs-morphism-permanence (1). The immersion after base change is separated
   by lem-weil-pbc-separated-cancellation (a). Apply lem-weil-pbc-fpqc-descend-quasi-compact
   and lem-weil-pbc-fpqc-descend-separated to descend quasi-compactness and separatedness.
2. Factor `f` through its scheme-theoretic image `Z` by lemma-nagata-scheme-image-ideal-qc.
   Its inclusion into affine `U` is closed, hence `Z` is affine
   (def-weil-closed-immersion). The map `a : X ⟶ Z` is quasi-compact by
   lem-weil-pbc-qcqs-morphism-permanence (2), (1), and separated by
   lem-weil-pbc-separated-cancellation (b), hence quasi-separated by
   lem-pc-separated-quasi-separated. The injection on structure sheaves gives that its
   scheme-theoretic image is all of `Z` (def-nagata-scheme-theoretic-image).
3. Put `Z' = Z ×_U V`. Its inclusion into `V` is closed by
   lem-weil-pbc-closed-immersion-base-change, so `Z'` is affine. Its projection to `Z`
   is flat and surjective by lem-weil-pbc-flat-morphism-base-change and
   lem-weil-pbc-surjective-base-change. Pullback associativity (def-pc-fibre-product)
   identifies the base change `b` of `a` with the factor of the given base change of `f`.
   The map `b` is quasi-compact by lem-weil-pbc-qcqs-morphism-permanence (3).
   Apply the dense case of lemma-nagata-dense-flat-pullback to see its image is all `Z'`;
   quasi-compactness identifies its kernel with the sheaf kernel, which is therefore zero.
4. On every affine open of `V`, injectivity for `b` makes the kernel of the composite
   equal the kernel of the closed inclusion of `Z'`. By lem-weil-pbc-scheme-image-qc-kernel
   (1), these are their scheme-image ideals. The affine description of closed immersions
   (def-weil-closed-immersion) identifies the two closed subschemes. Their factor maps
   agree by the monomorphism uniqueness in lem-weil-pbc-scheme-image-qc-kernel.
   Thus lemma-nagata-immersion-open-in-scheme-image makes `b` an open immersion.
5. Apply lem-galois-open-immersion-affine-descent to the flat surjective map `Z' ⟶ Z`:
   `a` is an open immersion. Both open and closed immersions are immersions by
   def-weil-closed-immersion (identity as the other factor). Their composite is an
   immersion by lem-weil-pbc-proper-fp-permanence (e). Combine with step 1.
-/
theorem quasiCompactImmersion_of_flat_surjective_affine_baseChange
    {S U V X : Scheme.{u}} [IsAffine U] [IsAffine V]
    (sU : U ⟶ S) (sV : V ⟶ S) (p : V ⟶ U) (_hp : p ≫ sU = sV)
    [Flat p] [Surjective p] (f : X ⟶ U)
    [QuasiCompact (pullback.snd f p)] [IsImmersion (pullback.snd f p)] :
    QuasiCompact f ∧ IsImmersion f := by
  sorry

end AlgebraicGeometry
