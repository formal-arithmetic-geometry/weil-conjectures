/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion
import Sheaf.RingTheory.QuasiFiniteComposition
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Proper locally quasi-finite stack morphisms

Source: Stacks Project, stacks-morphisms.tex, Tags 0CL7, 06UD, 06UF, 04YS and
06UA; spaces-morphisms.tex, Tag 03XJ
(blueprint: lem-sfb-stack-proper-locally-quasifinite-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄ v₅ w₅

open AlgebraicGeometry

namespace CategoryTheory

/-- Composition preserves properness and local quasi-finiteness of DM stack maps.
No representability, surjectivity or quasi-compactness of a chart is assumed.
Source: Stacks, Tags 0CL7 and 06UD
(blueprint: lem-sfb-stack-proper-locally-quasifinite-composition).

Proof: Step 1 uses lem-a1-scheme-lqf-affine-criterion and
lem-trf-quasi-finite-composition to compose locally quasi-finite scheme maps.
Step 2 uses lem-sfb-stack-finite-type-calculus and
lem-sfb-stack-separation-composition for finite type and proper relative diagonal.
Step 3 identifies the two iterated base changes by associativity of 2-fibre
products. Composing the two closed point maps proves universal closedness.
Steps 4 and 5 use lem-sfb-dm-etale-atlas-calculus to choose compatible étale
atlases W, V, U and lem-sfb-dm-lqf-atlas-test to make V → W and U → V locally
quasi-finite. Step 1 makes U → W locally quasi-finite; the reverse atlas test
then gives the intrinsic local quasi-finiteness of the composite, including
its diagonal and discrete-field-fibre conditions. -/
theorem proper_locallyQuasiFinite_moduli_comp {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)}
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (hC : IsDeligneMumfordModuliStack C) (f : BasedFunctor A B) (g : BasedFunctor B C)
    (hf : IsProperModuliMap f) (hg : IsProperModuliMap g)
    (hfq : IsLocallyQuasiFiniteModuliMap f) (hgq : IsLocallyQuasiFiniteModuliMap g) :
    IsProperModuliMap (f.comp g) ∧ IsLocallyQuasiFiniteModuliMap (f.comp g) := by
  sorry

/-- The intrinsic stack properties on discrete algebraic spaces are exactly
ordinary properness and chartwise local quasi-finiteness. Properness forces the
relative diagonal to be a closed immersion after every scheme base change.
Source: Stacks, Tags 0CL5, 04YS, 06UA and 06UF; Spaces, Tag 03XJ
(blueprint: lem-sfb-stack-proper-locally-quasifinite-composition).

Proof: Step 6 uses lem-trf-space-fibre-products-etale-covers to see that maps of
spaces are representable by spaces. The finite-type calculus identifies finite
type, lem-sfb-representable-stack-diagonal-criterion identifies proper diagonal
with a closed-immersion diagonal, and
lem-sfb-representable-stack-universally-closed-test identifies universal
closedness. Step 7 applies the forward DM atlas test to every pair of compatible
étale charts. Conversely choose a target atlas and an atlas of its pullback;
lem-sfb-dm-etale-atlas-calculus and the reverse atlas test give intrinsic local
quasi-finiteness. This applies also to nonsurjective charts. -/
theorem proper_locallyQuasiFinite_discrete_space {S : Scheme.{u}}
    {E F : AlgebraicSpace S} (f : E ⟶ F) :
    (IsProperModuliMap (discreteModuliMap f.hom.hom) ↔ SpaceMapIsProper f) ∧
    (IsLocallyQuasiFiniteModuliMap (discreteModuliMap f.hom.hom) ↔
      SpaceMapIsLocallyQuasiFinite f) ∧
    (IsProperModuliMap (discreteModuliMap f.hom.hom) →
      ModuliSchemeTest @IsClosedImmersion
        (moduliRelativeDiagonal (discreteModuliMap f.hom.hom))) := by
  sorry

/-- For a scheme target every étale scheme chart has locally quasi-finite
composite, even when the chart is not surjective.
Source: Stacks, Tag 06UF and Spaces, Tag 040Z
(blueprint: lem-sfb-stack-proper-locally-quasifinite-composition).

Proof: Step 7 takes the target scheme's identity as its étale chart. The forward
atlas test for the map from the discrete algebraic space gives local
quasi-finiteness of the composite with each source chart. -/
theorem locallyQuasiFinite_space_chart_to_scheme {S : Scheme.{u}}
    (E : AlgebraicSpace S) (T : Over S) (f : E.obj.obj ⟶ yoneda.obj T)
    (hf : IsLocallyQuasiFiniteModuliMap (discreteModuliMap f))
    (U : Over S) (a : yoneda.obj U ⟶ E.obj.obj) (ha : AlgebraicSpace.IsEtale a) :
    Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ f)).left := by
  sorry

/-- The stack definitions recover the recorded proper and locally quasi-finite
scheme definitions on representable discrete stacks.
Source: Stacks, Tags 0CL5, 06UA and 06UF; Morphisms, Tag 01TD
(blueprint: lem-sfb-stack-proper-locally-quasifinite-composition).

Proof: Apply the representable compatibility argument of steps 6 and 7 to the
scheme morphism. Every scheme base change is its usual scheme fibre product.
Properness has the recorded separated, finite-type and universally-closed
clauses; the atlas criterion for local quasi-finiteness specializes to the
scheme condition using the identity charts. -/
theorem proper_locallyQuasiFinite_discrete_scheme {S : Scheme.{u}}
    {U V : Over S} (f : U ⟶ V) :
    (IsProperModuliMap (discreteModuliMap (yoneda.map f)) ↔ IsProper f.left) ∧
    (IsLocallyQuasiFiniteModuliMap (discreteModuliMap (yoneda.map f)) ↔
      Scheme.Hom.IsLocallyQuasiFinite f.left) := by
  sorry

/-- The two intrinsic properties are invariant under equivalences of source and
target and a 2-isomorphism of the resulting square. Identity equivalences cover
replacement by a 2-isomorphic morphism.
Source: Stacks, Tags 0CL5 and 06PU, definitions on point spaces and 2-fibre products
(blueprint: lem-sfb-stack-proper-locally-quasifinite-composition).

Proof: Step 8 replaces a comparison in a 2-fibre-product triple by its composite
with the given 2-isomorphism. Quasi-inverses of the equivalences give inverse
equivalences on all base changes, relative diagonals and field fibres. Transport
atlases along them. Field-point quotients and atlas-detected closed subsets
correspond. Thus finite type, quasi-compactness, universal closedness, the
proper or locally quasi-finite diagonal, and discrete field fibres agree. -/
theorem proper_locallyQuasiFinite_moduli_equivalence {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {A' : BasedCategory.{v₄, w₄} (Over S)} {B' : BasedCategory.{v₅, w₅} (Over S)}
    (hA : IsDeligneMumfordModuliStack A) (hB : IsDeligneMumfordModuliStack B)
    (f : BasedFunctor A B) (f' : BasedFunctor A' B')
    (e : BasedFunctor A A') (d : BasedFunctor B B')
    (he : e.toFunctor.IsEquivalence) (hd : d.toFunctor.IsEquivalence)
    (h : Nonempty (ModuliTwoIso (e.comp f') (f.comp d))) :
    (IsProperModuliMap f ↔ IsProperModuliMap f') ∧
    (IsLocallyQuasiFiniteModuliMap f ↔ IsLocallyQuasiFiniteModuliMap f') := by
  sorry

end CategoryTheory
