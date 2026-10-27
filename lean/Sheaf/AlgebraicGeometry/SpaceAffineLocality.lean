/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFourPropertyFppfDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Limits

/-! # Affine morphisms of algebraic spaces: locality and permanence

Source: Stacks Project, Morphisms of Spaces, Tags 03WG, 03WH, 03WI, 03KG and 03KM
(blueprint: lem-sfb-space-affine-locality).

The atlas criterion uses an actual representing pullback square and an affine scheme
projection. Base change is expressed on every cartesian square of sheaves, so includes
all algebraic-space base changes and all their isomorphic presentations. Quasi-compact
spaces are expressed by quasi-compact scheme atlases. Absolute quasi-separatedness uses
the existing affine-test criterion for the diagonal over Spec Z, not the diagonal over S.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affineness is equivalent to affineness over a surjective representable etale scheme
atlas. Affine maps are representable, stable under base change and composition,
quasi-compact and separated; they have scheme source over scheme targets and affine
source over affine targets, and preserve quasi-compact quasi-separated sources.
Source: Stacks Project, Morphisms of Spaces, Tags 03WG, 03WH, 03WI, 03KG and 03KM
(blueprint: lem-sfb-space-affine-locality).

Proof:
1. For affine-test recognition, cover any scheme test T by affine opens. Each pullback
   piece is affine by MapIsAffine. Its inclusion is representable open, since its scheme
   tests are the corresponding open subschemes. The fppf sheaf is a Zariski sheaf, so
   [lem-pc-schemes-criterion], using [def-trf-algebraic-space], glues the pieces to a
   scheme over T. Its map is affine on those opens [pqf-def-affine-morphism]. Conversely
   scheme affine maps satisfy affine tests by [lem-weil-pbc-affine-morphism-permanence].
   This also gives representability and both assertions for scheme targets.
2. Choose the atlas from [def-trf-algebraic-space]. The base-change part of
   [lem-sfb-space-four-property-fppf-descent] and step 1 give the forward atlas criterion.
   Conversely the given affine scheme projection satisfies affine tests by step 1.
   Its singleton atlas is fppf: scheme tests are etale, hence flat and locally of finite
   presentation by [def-weil-etale-morphism] and
   [lem-trf-space-representable-etale-scheme-tests]. The affine descent clause of
   [lem-sfb-space-four-property-fppf-descent] gives MapIsAffine of the original map.
3. For any cartesian square and any affine scheme mapping to its new target,
   [lem-trf-space-fibre-products-etale-covers] and transitivity identify its source
   pullback with the original affine test. This proves arbitrary base-change stability.
4. For a composite and an affine scheme test of its final target, the intermediate
   pullback is affine by the second map. Testing the first map on that affine scheme
   again gives an affine scheme. Transitivity of fibre products proves composition.
5. On the atlas of step 2 the scheme map is quasi-compact and separated by
   [lem-weil-pbc-affine-morphism-permanence]. Its affine tests are affine schemes,
   quasi-compact by [lem-weil-pbc-affine-scheme-qcqs], and tests of its diagonal are
   closed immersions by [lem-weil-pbc-closed-immersion-base-change]. Descend these
   properties by [lem-trf-space-qc-separated-etale-local].
6. Affine tests for quasi-compactness imply tests by any quasi-compact space C: by
   [lem-a1-space-etale-open-image] and [lem-sfb-qc-space-affine-etale-atlas], choose an
   affine surjective etale atlas U of C. The test over U has a quasi-compact scheme
   atlas. Its composite is a quasi-compact scheme atlas of the test over C, using
   [lem-trf-space-fibre-products-etale-covers] and
   [lem-trf-space-representable-etale-scheme-tests]. The converse includes affine
   schemes by [lem-weil-pbc-affine-scheme-qcqs]. Successive tests give base change
   and composition for quasi-compact maps. Apply the identity test of Y to get X qc.
7. For absolute quasi-separatedness, pass to Spec Z by
   [lem-sfb-space-change-base-to-integers], which preserves fibre products and atlases.
   The absolute diagonal of X factors as its relative diagonal followed by the base
   change of the absolute diagonal of Y. The latter is quasi-compact by step 6. The
   former has closed-immersion scheme tests by step 5; these are affine by
   [lem-weil-pbc-closed-immersion-integral-separated-uc], hence have affine and
   quasi-compact sources on affine tests by
   [lem-weil-pbc-affine-morphism-permanence] and [lem-weil-pbc-affine-scheme-qcqs].
   Step 6 makes their composite quasi-compact. The equivalent absolute affine-test
   criterion is IsAbsolutelyQuasiSeparated. -/
theorem affine_locality_and_permanence
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (MapIsAffine f ↔
      ∃ (V : Over S) (a : yoneda.obj V ⟶ Y.obj.obj),
        IsEtale a ∧ IsSurjective a ∧
          ∃ (U : Over S) (p : U ⟶ V) (q : yoneda.obj U ⟶ X.obj.obj),
            IsPullback q (yoneda.map p) f.hom.hom a ∧ IsAffineHom p.left) ∧
    (MapIsAffine f →
      IsRepresentable f.hom.hom ∧
      (∀ (X' Y' : AlgebraicSpace S) (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p.hom f'.hom f.hom g.hom → MapIsAffine f') ∧
      (∀ (Z : AlgebraicSpace S) (g : Y ⟶ Z), MapIsAffine g → MapIsAffine (f ≫ g)) ∧
      IsQuasiCompactPresheafMap f.hom.hom ∧ IsSeparatedPresheafMap f.hom.hom ∧
      (∀ (V : Over S), Nonempty (Y.obj.obj ≅ yoneda.obj V) →
        ∃ (U : Over S), Nonempty (X.obj.obj ≅ yoneda.obj U) ∧
          (IsAffine V.left → IsAffine U.left)) ∧
      ((∃ (V : Over S) (a : yoneda.obj V ⟶ Y.obj.obj),
          CompactSpace V.left ∧ IsEtale a ∧ IsSurjective a) →
        IsAbsolutelyQuasiSeparated Y →
          (∃ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj),
            CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a) ∧
          IsAbsolutelyQuasiSeparated X)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
