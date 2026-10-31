/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.FpqcClosedImmersionDescent
import WeilConjectures.FieldTheory.FamilyCommonExtensionFields
import WeilConjectures.AlgebraicGeometry.FppfSheafCoproductPartition
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.FpqcAffineDescent

/-! # Fppf descent of four algebraic-space morphism properties

Source: Stacks Project, Spaces Descent, Tags 041Z, 041U, 0427, 0421 and
Definition-property-morphisms-local; Morphisms of Spaces, Tags 03WI, 03XH, 03XL, 03KL
(blueprint: lem-sfb-space-four-property-fppf-descent).

The three conjuncts assert isomorphism invariance, arbitrary base-change stability and
fppf locality separately for every member of the four-property list.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Each of affine, finite type, quasi-finite and separated is invariant under arrow
isomorphisms, preserved by arbitrary base change and local for fppf target coverings.
Source: Stacks, Spaces Descent, Tags 041Z, 041U, 0427, 0421;
Morphisms of Spaces, Tags 03WI, 03XH, 03XL, 03KL
(blueprint: lem-sfb-space-four-property-fppf-descent).

Proof:
1. Quasi-compact scheme tests and quasi-compact space tests agree: pull back a
   quasi-compact surjective etale scheme atlas of the test space, then compose the
   quasi-compact atlas supplied by the scheme test. Representable etale scheme tests
   give etaleness and surjectivity of the composite. Affine tests suffice as well.
   Arbitrary base change preserves affine tests by pullback associativity, finite type
   by the stack finite-type calculus, and separatedness by the separated-fp composition
   node. A geometric fibre after base change is the original geometric fibre, proving
   preservation of finite geometric fibres and hence quasi-finiteness.
2. Over an affine scheme test T, the finite-affine-refinement node refines the fppf
   family to a flat surjection T' → T of affine schemes with T' a finite coproduct
   of affine V_j mapping to cover members. All iterated pullbacks agree on sections.
3. Under local affineness, each E_j = X ×_Y V_j is affine. The scheme coproduct of
   the E_j represents E' = X ×_Y T': decompose every test by the inverse images of
   the clopen summands V_j, then glue sections uniquely by the sheaf condition.
   The fppf-sheaf coproduct partition and scheme-coproduct-family nodes identify
   these descriptions, including the empty family. The finite-affine-coproduct
   spectrum node makes E' affine.
4. E' is quasi-affine, so the quasi-affine-affine descent node makes E = X ×_Y T
   a scheme. Fpqc descent of affine scheme morphisms makes E → T affine; since T
   is affine, E is affine. This proves affineness on every affine test.
5. Local finite type descends by the lft-smooth-fpqc locality node, and
   quasi-compactness by the quasicompact-fppf-local node. Step 1 identifies its
   convention with ours. Together these give finite type, independently of separation.
6. The relative diagonal is representable: its scheme test is the equality locus
   given by the representable absolute diagonal of X. Closed immersion can be checked
   on affine opens by the closed-immersion affine-cover criterion. Refine those tests
   by Step 2.
7. On each refined V_j the tested diagonal is a scheme test of the diagonal of the
   corresponding local map, hence a closed immersion. The refinement is fppf, hence
   fpqc, so fpqc descent of closed immersions proves the original scheme test closed.
   Thus every scheme test of the diagonal is closed, proving separatedness.
8. For quasi-finiteness, Step 5 gives finite type. Lift a geometric point Spec Ω → Y
   through a cover member after extending its field, and take an algebraic closure Λ
   of that extension. Its fibre has finitely many point classes. The map from this
   fibre to the Ω-fibre is surjective: represent a point by Spec K, amalgamate K and Λ
   over Ω by the family-common-extension-field node, and use the fibre product.
   The Ω-fibre is therefore a surjective image of a finite set.
9. Arrow isomorphisms identify all scheme tests, compatible etale charts, geometric
   fibre point classes and diagonal tests. They preserve quasi-compact etale atlases.
   Hence all four properties are invariant. An empty covering forces the target,
   then the source, empty; the empty affine scheme, chart tests, fibres and diagonal
   satisfy all four properties. No nonempty-index assumption is required. -/
theorem four_property_fppf_descent {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    (hP : P = @MapIsAffine S ∨ P = @MapIsFiniteType S ∨
      P = @MapIsQuasiFinite S ∨ P = @MapIsSeparated S) :
    (∀ {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) (f' : X' ⟶ Y')
      (eX : X ≅ X') (eY : Y ≅ Y'),
      f ≫ eY.hom = eX.hom ≫ f' → (P f ↔ P f')) ∧
    (∀ {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y),
      P f → P (enlargedFibreProductFst g f)) ∧
    (∀ {I : Type w} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (Yᵢ : I → AlgebraicSpace S) (g : ∀ i : I, Yᵢ i ⟶ Y),
      (∀ i : I, MapIsFlat (g i)) →
      (∀ i : I, MapIsLocallyOfFinitePresentation (g i)) →
      IsJointlySurjective (fun i : I ↦ (g i).hom.hom) →
      (P f ↔ ∀ i : I, P (enlargedFibreProductFst (g i) f))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
