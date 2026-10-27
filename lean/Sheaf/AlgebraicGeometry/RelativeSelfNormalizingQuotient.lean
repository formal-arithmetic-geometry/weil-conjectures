module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.SpaceProperStrictLocalTest
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Quotients by smooth self-normalizing relative subgroups

Source: Conrad, Reductive group schemes, Theorem 2.3.6(1),(2), pp.72--75.
(blueprint: lem-sfb-relative-self-normalizing-quotient).

The right-coset presheaf is the pointwise coequalizer of projection and right
multiplication. After any base change its fppf sheafification is represented by
that same base change of the quotient scheme. Restriction along `Over.map t`
is the functor of points of the scheme pulled back along t, by the pullback
adjunction. The representing isomorphism is normalized by the quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- Right multiplication (g,h) ↦ g i(h), using the group on scheme-valued points.
Source: Conrad, Theorem 2.3.6, quotient relation, pp.72--73.
(blueprint: lem-sfb-relative-self-normalizing-quotient). -/
def relativeSubgroupRightTranslation {S : Scheme.{u}} {G H : Over S}
    [GrpObj G] (i : H ⟶ G) : G ⊗ H ⟶ G :=
  fst G H * (snd G H ≫ i)

/-- The actual right-coset presheaf after base change t. Colimits of set presheaves
are computed pointwise, so this coequalizer is G(W)/H(W) on every T-scheme W.
Source: Conrad, Theorem 2.3.6, pp.72--73; quotient sheaf construction.
(blueprint: lem-sfb-relative-self-normalizing-quotient). -/
def relativeSubgroupCosetPresheaf {S : Scheme.{u}} {G H : Over S}
    [GrpObj G] (i : H ⟶ G) {T : Scheme.{u}} (t : T ⟶ S) :
    (Over T)ᵒᵖ ⥤ Type (u + 1) :=
  coequalizer
    (Functor.whiskerLeft (Over.map t).op (uliftYoneda.{u + 1}.map (fst G H)))
    (Functor.whiskerLeft (Over.map t).op
      (uliftYoneda.{u + 1}.map (relativeSubgroupRightTranslation i)))

/-- The fppf sheafification of the right-coset presheaf after base change t.
Source: Conrad, Theorem 2.3.6, pp.72--73.
(blueprint: lem-sfb-relative-self-normalizing-quotient). -/
def relativeSubgroupFppfQuotient {S : Scheme.{u}} {G H : Over S}
    [GrpObj G] (i : H ⟶ G) {T : Scheme.{u}} (t : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over T) (Type (u + 1))).obj
    (relativeSubgroupCosetPresheaf i t)

/-- The coset projection followed by the sheafification unit, after base change t.
Source: Conrad, Theorem 2.3.6, pp.72--73.
(blueprint: lem-sfb-relative-self-normalizing-quotient). -/
def relativeSubgroupFppfQuotientMap {S : Scheme.{u}} {G H : Over S}
    [GrpObj G] (i : H ⟶ G) {T : Scheme.{u}} (t : T ⟶ S) :
    (Over.map t).op ⋙ uliftYoneda.{u + 1}.obj G ⟶
      (relativeSubgroupFppfQuotient i t).obj :=
  coequalizer.π _ _ ≫
    toSheafify (Scheme.fppfTopology.over T) (relativeSubgroupCosetPresheaf i t)

/-- A smooth connected self-normalizing closed subgroup has a smooth schematic
quotient. The projection is a smooth surjective right torsor. Its normalized
quotient isomorphism and its torsor relation persist after every base change.
Projectivity of the geometric quotient fibres implies properness.

Source: Conrad, Reductive group schemes, Theorem 2.3.6(1),(2), pp.72--75.
(blueprint: lem-sfb-relative-self-normalizing-quotient).

Proof:
1. Apply lem-sfb-free-flat-group-space-quotient to h.g = g h⁻¹, which is free.
   Smoothness makes H flat and locally finitely presented (lem-pc-smooth-flat).
   The quotient is an algebraic space with fppf local lifts and the torsor relation.
2. A lift a trivializes each scheme test by h ↦ ah, with inverse b ↦ a⁻¹b.
   Apply lem-sfb-space-smooth-surjective-fppf-locality to obtain smoothness of q,
   and lem-sfb-space-lft-smooth-fpqc-locality to obtain local finite type of Q/S.
3. Pulling back the diagonal to G ×_S G gives the inverse image of H under g⁻¹b.
   Use lem-sfb-space-fppf-covering-calculus and
   lem-sfb-space-closed-immersion-fppf-descent to descend its closed immersion.
   By lem-sfb-space-qcqs-source-products and lem-a1-space-point-open-calculus,
   the quotient is quasi-compact and quasi-separated.
4. On the affine opens of lem-sfb-finite-jet-normalizer-detection, the finite free
   coordinate quotient defines a Grassmannian point. The stabilizer of this point
   is the normalizer, hence H. Use lem-sfb-free-quotient-grassmann-projective
   for the Grassmannian. Sheafification gives a monomorphism Q → P, using
   lem-weil-pbc-site-sheafification-sections-local and
   lem-a1-algebraic-space-fpqc-sheaf with lem-trf-fppf-covering-is-fpqc.
5. Use lem-pc-projective-proper, lem-sfb-space-qcqs-source-products,
   lem-sfb-space-lft-cancellation and lem-sfb-space-qcqs-lft-mono-quasiaffine
   to make that monomorphism quasi-affine, so Q is a scheme locally on S.
   The representing schemes glue by lem-galois-glue; the sheaf isomorphisms glue too.
6. By lem-sbc-smooth-flat-surjective-source-descent, X/S is smooth. The projection
   is smooth and surjective by steps 1--2. Quasi-compactness, quasi-separatedness
   and local finite presentation give finite presentation, using
   lem-weil-pbc-qcqs-morphism-permanence.
7. After arbitrary base change, local lifts and the torsor relation still hold.
   The local equality criterion of lem-weil-pbc-site-sheafification-sections-local
   identifies the new quotient with X_T, compatibly with the projection.
8. Under fibre projectivity, lem-pc-projective-proper makes the geometric fibres
   proper. They are connected surjective images of the connected fibres of G.
   Use lem-sfb-space-proper-strict-local-test to reduce to the strict local base;
   lem-weil-pbc-strict-henselization-local-structure makes this base henselian.
   Smoothness and finite presentation persist, using the locality lemmas and
   lem-sfb-space-separated-fp-composition.
9. Descend properness of the closed fibre by lem-sfb-space-proper-fpqc-descent.
   Split it off as a proper clopen part by lem-sfb-scheme-henselian-proper-clopen-lift.
   This part surjects onto the local base: its image is closed and is open by
   lem-weil-pbc-smooth-restrict-open-subschemes, lem-pc-smooth-flat and
   lem-weil-pbc-flat-lfp-open. It is therefore a nonempty clopen subset of every
   connected geometric fibre, hence is the entire scheme. The strict-local test
   gives properness. This also covers nonreduced bases and the zero ring. -/
theorem exists_relative_self_normalizing_quotient
    (A : Type u) [CommRing A]
    (G H : Over (Spec (.of A))) [GrpObj G] [GrpObj H]
    [IsAffineHom G.hom] [Smooth G.hom] [LocallyOfFinitePresentation G.hom]
    [GeometricallyConnected G.hom]
    (i : H ⟶ G) [IsMonHom i] [IsClosedImmersion i.left]
    [LocallyOfFinitePresentation i.left] [Smooth H.hom] [GeometricallyConnected H.hom]
    (hself : ∀ (W : Over (Spec (.of A))) (g : W ⟶ G),
      (∀ (V : Over (Spec (.of A))) (a : V ⟶ W),
        Set.range (fun h : V ⟶ H ↦ (a ≫ g) * (h ≫ i) * (a ≫ g)⁻¹) =
          Set.range (fun h : V ⟶ H ↦ h ≫ i)) →
      ∃ h : W ⟶ H, h ≫ i = g) :
    ∃ (X : Over (Spec (.of A))) (q : G ⟶ X),
      Smooth X.hom ∧ Smooth q.left ∧ Surjective q.left ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ Spec (.of A)),
        ∃ e : (Over.map t).op ⋙ uliftYoneda.{u + 1}.obj X ≅
            (relativeSubgroupFppfQuotient i t).obj,
          Functor.whiskerLeft (Over.map t).op (uliftYoneda.{u + 1}.map q) ≫ e.hom =
            relativeSubgroupFppfQuotientMap i t) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ Spec (.of A)),
        IsPullback ((Over.pullback t).map (fst G H))
          ((Over.pullback t).map (relativeSubgroupRightTranslation i))
          ((Over.pullback t).map q) ((Over.pullback t).map q)) ∧
      ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of A)),
        ∃ (n : ℕ) (j : ((Over.pullback t).obj X).left ⟶
            ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of Ω))),
          IsClosedImmersion j ∧
            j ≫ (ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of Ω)) ↘
              Spec (.of Ω)) = ((Over.pullback t).obj X).hom) → IsProper X.hom) := by
  sorry

end AlgebraicGeometry
