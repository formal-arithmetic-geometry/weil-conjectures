module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GenericFlatness
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularClosedPointComponents
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.FinitePresentation

/-! # Geometry of smooth algebraic group orbits

Source: Milne, Algebraic Groups (2017), Propositions 1.65, 7.4--7.6,
Appendix A.11, A.14--A.15, A.71--A.73; Stacks Project, Tag 0B2L.
(blueprint: lem-sfb-smooth-algebraic-action-orbit-geometry)

The stabilizers are specified by their defining fibre squares. The orbits are specified
by reduced immersions and their vanishing ideals in every suitable open. Thus the
existential witnesses are determined up to their canonical isomorphisms over the ambient
scheme. No scheme or action is chosen from an unproved existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

namespace SmoothActionOrbit

variable {F : Type u} [Field F]
variable {G X : Over (Spec (.of F))} [GrpObj G] [ModObj G X]

/-- The orbit arrow `g ↦ g x`, using the given internal action.
Source: Milne, Algebraic Groups, §1(f), p.27 and §7(c), p.139.
(blueprint: lem-sfb-smooth-algebraic-action-orbit-geometry) -/
def orbitArrow (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) : G ⟶ X :=
  lift (𝟙 G) (toUnit G ≫ x) ≫ ModObj.smul (M := G) (X := X)

/-- The support of the orbit, the image of the entire underlying group scheme.
Source: Milne, Algebraic Groups, §7(c), p.139.
(blueprint: lem-sfb-smooth-algebraic-action-orbit-geometry) -/
def support (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) : Set X.left :=
  Set.range (orbitArrow (G := G) x).left

end SmoothActionOrbit

open SmoothActionOrbit

/-- Smooth algebraic group orbits, with their scheme-theoretic stabilizers.

Source: Milne, Algebraic Groups, Propositions 1.65(b),(c), 7.4(b), 7.5--7.6,
pp.27,139--140; Appendix A.11, A.14--A.15, A.71--A.73; Stacks Project, Tag 0B2L.
(blueprint: lem-sfb-smooth-algebraic-action-orbit-geometry)

Proof plan (the twelve steps of the DAG node):
1. Finite-type schemes over F are Noetherian; their opens are quasi-compact.
   Use lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-qc-open-immersion-finite-type and
   lem-weil-pbc-proper-fp-permanence. Composition and base change preserve finite type
   (lem-sfb-finite-type-composition-base-change). A map between these schemes is locally
   finite type by lemma-nagata-finite-type-to-separated-target; its affine maps are
   finitely presented by lem-weil-pbc-finite-type-noetherian-finite-presentation.
   Smooth G is reduced by sbc-lem-smooth-geometrically-reduced.
2. Detect nonempty locally closed subsets by F-points using
   lem-sc-lft-over-field-jacobson-space and lem-weil-pbc-closed-point-residue-field-base.
   An F-point is a closed immersion, so its pullback is a closed finite-type stabilizer
   (lem-weil-pbc-proper-fp-permanence). The action identities restrict its group law,
   making the closed immersion a homomorphism of group schemes (def-sc-group-scheme).
3. Chevalley (lem-weil-pbc-chevalley-constructible-image) makes the image constructible.
   Find a nonempty relatively open subset by lem-wf-affine-constructible-open. Its
   translates cover all closed points of the image, hence the image, proving local closure.
4. Form the reduced closure by lem-weil-pbc-reduced-induced-closed-subscheme, and its
   open on the orbit support. Factor the orbit map using
   lem-weil-pbc-reduced-source-factors-through-closed-subscheme and
   lem-weil-pbc-morphism-factors-through-open-subscheme. Vanishing ideals restrict
   compatibly, proving the canonical description in every suitable open.
5. The reduced orbit has finitely many components (lem-weil-pbc-noetherian-finite-components).
   Choose an integral affine open and apply lem-sbc-generic-flatness there. Translates
   cover all closed points, hence the orbit, and transport flatness everywhere.
6. Over perfect F, lem-kun-geometric-reduced-perfect makes the orbit geometrically reduced.
   Its dense smooth open (lem-pur-geometrically-reduced-dense-smooth-open) translates
   to cover all closed points. The orbit is therefore smooth; its orbit map need not be.
7. Products of G with the reduced orbit, closure and boundary are reduced by
   lem-sfb-flat-geometrically-reduced-pullback, lem-pc-smooth-flat and
   sbc-lem-smooth-geometrically-reduced. Closed-point detection and the two factorization
   lemmas in step 4 restrict the action; monomorphisms give its action identities.
8. Surjectivity survives extension by lem-weil-pbc-surjective-base-change. The two
   closed-point lemmas in step 2 lift every E-point to G(E). Multiplication by a lift h
   identifies the stabilizer base change with the geometric fibre; multiplication by
   h inverse is its inverse, as seen on every test scheme. This gives transitivity and
   the rational-point partition. Intersecting supports contain an F-point and agree.
9. The orbit is regular (lem-weil-pbc-smooth-scheme-over-field-regular). Its finitely
   many components are disjoint by lem-wf-smooth-components-disjoint, checked affine
   locally. Transitivity permutes them, so their finite dimensions agree
   (lem-kun-dimension-finite-type); finite-union dimension gives equidimensionality.
10. Apply lem-sbc-flat-composite-fibre-dimension-at-point at the identity and x.
    Use lem-ag-group-identity-local-dimension,
    lem-ag-rational-point-stalk-topological-local-dimension and
    lem-sbc-equidimensional-open-local-dimension to identify the three dimensions.
    They are finite by lem-kun-dimension-finite-type; hence dim G = dim G_x + dim O_x.
11. Component closures have the same dimensions by
    lem-weil-pbc-dense-open-dimension-comparison. The boundary in each is proper closed;
    append that component to any irreducible closed chain to get strict dimension drop.
    Finite-union dimension and subspace monotonicity bound every boundary orbit.
12. If G is connected, smooth regular G is integral by lem-sc-regular-connected-integral.
    Its continuous surjective image is irreducible.
-/
theorem smooth_algebraic_action_orbit_geometry
    {F : Type u} [Field F] [IsAlgClosed F]
    (G X : Over (Spec (.of F))) [GrpObj G] [ModObj G X]
    [Smooth G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ∃ (H O : (𝟙_ (Over (Spec (.of F))) ⟶ X) → Over (Spec (.of F)))
      (j : ∀ x, H x ⟶ G) (i : ∀ x, O x ⟶ X) (β : ∀ x, G ⟶ O x),
      (∀ x : 𝟙_ (Over (Spec (.of F))) ⟶ X,
        IsPullback (j x).left (H x).hom (orbitArrow (G := G) x).left x.left ∧
        (∃ (_ : GrpObj (H x)), IsMonHom (j x) ∧ IsClosedImmersion (j x).left) ∧
        LocallyOfFiniteType (H x).hom ∧ QuasiCompact (H x).hom ∧
        IsLocallyClosed (support (G := G) x) ∧
        IsImmersion (i x).left ∧ IsReduced (O x).left ∧
        Set.range (i x).left = support (G := G) x ∧
        (∀ (U : X.left.Opens) (_ : support (G := G) x ⊆ (U : Set X.left))
          (hc : IsClosed (U.ι ⁻¹' support (G := G) x)),
          ∃ f : (O x).left ⟶ U.toScheme,
            f ≫ U.ι = (i x).left ∧ IsClosedImmersion f ∧
            f.ker = Scheme.IdealSheafData.vanishingIdeal
              ⟨U.ι ⁻¹' support (G := G) x, hc⟩ ∧
            ∃! φ : (O x).left ≅ (Scheme.IdealSheafData.vanishingIdeal
                ⟨U.ι ⁻¹' support (G := G) x, hc⟩).subscheme,
              φ.hom ≫ (Scheme.IdealSheafData.vanishingIdeal
                ⟨U.ι ⁻¹' support (G := G) x, hc⟩).subschemeι = f) ∧
        Smooth (O x).hom ∧ LocallyOfFiniteType (O x).hom ∧ QuasiCompact (O x).hom ∧
        (∃ (_ : ModObj G (O x)), IsModHom G (i x)) ∧
        β x ≫ i x = orbitArrow (G := G) x ∧
        Flat (β x).left ∧ Surjective (β x).left ∧
        LocallyOfFinitePresentation (β x).left ∧
        (∀ (E : Type u) [Field E] [Algebra F E] [IsAlgClosed E]
          (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ O x),
          ∃ h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ G,
            h ≫ β x = y ∧
            ∃ φ : ((H x) ⊗ Over.mk
                (Spec.map (CommRingCat.ofHom (algebraMap F E)))).left ≅
                pullback (β x).left y.left,
              φ.hom ≫ pullback.fst (β x).left y.left =
                (((snd (H x) (Over.mk (Spec.map
                    (CommRingCat.ofHom (algebraMap F E))))) ≫ h) *
                  (fst (H x) (Over.mk (Spec.map
                    (CommRingCat.ofHom (algebraMap F E)))) ≫ j x)).left ∧
              φ.hom ≫ pullback.snd (β x).left y.left =
                (snd (H x) (Over.mk (Spec.map
                  (CommRingCat.ofHom (algebraMap F E))))).left) ∧
        (∀ (E : Type u) [Field E] [Algebra F E] [IsAlgClosed E]
          (y z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ O x),
          ∃ g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ G,
            g • (y ≫ i x) = z ≫ i x) ∧
        (∀ y : 𝟙_ (Over (Spec (.of F))) ⟶ X,
          (∃ z : 𝟙_ (Over (Spec (.of F))) ⟶ O x, z ≫ i x = y) ↔
            ∃ g : 𝟙_ (Over (Spec (.of F))) ⟶ G, g • x = y) ∧
        (∀ C ∈ irreducibleComponents (O x).left,
          topologicalKrullDim C = topologicalKrullDim (O x).left) ∧
        (∃ d e : ℕ,
          topologicalKrullDim (O x).left = (d : WithBot ℕ∞) ∧
          topologicalKrullDim (H x).left = (e : WithBot ℕ∞) ∧
          topologicalKrullDim G.left = ((d + e : ℕ) : WithBot ℕ∞)) ∧
        (∃ (Z B : Over (Spec (.of F))) (iz : Z ⟶ X) (ib : B ⟶ X),
          IsReduced Z.left ∧ IsReduced B.left ∧
          IsClosedImmersion iz.left ∧ IsClosedImmersion ib.left ∧
          Set.range iz.left = closure (support (G := G) x) ∧
          Set.range ib.left = closure (support (G := G) x) \ support (G := G) x ∧
          (∃ (_ : ModObj G Z), IsModHom G iz) ∧
          (∃ (_ : ModObj G B), IsModHom G ib)) ∧
        (∀ y : 𝟙_ (Over (Spec (.of F))) ⟶ X,
          support (G := G) y ⊆ closure (support (G := G) x) \ support (G := G) x →
            topologicalKrullDim (O y).left < topologicalKrullDim (O x).left) ∧
        (ConnectedSpace G.left → IrreducibleSpace (O x).left)) ∧
      (∀ y : 𝟙_ (Over (Spec (.of F))) ⟶ X,
        ∃ (x : 𝟙_ (Over (Spec (.of F))) ⟶ X)
          (z : 𝟙_ (Over (Spec (.of F))) ⟶ O x), z ≫ i x = y) ∧
      (∀ x y : 𝟙_ (Over (Spec (.of F))) ⟶ X,
        Set.range (fun z : 𝟙_ (Over (Spec (.of F))) ⟶ O x ↦ z ≫ i x) =
            Set.range (fun z : 𝟙_ (Over (Spec (.of F))) ⟶ O y ↦ z ≫ i y) ∨
          Disjoint (Set.range (fun z : 𝟙_ (Over (Spec (.of F))) ⟶ O x ↦ z ≫ i x))
            (Set.range (fun z : 𝟙_ (Over (Spec (.of F))) ⟶ O y ↦ z ≫ i y))) ∧
      (∀ x y : 𝟙_ (Over (Spec (.of F))) ⟶ X,
        support (G := G) x = support (G := G) y ∨
          Disjoint (support (G := G) x) (support (G := G) y)) := by
  sorry

end AlgebraicGeometry
