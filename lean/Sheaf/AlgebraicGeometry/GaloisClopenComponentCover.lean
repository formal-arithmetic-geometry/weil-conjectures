module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.FieldTheory.FieldTower
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Galois clopen component covers

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, 2.3 Step 2,
printed p.150; Stacks Project, Tags 03SF, 0BR4 and 02GL.
(blueprint: lem-sfb-galois-clopen-component-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Clopen irreducible components of a finite Galois scalar extension cover the integral
base by finite etale surjections. The canonical left action is specified by its projections;
its component stabilizers act by restriction and transitively on geometric lifts.
`IsPullback p q b ...` presents exactly the scalar extension, with its two projections.
The coproduct isomorphism is over `Spec Ω`, and all orbit equalities are equalities of
morphisms from `Spec Ω`, retaining the residue-field embeddings.

Source: ILO, Travaux de Gabber, Expose X, 2.3 Step 2, printed p.150;
Stacks Project, Tags 03SF, 0BR4 and 02GL.
(blueprint: lem-sfb-galois-clopen-component-cover)

Proof:
1. The field-spectrum map is finite by lem-weil-pbc-spec-finite-ring-map-finite,
   etale by lem-weil-pbc-finite-separable-extension-etale, and surjective since both
   spectra are singletons (def-weil-affine-spectrum). Base change by b preserves these
   properties, using lem-weil-pbc-finite-morphism-permanence,
   lem-weil-pbc-etale-scheme-base-change and lem-weil-pbc-surjective-base-change.
2. At a geometric point t, lem-galois-geometric-fibre identifies the fibre over Spec Ω
   with a finite coproduct of Spec Ω. Surjectivity after base change makes it nonempty.
   The fibre-product universal property identifies its Ω-sections with e-embeddings
   L into Ω, retaining the embeddings themselves rather than their prime kernels.
3. The pullback universal property defines the canonical automorphisms with scalar
   part Spec(g inverse); contravariance gives the left-action law. Under the embedding
   description this sends τ to τ composed with g inverse. By
   lem-sfb-normal-embeddings-automorphism-transitive this is transitive. Injectivity
   of τ makes the element g carrying one lift to another unique.
4. The base B is irreducible. Apply lem-sfb-finite-etale-clopen-restriction to every
   nonempty clopen component to get a finite etale surjection. Base change and
   lem-galois-geometric-fibre give a nonempty geometric fibre and an Ω-valued lift.
   This uses no normality, properness, Noetherian or finite-type assumption on B.
5. Automorphisms permute maximal irreducible subsets (def-weil-irreducible-components).
   Choose a geometric point of B via an algebraic closure of a point's residue field
   (def-weil-algebraic-closure, def-weil-geometric-point). Every component has a lift
   over it. Transitivity on lifts sends a lift in any component to one in any other;
   their components then intersect and hence coincide by disjointness.
6. For two lifts in one component the full-group element carrying one to the other
   stabilizes that component, since its translate intersects the original component.
   These stabilizing elements form a subgroup. Restrict their automorphisms to the
   induced open subscheme to obtain r; equality after its open inclusion is equality
   of morphisms into that subscheme. Thus its nonempty geometric fibres are single
   stabilizer orbits, equivalently the stated equality for every pair of lifts.
-/
theorem galois_clopen_component_cover
    (e L : Type u) [Field e] [Field L] [Algebra e L]
    [Module.Finite e L] [Algebra.IsSeparable e L] [Normal e L]
    (B : Scheme.{u}) [IsIntegral B] (b : B ⟶ Spec (.of e))
    (Y : Scheme.{u}) (p : Y ⟶ B) (q : Y ⟶ Spec (.of L))
    (hY : IsPullback p q b (Spec.map (CommRingCat.ofHom (algebraMap e L))))
    (I : Type v) [Finite I] (U : I → Y.Opens)
    (hcomp : ∀ i : I, (U i : Set Y) ∈ irreducibleComponents Y)
    (hclosed : ∀ i : I, IsClosed (U i : Set Y))
    (hdisjoint : Pairwise (fun i j : I ↦ Disjoint (U i) (U j)))
    (hcover : iSup U = ⊤) :
    ∃ a : (L ≃ₐ[e] L) →* Aut Y,
      (∀ g : L ≃ₐ[e] L,
        (a g).hom ≫ p = p ∧
        (a g).hom ≫ q = q ≫ Spec.map (CommRingCat.ofHom g.symm.toRingHom)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B),
        (∃ (J : Type u) (_ : Finite J) (_ : Nonempty J),
          Nonempty (Over.mk (pullback.snd p t) ≅
            Over.mk (Sigma.desc fun _ : J ↦ 𝟙 (Spec (.of Ω))))) ∧
        (∃ x : Spec (.of Ω) ⟶ Y, x ≫ p = t) ∧
        ∀ (x y : Spec (.of Ω) ⟶ Y), x ≫ p = t → y ≫ p = t →
          ∃! g : L ≃ₐ[e] L, x ≫ (a g).hom = y) ∧
      (∀ i j : I, ∃ g : L ≃ₐ[e] L,
        (a g).hom '' (U i : Set Y) = (U j : Set Y)) ∧
      ∀ i : I, ∃ (H : Subgroup (L ≃ₐ[e] L)) (r : H →* Aut (U i).toScheme),
        (∀ g : L ≃ₐ[e] L, g ∈ H ↔
          (a g).hom '' (U i : Set Y) = (U i : Set Y)) ∧
        (∀ h : H, (r h).hom ≫ (U i).ι = (U i).ι ≫ (a h.val).hom) ∧
        IsFinite ((U i).ι ≫ p) ∧ Etale ((U i).ι ≫ p) ∧ Surjective ((U i).ι ≫ p) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ B),
          (∃ x : Spec (.of Ω) ⟶ (U i).toScheme, x ≫ (U i).ι ≫ p = t) ∧
          ∀ (x y : Spec (.of Ω) ⟶ (U i).toScheme),
            x ≫ (U i).ι ≫ p = t → y ≫ (U i).ι ≫ p = t →
            ∃ h : H, x ≫ (r h).hom = y := by
  sorry

end AlgebraicGeometry
