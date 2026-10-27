module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import Sheaf.AlgebraicGeometry.SmoothAffineQuotientLift
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.RingTheory.BasisIffBasisQuotientOfNilpotent
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Extending a prescribed lift across a smooth affine open

Source: Stacks Project, Examples of Deformation Problems, Tag 0DZN,
`lemma-glueing-smooth`, second assertion with the first open smooth;
`situation-glueing`, `section-general`, and Formal Deformation Theory,
`definition-CLambda` (blueprint: lem-sfb-smooth-open-coefficient-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A prescribed lift on `V` extends across a smooth affine open `U`, with its
specified reduction. The coefficient rings need not contain a coefficient field.

Source: Stacks Project, Examples of Deformation Problems, Tag 0DZN,
`lemma-glueing-smooth`, second assertion for smooth `U`; `situation-glueing`
and Formal Deformation Theory, `definition-CLambda`
(blueprint: lem-sfb-smooth-open-coefficient-lift).

The residue isomorphisms are algebra isomorphisms over `Λ`. The equation
`hresidue` makes the map on the identified residue fields the identity.
The open `VY` is specified by its inverse image along the marked special fibre;
nilpotence makes this exactly the open denoted `Y_V` in the node.
The label of `V'` uses the special-fibre marking induced by `ι` and `α`.
The last equation expresses the prescribed compatibility using `γ.inv` and
projections: after the closed immersion into `Y'`, the inverse of the reduced
`γ` equals `e` followed by the inverse of `α`. This is equivalent to
`e ∘ γ_A = α|_V`, since closed immersions are monomorphisms.

Proof following the seven steps of the DAG node:
1. Artinian maximal ideals and the kernel of `φ` are nilpotent
   (lem-weil-pbc-artinian-local-noetherian-nilpotent). Reduction is a thickening
   and a homeomorphism on points (def-sbc-first-order-thickening). Hence all
   labelled opens are well defined. Restriction preserves flatness
   (def-weil-flat-morphism), and the thickening of the affine special fibre `U`
   is affine (lem-weil-pbc-thickening-affine-scheme).
2. Smoothness of `U` gives local finite presentation (lem-pc-smooth-flat), which
   ascends to its flat deformation (lem-sfb-flat-deformation-lfp). The smooth
   fibre criterion (lem-pc-smooth-characterization) makes this deformation smooth.
   Lift it to a smooth affine `A'`-scheme `L`, with the specified reduction
   (lem-sfb-smooth-affine-quotient-lift). It is flat (lem-pc-smooth-flat).
3. Take the opens `D` of `L` and `E` of `Z` labelled by `U ∩ V`. Reduction of
   opens is cartesian (lem-weil-pbc-open-immersion-base-change). Both opens are
   affine (lem-weil-pbc-thickening-affine-scheme) and flat
   (def-weil-flat-morphism). The smooth special fibre makes `E` smooth by
   lem-pc-smooth-flat, lem-sfb-flat-deformation-lfp, and
   lem-pc-smooth-characterization, without a finite-presentation assumption on `Z`.
4. The specified reductions identify `D_A` and `E_A`. Filter the nilpotent kernel
   by its powers: each successive extension is square zero. Formal smoothness
   lifts the specified map at each step, producing `h : D ⟶ E`
   (def-sbc-smooth-morphisms, def-sbc-formally-smooth).
5. The two coordinate rings are flat over `A'`
   (lem-weil-pbc-flat-morphism-affine-criterion). Lift a residue-field basis in
   the target ring and its image in the source ring. Both are bases over `A'`
   (lem-weil-pbc-local-artinian-basis-when-flat). Thus `h` is an isomorphism
   inducing exactly the prescribed overlap isomorphism, also for empty overlap.
6. Glue `L` and `Z` along `h` (lem-weil-pbc-glue-schemes). Their structure maps
   glue (lem-weil-pbc-scheme-morphism-gluing), and flatness is local
   (def-weil-flat-morphism). Reduce the open cover
   (lem-weil-pbc-open-immersion-base-change). The two specified reduction maps
   glue to `α`; the inverse maps also agree and glue, giving its inverse
   (lem-weil-pbc-scheme-morphism-gluing).
7. Under the marking induced by `ι` and `α`, the open copy of `Z` has label `V`.
   Invert that open-copy isomorphism to obtain `γ`. Its reduction satisfies the
   displayed equation because the restriction of `α` to this copy was `e`.
   Empty opens, disconnected schemes and arbitrary dimensions use the same argument.
-/
theorem exists_smooth_open_coefficient_lift
    (k : Type u) (Λ : Type v) (A' A : Type u) [Field k]
    [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ k] (ρΛ : IsLocalRing.ResidueField Λ ≃ₐ[Λ] k)
    [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra Λ A']
    [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Λ A]
    (ρ' : IsLocalRing.ResidueField A' ≃ₐ[Λ] k)
    (ρ : IsLocalRing.ResidueField A ≃ₐ[Λ] k)
    (φ : A' →ₐ[Λ] A) [IsLocalHom φ.toRingHom] (hφ : Function.Surjective φ)
    (hresidue : ∀ a : A', ρ (IsLocalRing.residue A (φ a)) =
      ρ' (IsLocalRing.residue A' a))
    (X : Scheme.{u}) (x : X ⟶ Spec (.of k)) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) [Smooth (U.ι ≫ x)] [Smooth ((U ⊓ V).ι ≫ x)]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of A)) [Flat y]
    (ι : pullback y
      (Spec.map (CommRingCat.ofHom (ρ.toRingHom.comp (IsLocalRing.residue A)))) ≅ X)
    (hι : ι.hom ≫ x =
      pullback.snd y (Spec.map (CommRingCat.ofHom (ρ.toRingHom.comp (IsLocalRing.residue A)))))
    (VY : Y.Opens)
    (hVY : (ι.inv ≫
      pullback.fst y (Spec.map (CommRingCat.ofHom (ρ.toRingHom.comp (IsLocalRing.residue A))))) ⁻¹ᵁ
        VY = V)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (.of A')) [Flat z]
    (e : pullback z (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≅ VY.toScheme)
    (he : e.hom ≫ VY.ι ≫ y = pullback.snd z (Spec.map (CommRingCat.ofHom φ.toRingHom))) :
    ∃ (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (.of A')), Flat y' ∧
      ∃ α : pullback y' (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≅ Y,
        α.hom ≫ y = pullback.snd y' (Spec.map (CommRingCat.ofHom φ.toRingHom)) ∧
        ∃ (V' : Y'.Opens) (γ : V'.toScheme ≅ Z),
          γ.hom ≫ z = V'.ι ≫ y' ∧
          (ι.inv ≫
            pullback.fst y
              (Spec.map (CommRingCat.ofHom (ρ.toRingHom.comp (IsLocalRing.residue A)))) ≫
            α.inv ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom φ.toRingHom))) ⁻¹ᵁ V' = V ∧
          pullback.fst z (Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫ γ.inv ≫ V'.ι =
            e.hom ≫ VY.ι ≫ α.inv ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  sorry

end AlgebraicGeometry
