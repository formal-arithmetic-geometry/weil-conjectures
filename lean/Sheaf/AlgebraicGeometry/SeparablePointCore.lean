module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.RingTheory.SmoothAtGenericPointOverField
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Sheaf.RingTheory.GeometricallyReducedBaseChange

/-!
# The closed subscheme carrying the separable points

Source: Conrad, Finiteness theorems for algebraic groups over function fields,
Lemma 3.1.1, printed p. 15 (blueprint: lem-sfb-separable-point-scheme-core).

The ideal is constructed as the vanishing ideal of the closure of the images of
all points over the absolute separable closure. Thus the construction has actual
data, including when there are no such points. Equality of ideals expresses equality
as closed subschemes, rather than an unspecified abstract isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The ideal of the closure of the separable-closure points, with its reduced
induced structure. Source: Conrad, Lemma 3.1.1; construction in the node's proof,
step 2 (blueprint: lem-sfb-separable-point-scheme-core). -/
noncomputable def separablePointCoreIdeal (X : Over (Spec (.of k))) : X.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure {x | ∃ t : Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))) ⟶ X,
      x ∈ Set.range t.left}, isClosed_closure⟩

/-- The reduced induced closed subscheme on the closure of the separable points,
regarded as a scheme over the original field. Source: Conrad, Lemma 3.1.1,
node proof step 2 (blueprint: lem-sfb-separable-point-scheme-core). -/
noncomputable def separablePointCore (X : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk ((separablePointCoreIdeal X).subschemeι ≫ X.hom)

/-- The canonical inclusion of the separable-point core. Source: Conrad,
Lemma 3.1.1 (blueprint: lem-sfb-separable-point-scheme-core). -/
noncomputable def separablePointCoreι (X : Over (Spec (.of k))) : separablePointCore X ⟶ X :=
  Over.homMk (separablePointCoreIdeal X).subschemeι rfl

/-- Existence and uniqueness of the geometrically reduced closed subscheme with
all separable-field points. Source: Conrad, Lemma 3.1.1
(blueprint: lem-sfb-separable-point-scheme-core).

Proof: step 1 describes affine closed immersions by quotients and proves they
are monomorphisms. Step 2 takes the reduced induced closed subscheme on the closure
of the separable-closure points; the universal-density node makes it geometrically
reduced. In step 3 a point over any separable extension factors through a smooth
affine model of its finitely generated image field, using smoothness at the generic
point. Dense finite separable points of this smooth model lie in the defining
closure, so reduced-source factorization gives the required point lift. Closed
immersions give uniqueness of lifts. In step 4 another candidate has dense smooth
locus and dense separable points there, so it has exactly the same support.
Uniqueness of the reduced induced closed subscheme gives equality of its ideal. -/
theorem separablePointCore_spec (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    IsClosedImmersion (separablePointCoreι X).left ∧
    GeometricallyReduced (separablePointCore X).hom ∧
    (∀ (L : Type u) [Field L] [Algebra k L], Algebra.IsSeparableExtension k L →
      Function.Bijective (fun t : Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ separablePointCore X ↦
        t ≫ separablePointCoreι X)) ∧
    (∀ I : X.left.IdealSheafData,
      GeometricallyReduced (I.subschemeι ≫ X.hom) →
      (∀ (L : Type u) [Field L] [Algebra k L], Algebra.IsSeparableExtension k L →
        Function.Bijective (fun t : Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
            Over.mk (I.subschemeι ≫ X.hom) ↦
          t ≫ Over.homMk I.subschemeι rfl)) →
      I = separablePointCoreIdeal X) := by
  sorry

/-- Every morphism restricts uniquely to the cores. Source: Conrad, Lemma 3.1.1
(blueprint: lem-sfb-separable-point-scheme-core).

Proof (step 5): composition carries separable-closure points to separable-closure
points. The inverse image of the target's closed support therefore contains the
closure of all such source points. The source core is reduced, so reduced-source
factorization gives the lift; the target closed immersion is mono, giving uniqueness. -/
theorem existsUnique_separablePointCoreMap {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) :
    ∃! g : separablePointCore X ⟶ separablePointCore Y,
      g ≫ separablePointCoreι Y = separablePointCoreι X ≫ f := by
  sorry

/-- The unique restriction of a morphism to the cores. This choice is determined
by its factorization equation, not by mere existence of an unspecified object.
Source: Conrad, Lemma 3.1.1 (blueprint: lem-sfb-separable-point-scheme-core). -/
noncomputable def separablePointCoreMap {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y) :
    separablePointCore X ⟶ separablePointCore Y :=
  Classical.choose (existsUnique_separablePointCoreMap f)

/-- Restrictions satisfy their factorization equation and the identity and
composition laws. Source: Conrad, Lemma 3.1.1
(blueprint: lem-sfb-separable-point-scheme-core).

Proof (step 5): the chosen lift has its defining equation by construction.
The identity satisfies the equation for an identity map, and the composite of two
lifts satisfies it for the composite. Uniqueness of each lift gives both laws. -/
theorem separablePointCoreMap_laws (X Y Z : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) :
    separablePointCoreMap f ≫ separablePointCoreι Y = separablePointCoreι X ≫ f ∧
    separablePointCoreMap (𝟙 X) = 𝟙 (separablePointCore X) ∧
    separablePointCoreMap (f ≫ g) = separablePointCoreMap f ≫ separablePointCoreMap g := by
  sorry

/-- The core commutes with every finite product, including the empty product,
as an equality of closed-subscheme ideals. Source: Conrad, Lemma 3.1.1
(blueprint: lem-sfb-separable-point-scheme-core).

Proof (step 6): affine charts of a product have tensor-product coordinate rings.
The tensor product of a geometrically reduced algebra with a reduced algebra is
reduced, also after arbitrary field extension. Thus the product of the cores is
geometrically reduced. Its separable-field points equal those of the product by
the product universal property. Uniqueness identifies its ideal with that of the
core. The product ideal is the sum of the ideals pulled back by the projections.
For the empty product the ideal is zero and the product is Spec k. -/
theorem separablePointCore_finiteProduct (J : Type u) [Finite J]
    (X : J → Over (Spec (.of k)))
    [∀ j, LocallyOfFiniteType (X j).hom] [∀ j, QuasiCompact (X j).hom] :
    separablePointCoreIdeal (∏ᶜ X) =
      ⨆ j, (separablePointCoreIdeal (X j)).comap (Pi.π X j).left := by
  sorry

/-- The core commutes with every separable extension of the base field, including
transcendental ones, as closed subschemes. Source: Conrad, Lemma 3.1.1
(blueprint: lem-sfb-separable-point-scheme-core).

Proof (step 7): base change of the core is geometrically reduced. If L/K and K/k
are separable, their composite is separable by the general transitivity node.
The pullback universal property therefore gives exactly the L-points of X_K.
Uniqueness over K identifies the ideals. Pulling back the ideal is precisely the
closed-subscheme base change. -/
theorem separablePointCore_baseChange (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (K : Type u) [Field K] [Algebra k K] (hK : Algebra.IsSeparableExtension k K) :
    separablePointCoreIdeal
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj X) =
      (separablePointCoreIdeal X).comap
        (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

/-- A geometrically reduced scheme is its own core. Source: Conrad, Lemma 3.1.1,
uniqueness, node proof step 4 (blueprint: lem-sfb-separable-point-scheme-core).

Proof: the identity closed subscheme already has all the required points and is
geometrically reduced. Uniqueness gives its zero ideal as the core ideal. -/
theorem separablePointCoreIdeal_eq_bot (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [GeometricallyReduced X.hom] :
    separablePointCoreIdeal X = ⊥ := by
  sorry

/-- The core of an affine group scheme is an affine closed subgroup scheme.
Its geometric reducedness is included in `separablePointCore_spec`.
Source: Conrad, Lemma 3.1.1 (blueprint: lem-sfb-separable-point-scheme-core).

Proof (step 8): restrict multiplication, inverse and identity by functoriality.
Product compatibility identifies the source of multiplication with the product of
cores, and the nullary product identifies the source of the unit with Spec k.
After composition with the inclusion the group diagrams are those of G; cancel
the monomorphism to prove all group laws. The inclusion preserves the operations
and is injective on all algebra-valued points, hence is a closed subgroup scheme.
The affine quotient description of a closed immersion proves affineness. -/
theorem separablePointCore_closedSubgroup (G : Over (Spec (.of k)))
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsAffine G.left] [GrpObj G] :
    ∃ s : GrpObj (separablePointCore G),
      @IsClosedSubgroupScheme k _ (separablePointCore G) G s inferInstance
        (separablePointCoreι G) ∧ IsAffine (separablePointCore G).left := by
  sorry

end AlgebraicGeometry
