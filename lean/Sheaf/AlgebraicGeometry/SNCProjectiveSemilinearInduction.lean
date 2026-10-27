module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Sober
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.HProjectivePermanence
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.TraceFormula.SmoothGeometricallyNormal

/-!
# Smooth SNC and projectivity under finite semilinear induction

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X 2.3 Step 2,
diagram (2.b), printed pp. 150--151; relative SNC definition on p. 149.
(blueprint: lem-sfb-snc-projective-semilinear-induction)

The induced schemes are specified by their coset coproduct universal property and
the translate, scalar and action equations, as in the project's common-field induction
interface. Thus the assertion applies to every realization of the contracted products.
The total scheme and its morphisms are the chosen categorical coproduct and coproduct
maps. The ideal C is specified by its restrictions to the disjoint open summands.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite semilinear induction preserves smooth projective pairs, and its invariant map
is surjective and projective in both conventions.

Source: ILO, Expose X 2.3 Step 2, diagram (2.b), pp. 150--151, and the relative
strict normal crossings definition, p. 149.
(blueprint: lem-sfb-snc-projective-semilinear-induction)

Here d is the diagonal action on W_i = S_i x_{F_i} K, characterized by its two
projections. The maps t i g represent [g,-]. The coset-representative cocone is a
coproduct, hrelation specifies (g gamma,w) = (g,gamma w), hscalar specifies the
scalar twist, and hleft specifies left multiplication. The maps fY i are the unique
maps with hmap; the total h is Sigma.desc (fun i ↦ fY i ≫ Sigma.ι B i).
No separability, nonempty boundary, or common dimension is required.

Proof (the eight steps of the node):
1. Choose coset representatives, with 1 for the identity coset. The defining relation
   identifies each summand with W_i and twists its scalar map by the corresponding
   automorphism of K. Invariance of v_i makes the maps to B_i independent of the
   representative. The fibre-product universal property identifies each scalar twist
   with base change along an automorphism. This constructs the invariant map h.
2. Projectivity makes S_i proper and finite type. Apply
   lem-sfb-relative-snc-field-extension to D_i and K/F_i, and then to every scalar
   twist. Each summand is smooth with relative SNC boundary. Smoothness of their
   finite coproduct follows from lem-weil-pbc-smooth-coproduct. By
   lem-trf-smooth-geometrically-normal smooth schemes over a field are geometrically
   reduced; the trivial extension gives reducedness.
3. Locally write I for the ideal of v_i^{-1} C_i and J = radical I. Under any scalar
   extension their extended ideals have the same radical: each element of J has a
   power in I. The scalar extension of D_i is reduced by
   lem-sfb-relative-snc-field-extension, so its ideal equals that radical. Thus this
   is the reduced inverse image of C_i on each coset copy. Cartier ideals glue on
   disjoint open summands. Components in different summands have empty intersection;
   within one summand the same lemma gives smooth intersections and their pure
   codimensions, including the empty family, whose intersection is the ambient scheme.
4. Base change a finite projective-space embedding of S_i using
   lem-weil-pbc-closed-immersion-base-change and
   lemma-nagata-projective-space-base-change-pullback. Repeat along the scalar
   automorphisms to embed every coset summand into a finite projective space over K.
5. Put these embeddings in disjoint coordinate blocks of one projective space,
   with N+1 the sum of the numbers of coordinates. Different blocks are disjoint,
   since a projective point cannot have all coordinates zero. On each standard
   affine chart only its own block meets the image; there the map is the given
   closed immersion followed by setting the other coordinates to zero. Thus the
   finite coproduct has a closed immersion, with no dimension equality assumption.
6. Spec K to Spec e is finite, hence projective in the bundle convention by
   lem-trf-finite-projective-bundle. The structure sheaf on Spec e is ample (the
   section 1 has affine nonvanishing locus the entire scheme). By
   lem-trf-projective-bundle-to-h-projective the finite map is H-projective.
   Compose with Y to Spec K by lem-trf-h-projective-composition.
7. Repeated use of lem-weil-pbc-proper-coproduct makes B proper, hence separated
   over e. Apply lem-per-h-projective-permanence to the graph of h and the embedding
   of Y over e: (j,h) embeds Y into P^M_e x_e B = P^M_B. The identification with
   the projective bundle of the finite free module, supplied by
   lem-trf-free-projective-bundle-base-change-space, gives bundle projectivity too.
8. Spec K to Spec F_i is surjective. By lem-weil-pbc-surjective-base-change,
   W_i to S_i is surjective. The identity-coset copy therefore covers B_i under
   the composite with v_i. All B_i cover B, proving surjectivity of h.
-/
theorem snc_projective_semilinear_induction
    (e : Type u) [Field e] (I : Type w) [Finite I] [Nonempty I]
    (B S : I → Scheme.{u}) (b : ∀ i, B i ⟶ Spec (.of e))
    [∀ i, IsIntegral (B i)] [∀ i, IsProper (b i)]
    (C : (∐ B).IdealSheafData) (Ci : ∀ i, (B i).IdealSheafData)
    (hC : ∀ i, C.comap (Sigma.ι B i) = Ci i) (hCi : ∀ i, (Ci i).IsInvertible)
    (F : I → Type u) [∀ i, Field (F i)] [∀ i, Algebra e (F i)]
    [∀ i, Module.Finite e (F i)]
    (J : I → Type v) [∀ i, Group (J i)] [∀ i, Finite (J i)]
    (rho : ∀ i, J i →* (F i ≃ₐ[e] F i))
    (p : ∀ i, S i ⟶ Spec (.of (F i)))
    [∀ i, IsIntegral (S i)] [∀ i, Smooth (p i)] [∀ i, IsHProjective (p i)]
    (a : ∀ i, J i →* Aut (S i))
    (ha : ∀ (i : I) (j : J i), (a i j).hom ≫ p i =
      p i ≫ Spec.map (CommRingCat.ofHom (rho i j⁻¹).toRingHom))
    (vS : ∀ i, S i ⟶ B i) [∀ i, Surjective (vS i)]
    (hbase : ∀ i, vS i ≫ b i =
      p i ≫ Spec.map (CommRingCat.ofHom (algebraMap e (F i))))
    (hinvariant : ∀ (i : I) (j : J i), (a i j).hom ≫ vS i = vS i)
    (hgeneric : ∀ i, vS i (genericPoint (S i)) = genericPoint (B i))
    (hfinite : ∀ i, ((vS i).residueFieldMap (genericPoint (S i))).hom.Finite)
    (hD : ∀ i, ((Ci i).comap (vS i)).radical.IsSmoothStrictNormalCrossingsDivisor (p i))
    (K : Type u) [Field K] [Algebra e K] [Module.Finite e K] [Normal e K]
    (emb : ∀ i, F i →ₐ[e] K)
    (G : Type t) [Group G] [Finite G] (pi : G →* (K ≃ₐ[e] K))
    (Gamma : I → Subgroup G) (r : ∀ i, Gamma i →* J i)
    (hr : ∀ i, Function.Surjective (r i))
    (hcompatible : ∀ (i : I) (gamma : Gamma i) (x : F i),
      pi gamma (emb i x) = emb i (rho i (r i gamma) x))
    (d : ∀ i, Gamma i →*
      Aut (pullback (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom))))
    (hdS : ∀ (i : I) (gamma : Gamma i), (d i gamma).hom ≫
      pullback.fst (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) =
      pullback.fst (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫
        (a i (r i gamma)).hom)
    (hdK : ∀ (i : I) (gamma : Gamma i), (d i gamma).hom ≫
      pullback.snd (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) =
      pullback.snd (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (pi (gamma : G)⁻¹).toRingHom))
    (Y : I → Scheme.{u}) (q : ∀ i, Y i ⟶ Spec (.of K))
    (aY : ∀ i, G →* Aut (Y i)) (fY : ∀ i, Y i ⟶ B i)
    (tY : ∀ i, G →
      (pullback (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ⟶ Y i))
    (s : ∀ i, G ⧸ Gamma i → G)
    (hs : ∀ (i : I) (c : G ⧸ Gamma i),
      Quotient.mk (QuotientGroup.leftRel (Gamma i)) (s i c) = c)
    (hcoproduct : ∀ i, Nonempty (IsColimit
      (Cofan.mk (Y i) (fun c : G ⧸ Gamma i ↦ tY i (s i c)))))
    (hrelation : ∀ (i : I) (g : G) (gamma : Gamma i),
      tY i (g * gamma) = (d i gamma).hom ≫ tY i g)
    (hscalar : ∀ (i : I) (g : G), tY i g ≫ q i =
      pullback.snd (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (pi g⁻¹).toRingHom))
    (hleft : ∀ (i : I) (h g : G), tY i g ≫ (aY i h).hom = tY i (h * g))
    (hmap : ∀ (i : I) (g : G), tY i g ≫ fY i =
      pullback.fst (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫ vS i) :
    Smooth (Sigma.desc q) ∧ GeometricallyReduced (Sigma.desc q) ∧ IsReduced (∐ Y) ∧
      IsHProjective (Sigma.desc q) ∧
      IsHProjective
        (Sigma.desc q ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))) ∧
      IsHProjective (Sigma.desc (fun i ↦ fY i ≫ Sigma.ι B i)) ∧
      IsProjectiveBundle (Sigma.desc (fun i ↦ fY i ≫ Sigma.ι B i)) ∧
      Surjective (Sigma.desc (fun i ↦ fY i ≫ Sigma.ι B i)) ∧
      Scheme.IdealSheafData.IsSmoothStrictNormalCrossingsDivisor (Sigma.desc q)
        (C.comap (Sigma.desc (fun i ↦ fY i ≫ Sigma.ι B i))).radical := by
  sorry

end AlgebraicGeometry
