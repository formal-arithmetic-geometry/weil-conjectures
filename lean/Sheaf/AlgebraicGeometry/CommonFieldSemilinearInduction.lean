module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Sober
public import Sheaf.FieldTheory.FieldTower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable

/-!
# Common normal constants and semilinear induction

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X 2.3 Step 2,
printed p. 150, contracted products and diagram (2.b); the DAG's finite-family
common-normal-field elaboration. (blueprint: lem-sfb-common-field-semilinear-induction)

The contracted product is specified by its actual coset coproduct cocone and its
maps from every copy, with the relation, scalar twists and left action written out.
Geometric orbits concern underlying points of the pullback schemes, including
nonreduced geometric fibres, rather than only field-valued lifts to the source.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map of a fibre product induced by an invariant endomorphism.

Source: the fibre-product action in ILO, Expose X 2.3 Step 2, diagram (2.b).
(blueprint: lem-sfb-common-field-semilinear-induction)

This is exactly `pullback.map` with identity maps on the geometric point and base.
It supplies the actual morphism used in the underlying-point orbit clauses. -/
noncomputable def invariantSchemeFiberMap {X B T : Scheme.{u}}
    (f : X ⟶ B) (b : T ⟶ B) (a : X ⟶ X) (ha : a ≫ f = f) :
    pullback f b ⟶ pullback f b :=
  pullback.map f b f b a (𝟙 T) (𝟙 B)
    (by simpa only [Category.comp_id] using ha.symm)
    (by simp only [Category.comp_id, Category.id_comp])

/-- Simultaneous induction to one finite normal field and one finite group.

Source: ILO, Expose X 2.3 Step 2, printed p. 150, contracted products and (2.b),
with the finite-family common-normal-field argument in the DAG.
(blueprint: lem-sfb-common-field-semilinear-induction)

The homomorphism `rho` is the field action; `a` is the compatible scheme action.
The inverse in `Spec.map` converts left field actions into left scheme actions.
The maps `t i g` represent `[g,-]`. Their coset-representative subfamily is a
coproduct cocone; `hrelation` below is written as an equality of these morphisms.
No normality or separability is imposed on the original extensions `F i / e`.

Proof (the ten steps of the node):
1. Enumerate the nonempty finite family. Successively form common extensions and
   composita using lem-weil-common-extension-fields and
   lem-weil-pbc-compositum-degree-bound. Finite spanning sets show that each
   compositum remains finite. Apply
   lem-weil-pbc-finite-extension-in-finite-normal-extension at the final stage,
   giving K and the embeddings of all F i.
2. A = Aut_e(K) is finite: each automorphism is determined on a finite basis, and
   every basis element has only finitely many possible conjugates. Put
   G = A times the product of the J i. Let Gamma i be the compatible pairs, and
   project to J i. By lem-sfb-normal-intermediate-isomorphism-lifts every field
   automorphism coming from J i lifts to A, even if that action is not faithful.
   Thus the projections are surjective. The image on K is A, and
   lem-weil-pbc-normal-extension-fixed-field-purely-inseparable gives the fixed field.
3. On W i = V i times_{F i} K, the fibre-product universal property constructs
   the diagonal Gamma i action from the two compatible actions. Its projection
   identities determine it and prove the group law.
4. Choose representatives s of left cosets and form the coproduct of copies of
   W i using lem-weil-pbc-scheme-coproduct-family. Give the g-copy the scalar map
   p_W followed by Spec(pi(g^{-1})). The diagonal action identifies the g gamma
   copy with the g copy by gamma_W. These identifications obey the action law,
   realizing precisely (g gamma,w) equivalent to (g,gamma w).
5. Write h s(c) = s(hc) gamma(h,c). Send the c-copy by gamma(h,c)_W to the hc-copy.
   The cocycle identity proves the group law, and the scalar formula proves
   semilinearity. This action is left multiplication on [g,w].
6. Descend the Gamma-invariant morphism pr_1 followed by v i on each copy.
   The coproduct universal property proves the formula for t i g, invariance
   under G, and compatibility with the maps to Spec e.
7. Over an algebraically closed geometric point, a nonempty single finite orbit
   on V_b consists of rational points: apply lem-weil-pbc-zariski-lemma on a
   nonempty finite-type affine chart and translate that rational point. Above x,
   W_b has the points of Spec(Omega tensor_{F i} K). This is a nonzero finite
   algebra. By lem-weil-pbc-finite-dimensional-domain-is-field its prime quotients
   are Omega; its points are exactly the extending embeddings K into Omega.
   The argument allows nilpotents and inseparability.
8. Lift an element of J i carrying two images in V_b to Gamma i. Once those
   images agree, use lem-weil-pbc-normal-extension-normal-over-intermediate and
   lem-sfb-normal-embeddings-automorphism-transitive to join the two extending
   embeddings by Aut_{F i}(K), a subgroup of Gamma i. Thus W_b is one orbit.
9. The coproduct is a disjoint open cover and remains so after base change.
   Move two points to the identity copy by G, use the preceding Gamma orbit,
   and move back. The identity copy has a point, proving nonemptiness as well.
10. W i to V i is finite free on affine charts. By lem-sc-flat-going-down every
   generic point maps to a generic point. Its residue extension is finite by
   lem-weil-pbc-finite-dimensional-domain-is-field applied to the scalar tensor
   algebra. Compose finite residue extensions with those for v i. Generic points
   of a disjoint coproduct are exactly those of its copies; scalar twists do
   not change their underlying e-morphisms. This proves the final implication. -/
theorem common_field_semilinear_induction
    (e : Type u) [Field e] (I : Type w) [Finite I] [Nonempty I]
    (F : I → Type u) [∀ i, Field (F i)] [∀ i, Algebra e (F i)]
    [∀ i, Module.Finite e (F i)]
    (J : I → Type v) [∀ i, Group (J i)] [∀ i, Finite (J i)]
    (rho : ∀ i, J i →* (F i ≃ₐ[e] F i))
    (V B : I → Scheme.{u})
    (p : ∀ i, V i ⟶ Spec (.of (F i))) (b : ∀ i, B i ⟶ Spec (.of e))
    [∀ i, LocallyOfFiniteType (p i)] [∀ i, QuasiCompact (p i)]
    (a : ∀ i, J i →* Aut (V i))
    (ha : ∀ (i : I) (j : J i), (a i j).hom ≫ p i =
      p i ≫ Spec.map (CommRingCat.ofHom (rho i j⁻¹).toRingHom))
    (f : ∀ i, V i ⟶ B i)
    (hbase : ∀ i, f i ≫ b i =
      p i ≫ Spec.map (CommRingCat.ofHom (algebraMap e (F i))))
    (hinvariant : ∀ (i : I) (j : J i), (a i j).hom ≫ f i = f i) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra e K)
      (_ : Module.Finite e K) (_ : Normal e K) (emb : ∀ i, F i →ₐ[e] K)
      (G : Type (max u v w)) (_ : Group G) (_ : Finite G)
      (pi : G →* (K ≃ₐ[e] K)),
      Function.Surjective pi ∧
      IsPurelyInseparable e (IntermediateField.fixedField pi.range) ∧
      ∃ (Gamma : I → Subgroup G) (r : ∀ i, Gamma i →* J i),
        (∀ i, Function.Surjective (r i)) ∧
        (∀ (i : I) (gamma : Gamma i) (x : F i),
          pi gamma (emb i x) = emb i (rho i (r i gamma) x)) ∧
        ∃ (d : ∀ i, Gamma i →*
            Aut (pullback (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom))))
          (Y : I → Scheme.{u}) (q : ∀ i, Y i ⟶ Spec (.of K))
          (aY : ∀ i, G →* Aut (Y i)) (fY : ∀ i, Y i ⟶ B i)
          (t : ∀ i, G →
            (pullback (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ⟶ Y i))
          (s : ∀ i, G ⧸ Gamma i → G)
          (hinvariantY : ∀ (i : I) (g : G), (aY i g).hom ≫ fY i = fY i),
          (∀ (i : I) (gamma : Gamma i), (d i gamma).hom ≫
            pullback.fst (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) =
            pullback.fst (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫
              (a i (r i gamma)).hom) ∧
          (∀ (i : I) (gamma : Gamma i), (d i gamma).hom ≫
            pullback.snd (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) =
            pullback.snd (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫
              Spec.map (CommRingCat.ofHom (pi (gamma : G)⁻¹).toRingHom)) ∧
          (∀ (i : I) (c : G ⧸ Gamma i),
            Quotient.mk (QuotientGroup.leftRel (Gamma i)) (s i c) = c) ∧
          (∀ i, Nonempty (IsColimit
            (Cofan.mk (Y i) (fun c : G ⧸ Gamma i ↦ t i (s i c))))) ∧
          (∀ (i : I) (g : G) (gamma : Gamma i),
            t i (g * gamma) = (d i gamma).hom ≫ t i g) ∧
          (∀ (i : I) (g : G), t i g ≫ q i =
            pullback.snd (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫
              Spec.map (CommRingCat.ofHom (pi g⁻¹).toRingHom)) ∧
          (∀ (i : I) (h g : G), t i g ≫ (aY i h).hom = t i (h * g)) ∧
          (∀ (i : I) (g : G), t i g ≫ fY i =
            pullback.fst (p i) (Spec.map (CommRingCat.ofHom (emb i).toRingHom)) ≫ f i) ∧
          (∀ (i : I) (g : G), (aY i g).hom ≫ q i =
            q i ≫ Spec.map (CommRingCat.ofHom (pi g⁻¹).toRingHom)) ∧
          (∀ i, fY i ≫ b i = q i ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))) ∧
          (∀ (i : I) (Omega : Type u) [Field Omega] [IsAlgClosed Omega]
            (z : Spec (.of Omega) ⟶ B i),
            (Nonempty ↥(pullback (C := Scheme.{u}) (f i) z) ∧
              ∀ x y : ↥(pullback (C := Scheme.{u}) (f i) z), ∃ j : J i,
                invariantSchemeFiberMap (f i) z (a i j).hom (hinvariant i j) x = y) →
            Nonempty ↥(pullback (C := Scheme.{u}) (fY i) z) ∧
              ∀ x y : ↥(pullback (C := Scheme.{u}) (fY i) z), ∃ g : G,
                invariantSchemeFiberMap (fY i) z (aY i g).hom (hinvariantY i g) x = y) ∧
          (∀ i, (∀ x ∈ genericPoints (V i),
              f i x ∈ genericPoints (B i) ∧ ((f i).residueFieldMap x).hom.Finite) →
            ∀ y ∈ genericPoints (Y i),
              fY i y ∈ genericPoints (B i) ∧ ((fY i).residueFieldMap y).hom.Finite) := by
  sorry

end AlgebraicGeometry
