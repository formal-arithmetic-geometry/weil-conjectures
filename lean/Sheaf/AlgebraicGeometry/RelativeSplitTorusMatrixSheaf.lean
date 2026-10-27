module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Matrix.Mul
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Relative split tori and locally constant exponent matrices

Source: Milne, Algebraic Groups (2017), Lemma 12.4 and Theorem 12.9(a), pp.232--234;
Stacks, Tags 022U and 03P5. The coefficient argument is used over arbitrary rings,
retaining its orthogonal idempotents (blueprint: lem-sfb-relative-split-torus-matrix-sheaf).

## Main definitions

The relative model is the base change of the explicit integer Laurent Hopf algebra.
All coordinates and change-of-base arrows have real data. The theorem packages their
point interpretation and the compatible matrix and character-sheaf identifications.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.RelativeSplitTorus

/-- The integral Laurent algebra with basis e^v, v in Z^n. Source: Milne, Examples
12.1--12.2 (blueprint: lem-sfb-relative-split-torus-matrix-sheaf). -/
abbrev LaurentAlgebra (n : ℕ) := AddMonoidAlgebra (ULift.{u} ℤ) (Fin n → ℤ)

/-- The integer split torus with its canonical Hopf group law e^v to e^v tensor e^v,
1 and e^(-v). Source: Milne, Remark 12.6; Stacks, Tag 022U
(blueprint: lem-sfb-relative-split-torus-matrix-sheaf). -/
def integerModel (n : ℕ) : CommGrp (Over (Spec (.of (ULift.{u} ℤ)))) :=
  ⟨(Spec (.of (LaurentAlgebra.{u} n))).asOver (Spec (.of (ULift.{u} ℤ)))⟩

/-- The canonical relative split torus. Base change of the integer model has affine
charts Spec A[Z^n], and therefore is the gluing in the statement. Source: Stacks, Tag
022U (blueprint: lem-sfb-relative-split-torus-matrix-sheaf). -/
def model (B : Scheme.{u}) (n : ℕ) : CommGrp (Over B) :=
  (Over.pullback (specULiftZIsTerminal.from B)).mapCommGrp.obj (integerModel n)

/-- Projection to the integral Laurent model. Source: Stacks, Tag 022U
(blueprint: lem-sfb-relative-split-torus-matrix-sheaf). -/
def integralProjection (B : Scheme.{u}) (n : ℕ) :
    (model B n).X.left ⟶ Spec (.of (LaurentAlgebra.{u} n)) :=
  pullback.fst _ _

/-- The i-th Laurent coordinate as a global function on the relative model.
Source: Milne, Remark 12.6; Stacks, Tag 022U
(blueprint: lem-sfb-relative-split-torus-matrix-sheaf). -/
def coordinate (B : Scheme.{u}) (n : ℕ) (i : Fin n) : Γ((model B n).X.left, ⊤) :=
  (integralProjection B n).appTop
    ((Scheme.ΓSpecIso (.of (LaurentAlgebra.{u} n))).inv
      (AddMonoidAlgebra.single (Pi.single i 1) 1))

/-- Base change of a group morphism, conjugated by the specified split-model
comparisons. Source: Stacks, Tag 022U; Milne, Theorem 12.9(a)
(blueprint: lem-sfb-relative-split-torus-matrix-sheaf). -/
def changeHom {B B' : Scheme.{u}} (b : B' ⟶ B) (r s : ℕ)
    (er : (Over.pullback b).mapGrp.obj (model B r).toGrp ≅ (model B' r).toGrp)
    (es : (Over.pullback b).mapGrp.obj (model B s).toGrp ≅ (model B' s).toGrp)
    (f : (model B r).toGrp ⟶ (model B s).toGrp) :
    (model B' r).toGrp ⟶ (model B' s).toGrp :=
  er.inv ≫ (Over.pullback b).mapGrp.map f ≫ es.hom

/-- Relative split-torus homomorphisms are locally constant integer matrices, with
the monomial normalization, all functorialities and the constant character sheaf.

Source: Milne, Lemma 12.4 and Theorem 12.9(a), pp.232--234, with the ring-generalized
coefficient calculation; Stacks, Tags 022U, 00EE, 00AN and 03P5
(blueprint: lem-sfb-relative-split-torus-matrix-sheaf).

Proof:
1. Write A[Z^n] as finite sums c_v e^v, with convolution multiplication. Algebra maps
   to C correspond to n units. The tensor product of two such algebras is A[Z^(n+m)]
   by e^v tensor e^w to e^(v,w); use the algebra tensor pushout universal property.
2. Base change the integer model to B. The affine fibre-product formula identifies
   its affine charts with these Laurent algebras. The affine adjunction gives the
   natural point formula; the Hopf maps give multiplication, unit and inversion.
3. A group morphism gives an algebra map whose generator images g satisfy
   Delta(g)=g tensor g and epsilon(g)=1, by the affine group diagrams.
4. Comparing coefficients says that the finitely many coefficients of each g are
   orthogonal idempotents summing to 1. This holds even over nonreduced rings.
5. The clopen-idempotent correspondence (lem-weil-pbc-spec-clopen-idempotent) gives
   a clopen partition on which each generator image is one monomial. Intersect the
   finitely many row partitions. Residue-field monomials give uniqueness, so affine
   charts agree on overlaps and determine a locally constant matrix on B.
6. Conversely glue the monomial maps over the open fibres of a locally constant
   matrix, using lem-weil-pbc-scheme-morphism-gluing. These constructions are inverse;
   evaluation on every test scheme gives the displayed unit formula.
7. Substitution multiplies matrices, identity has matrix I, and multiplying
   homomorphisms adds exponents. Pullback retains the same generator images, giving
   composition of the matrix function with the base map. Inverses correspond to
   inverse integer matrices and give the automorphism correspondence.
8. On the small etale site the character presheaf becomes locally constant Z^r.
   Use lem-galois-coproduct-copies-morphisms-clopen and
   lem-galois-constant-sheaf-sets-representable to identify it with the constant sheaf.
   Addition of vectors agrees with multiplication of characters; constant vectors
   give their monomial characters. Base change supplies the restriction maps.
9. For rank zero there are no coordinates and empty products equal 1. On the empty
   base both morphism and locally constant function sets are singletons. All ring
   calculations allow the zero ring, disconnected bases and nilpotents. -/
theorem matrix_sheaf_classification :
    ∃ (p : ∀ (B : Scheme.{u}) (n : ℕ) (W : Over B),
        (W ⟶ (model B n).X) ≃* (Fin n → Γ(W.left, ⊤)ˣ))
      (e : ∀ (B : Scheme.{u}) (r s : ℕ),
        ((model B r).toGrp ⟶ (model B s).toGrp) ≃
          LocallyConstant B (Matrix (Fin s) (Fin r) ℤ))
      (β : ∀ {B B' : Scheme.{u}} (b : B' ⟶ B) (n : ℕ),
        (Over.pullback b).mapGrp.obj (model B n).toGrp ≅ (model B' n).toGrp),
      (∀ (B : Scheme.{u}) (n : ℕ) (W : Over B) (x : W ⟶ (model B n).X) (i : Fin n),
        ↑(p B n W x i) = x.left.appTop (coordinate B n i)) ∧
      (∀ (B : Scheme.{u}) (n : ℕ) (V W : Over B) (a : W ⟶ V)
        (x : V ⟶ (model B n).X) (i : Fin n),
        p B n W (a ≫ x) i = Units.map a.left.appTop.hom.toMonoidHom (p B n V x i)) ∧
      (∀ (B : Scheme.{u}) (r s : ℕ)
        (f : (model B r).toGrp ⟶ (model B s).toGrp)
        (U : B.Opens) (A : Matrix (Fin s) (Fin r) ℤ)
        (_hA : ∀ b ∈ U, e B r s f b = A) (W : Over B)
        (_hW : Set.range W.hom ⊆ U) (x : W ⟶ (model B r).X) (j : Fin s),
        p B s W (x ≫ f.hom.hom) j = ∏ i : Fin r, p B r W x i ^ A j i) ∧
      (∀ (B : Scheme.{u}) (r s t : ℕ)
        (f : (model B r).toGrp ⟶ (model B s).toGrp)
        (g : (model B s).toGrp ⟶ (model B t).toGrp) (b : B),
        e B r t (f ≫ g) b = e B s t g b * e B r s f b) ∧
      (∀ (B : Scheme.{u}) (r : ℕ) (b : B), e B r r (𝟙 _) b = 1) ∧
      (∀ (B : Scheme.{u}) (r s : ℕ)
        (f g : (model B r).toGrp ⟶ (model B s).toGrp),
        ∃ h : (model B r).toGrp ⟶ (model B s).toGrp,
          h.hom.hom = f.hom.hom * g.hom.hom ∧
          ∀ b : B, e B r s h b = e B r s f b + e B r s g b) ∧
      (∀ (B B' : Scheme.{u}) (b : B' ⟶ B) (n : ℕ) (W : Over B')
        (x : W ⟶ ((Over.pullback b).mapGrp.obj (model B n).toGrp).X) (i : Fin n),
        p B' n W (x ≫ (β b n).hom.hom.hom) i =
          p B n ((Over.map b).obj W)
            (((Over.mapPullbackAdj b).homEquiv W (model B n).X).symm x) i) ∧
      (∀ (B B' : Scheme.{u}) (b : B' ⟶ B) (r s : ℕ)
        (f : (model B r).toGrp ⟶ (model B s).toGrp) (x : B'),
        e B' r s (changeHom b r s (β b r) (β b s) f) x = e B r s f (b x)) ∧
      (∀ (B : Scheme.{u}) (r : ℕ),
        ∃ a : Aut (model B r).toGrp ≃
            LocallyConstant B (Matrix (Fin r) (Fin r) ℤ)ˣ,
          ∀ (f : Aut (model B r).toGrp) (b : B),
            ↑(a f b) = e B r r f.hom b) ∧
      (∀ B : Scheme.{u}, Nonempty ((model B 0).toGrp ≅ Grp.trivial (Over B))) ∧
      (∀ (B : Scheme.{u}) (r : ℕ),
        ∃ (H : B.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
          (hH : Presheaf.IsSheaf B.smallEtaleTopology H)
          (q : ∀ U : B.Etale, H.obj (op U) ≃
            ((model U.left r).toGrp ⟶ (model U.left 1).toGrp))
          (φ : (constantSheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (Fin r → ℤ))) ≅ ⟨H, hH⟩),
          (∀ (U V : B.Etale) (k : V ⟶ U) (χ : H.obj (op U)),
            q V (H.map k.op χ) =
              changeHom k.left r 1 (β k.left r) (β k.left 1) (q U χ)) ∧
          (∀ (U : B.Etale) (χ ψ : H.obj (op U)),
            (q U (χ + ψ)).hom.hom = (q U χ).hom.hom * (q U ψ).hom.hom) ∧
          (∀ (U : B.Etale) (v : Fin r → ℤ),
            e U.left r 1
              (q U ((φ.hom.hom.app (op U))
                ((toSheafify B.smallEtaleTopology
                  ((Functor.const B.Etaleᵒᵖ).obj
                    (AddCommGrpCat.of (ULift.{u + 1} (Fin r → ℤ))))).app (op U) ⟨v⟩))) =
              LocallyConstant.const U.left (fun (_ : Fin 1) (i : Fin r) ↦ v i))) := by
  sorry

end AlgebraicGeometry.RelativeSplitTorus
