module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Relative tangent modules and torus weights

Source: Conrad, Reductive group schemes, printed pp.2 and 107; Stacks Tags
00RO, 00RV, 00T2, 01V6, 02H6 and 0EKK.
(blueprint: lem-sfb-relative-tangent-weight-base-change)

The tangent module is the existing `GrpObj.Lie`. The kernel uses G-valued points over
A, equivalently points of G_B over B. `Data` specifies the natural comparisons by their
actual dual-number points. Its coaction is characterized at all algebra-valued torus
points, including the generic point, rather than only at geometric points. The full
coaction after extension is `SplitTorus.baseChangeCoaction`, transported by `E`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.RelativeTangentWeights

variable {A : Type u} [CommRing A]

/-- The actual kernel of reduction of dual-number points. Source: Conrad, printed p.2.
(blueprint: lem-sfb-relative-tangent-weight-base-change) -/
abbrev Kernel (G : Grp (Over (Spec (.of A)))) (B : Type u) [CommRing B] [Algebra A B] :=
  {x : points G.X (DualNumber B) //
    points.map G.X ((TrivSqZeroExt.fstHom B B B).restrictScalars A) x = 1}

/-- The relative version of the coefficient map on dual numbers, bundled over A.
Source: Stacks 00CV, scalar-extension formulas.
(blueprint: lem-sfb-relative-tangent-weight-base-change) -/
def dualMap {B C : Type u} [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    (h : B →ₐ[A] C) : DualNumber B →ₐ[A] DualNumber C where
  __ := DualNumber.mapRingHom h.toRingHom
  commutes' x := by
    ext <;> simp [DualNumber.mapRingHom, TrivSqZeroExt.algebraMap_eq_inl']

/-- The action on test points obtained from the actual scheme action morphism.
Source: Conrad, Section 4, printed p.107.
(blueprint: lem-sfb-relative-tangent-weight-base-change) -/
def act {r : ℕ} {G : Grp (Over (Spec (.of A)))}
    (a : ModObj (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X G.X)
    {B : Type u} [CommRing B] [Algebra A B]
    (t : points (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X B)
    (x : points G.X B) : points G.X B :=
  CartesianMonoidalCategory.lift t x ≫ a.smul

/-- A character-valued algebra map is a point of Spec A[M]. The universe lift of the
finite-rank character lattice changes no characters. Source: Conrad, Appendix B.1.
(blueprint: lem-sfb-relative-tangent-weight-base-change) -/
def torusPoint {r : ℕ} {B : Type u} [CommRing B] [Algebra A B]
    (f : AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)) →ₐ[A] B) :
    points (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X B :=
  (Spec.map (CommRingCat.ofHom f.toRingHom)).asOver (Spec (.of A))

/-- Evaluate the coaction at an arbitrary B-valued torus point and extend B-linearly.
On b tensor v this is b times the tensor-factor interchange of (1 tensor f)rho(v).
Source: Stacks 0EKK, coefficient description of an action.
(blueprint: lem-sfb-relative-tangent-weight-base-change) -/
def evaluatedAction {r : ℕ} {G : Grp (Over (Spec (.of A)))}
    (rho : GrpObj.Lie G.X →ₗ[A]
      GrpObj.Lie G.X ⊗[A] AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))
    {B : Type u} [CommRing B] [Algebra A B]
    (f : AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)) →ₐ[A] B) :
    B ⊗[A] GrpObj.Lie G.X →ₗ[B] B ⊗[A] GrpObj.Lie G.X :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton B _
      ((TensorProduct.comm A _ B).toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id f.toLinearMap ∘ₗ rho))

/-- All conclusions, with maps normalized by actual tangent points. `E` is B-linear
for the intrinsic operations because `add`, `zero`, `neg` and `scale` identify them
with multiplication, identity, inversion and epsilon scaling. Its naturality is the
successive-extension comparison on all vectors, not just on a chosen basis.
Source: Conrad, printed pp.2 and 107; Stacks 00RO, 00RV and 0EKK.
(blueprint: lem-sfb-relative-tangent-weight-base-change) -/
structure Data (r : ℕ) (G : Grp (Over (Spec (.of A))))
    (a : ModObj (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X G.X) where
  /-- The identity tangent module is finite. -/
  finite : Module.Finite A (GrpObj.Lie G.X)
  /-- The identity tangent module is projective, hence a finite-free summand. -/
  projective : Module.Projective A (GrpObj.Lie G.X)
  /-- The natural comparison to the actual dual-number kernel. -/
  E (B : Type u) [CommRing B] [Algebra A B] : (B ⊗[A] GrpObj.Lie G.X) ≃ Kernel G B
  /-- Addition is the group law. -/
  add (B : Type u) [CommRing B] [Algebra A B] (v w : B ⊗[A] GrpObj.Lie G.X) :
    (E B (v + w)).val = (E B v).val * (E B w).val
  /-- Zero is the identity. -/
  zero (B : Type u) [CommRing B] [Algebra A B] : (E B 0).val = 1
  /-- Negation is inversion. -/
  neg (B : Type u) [CommRing B] [Algebra A B] (v : B ⊗[A] GrpObj.Lie G.X) :
    (E B (-v)).val = ((E B v).val)⁻¹
  /-- Scalars act by epsilon scaling. -/
  scale (B : Type u) [CommRing B] [Algebra A B] (b : B)
      (v : B ⊗[A] GrpObj.Lie G.X) :
    points.map G.X ((DualNumber.scale b).restrictScalars A) (E B v).val =
      (E B (b • v)).val
  /-- Normalization fixes the comparison over the base ring. -/
  normalize (v : GrpObj.Lie G.X) : (E A (1 ⊗ₜ[A] v)).val = GrpObj.tangentPoint v
  /-- Compatibility with every successive algebra extension. -/
  natural (B C : Type u) [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (h : B →ₐ[A] C) (v : B ⊗[A] GrpObj.Lie G.X) :
    points.map G.X (dualMap h) (E B v).val =
      (E C (TensorProduct.map h.toLinearMap LinearMap.id v)).val
  /-- The differentiated coaction is an A-linear map. -/
  rho : GrpObj.Lie G.X →ₗ[A]
    GrpObj.Lie G.X ⊗[A] AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ))
  /-- Coassociativity uses the full group-algebra coproduct. -/
  coassoc : (TensorProduct.assoc A _ _ _).toLinearMap ∘ₗ rho.rTensor _ ∘ₗ rho =
    (Coalgebra.comul (R := A)
      (A := AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))).lTensor _ ∘ₗ rho
  /-- The identity torus element acts identically. -/
  counit : (TensorProduct.rid A _).toLinearMap ∘ₗ
    (Coalgebra.counit (R := A)
      (A := AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)))).lTensor _ ∘ₗ rho = LinearMap.id
  /-- Evaluation at every torus point equals differentiation of the given action.
  Taking B=A[M], f=id and v=1 tensor w fixes rho uniquely. Naturality
  supplies the full scalar-extended differentiated coaction over every B. -/
  differentiated (B : Type u) [CommRing B] [Algebra A B]
      (f : AddMonoidAlgebra A (ULift.{u} (Fin r → ℤ)) →ₐ[A] B)
      (v : B ⊗[A] GrpObj.Lie G.X) :
    act a (points.map _ (TrivSqZeroExt.inlAlgHom A B B) (torusPoint f))
        (E B v).val = (E B (evaluatedAction rho f v)).val
  /-- The canonical direct sum of weight inclusions is an isomorphism. -/
  decomposition : Function.Bijective (DirectSum.coeLinearMap (SplitTorus.weightSpace rho))
  /-- Only finitely many weights occur. -/
  support : Set.Finite {m | SplitTorus.weightSpace rho m ≠ ⊥}
  /-- Every weight summand is finite projective, including zero summands. -/
  weight_projective (m : ULift.{u} (Fin r → ℤ)) :
    Module.Finite A (SplitTorus.weightSpace rho m) ∧
      Module.Projective A (SplitTorus.weightSpace rho m)
  /-- The actual weight inclusion stays injective after every, possibly nonflat, extension;
  its image is exactly the full extended-coaction weight space. Transport through E B
  gives the asserted weight comparison in the actual tangent kernel. -/
  weight_baseChange (B : Type u) [CommRing B] [Algebra A B]
      (m : ULift.{u} (Fin r → ℤ)) :
    Function.Injective ((SplitTorus.weightSpace rho m).subtype.baseChange B) ∧
      (SplitTorus.weightSpace rho m).baseChange B =
        SplitTorus.weightSpace (SplitTorus.baseChangeCoaction B rho) m

/-- Smooth relative tangent modules have finite projective torus weight summands, and
all tangent and weight comparisons commute with arbitrary and successive base changes.
Source: Conrad, Reductive group schemes, printed pp.2 and 107; Stacks 00RO, 00RV,
00T2, 01V6, 02H6 and 0EKK.
(blueprint: lem-sfb-relative-tangent-weight-base-change)

Proof: (1) Write G=Spec C and pull the finite projective smooth cotangent module back
along its identity u:C→A, obtaining Q as a summand of A^N. (2) Expand dual-number
points as u+epsilon D. The derivation universal property identifies them with
Hom_A(Q,B), naturally in every A-algebra B. (3) The two unit identities in the group
law make multiplication of tangent points addition of derivations; epsilon scaling
is scalar multiplication. (4) Dualizing the splitting makes Q* finite projective.
(5) Differential base change gives Q_B=B tensor Q. A finite dual basis gives the
inverse of B tensor Q*→Hom_B(B tensor Q,B), without flatness. Its formula on c is
b D(c), fixing E. (6) Over A→B→C both comparisons have coefficient c h(b)D(x),
proving naturality and the successive-extension identification. (7) Evaluate the
given action at the generic point of A[M]; on a*(x)=sum h_i tensor x_i its tangent
coefficient is sum h_i D(x_i). This fixes rho and proves the differentiated formula.
(8) The identity and action diagrams give the counit and coassociativity identities
over A[M] and A[M] tensor A[M]. (9) Apply the group-algebra coaction grading argument
to the square-zero algebra A plus Lie(G); coefficient projections preserve its
square-zero summand, giving the unique finite weight expansion and direct-sum
isomorphism. (10) Finite generators have finitely many total weights. Coefficient
projections split each weight inclusion, making each weight finite projective.
(11) Tensor these split projections with B. Laurent coefficient comparison proves
that their images are exactly the full extended weight modules, even for nonflat
or zero B. (12) Naturality restricts to these split weight summands and gives the
same tower formula c h(b) tensor v_m. Rank zero and a zero tangent module are included.
-/
theorem exists_data (r : ℕ) [Nontrivial A] [IsNoetherianRing A]
    (G : Grp (Over (Spec (.of A)))) [IsAffine G.X.left] [Smooth G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (a : ModObj (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X G.X)
    (hgroup : ∀ (B : Type u) [CommRing B] [Algebra A B]
      (t : points (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X B)
      (x y : points G.X B), act a t (x * y) = act a t x * act a t y) :
    Nonempty (Data r G a) := by
  sorry

end AlgebraicGeometry.RelativeTangentWeights
