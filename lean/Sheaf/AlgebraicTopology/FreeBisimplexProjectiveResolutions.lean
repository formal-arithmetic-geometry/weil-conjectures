module

public import Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Order.Fin.InsertNth
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Free bisimplex resolutions and their pointwise contractions

Source: the agent-written free-generator and cone calculations extracted from paragraph (3)
of the blueprint's six-functor stability proof. Stacks, Tag 08Q3,
`example-simplex-contractible`, motivates the minimum-vertex contraction only
(blueprint: lem-sfb-free-bisimplex-projective-resolutions).

The resolution theorem specifies every differential and augmentation on generators. Its
comparison isomorphisms specify the generators too. The cone maps below retain repetitions.
Abelian groups may live in any universe `u`; the finite string complexes are lifted from
universe zero by the existing additive group lift functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial
open scoped BigOperators TensorProduct

noncomputable section

namespace AlgebraicTopology.FreeBisimplex

/-- The free abelian covariant representable, with arrows lifted only for universe size.
Source: free-generator construction, proof steps 2–3
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def representable (i : SimplexCategory × SimplexCategory) :
    SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u} :=
  coyoneda.obj (op i) ⋙ CategoryTheory.uliftFunctor.{u, 0} ⋙ AddCommGrpCat.free

/-- The basis element associated to an arrow. Source: proof step 2
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def generator {i j : SimplexCategory × SimplexCategory} (f : i ⟶ j) :
    (representable.{u} i).obj j :=
  FreeAbelianGroup.of (ULift.up f)

/-- The finite antidiagonal sum in degree `n`. Source: proof steps 5–6
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def totalTerm (n : ℕ) : SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u} :=
  ∐ (fun ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n} ↦
    representable.{u} (⦋ab.val.1⦌, ⦋ab.val.2⦌))

/-- A basis arrow in a summand of the total degree. Source: proof step 5
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def totalGenerator (a b n : ℕ) (h : a + b = n)
    (j : SimplexCategory × SimplexCategory) (f : (⦋a⦌, ⦋b⦌) ⟶ j) :
    (totalTerm.{u} n).obj j :=
  (Sigma.ι (fun ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n} ↦
    representable.{u} (⦋ab.val.1⦌, ⦋ab.val.2⦌)) ⟨(a, b), h⟩).app j (generator f)

/-- A coface with a positive source degree written using its predecessor. The equality
transport changes only the natural-number index. Source: proof step 6
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def predecessorCoface (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) : ⦋n - 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.δ (k.cast (by omega : n + 1 = n - 1 + 2)) ≫
    eqToHom (congrArg SimplexCategory.mk (by omega : n - 1 + 1 = n))

/-- The two signed boundary contributions on a total-complex basis arrow. A direction
of degree zero contributes zero. Source: proof steps 5–6
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def totalBoundary (a b : ℕ) (j : SimplexCategory × SimplexCategory)
    (f : (⦋a⦌, ⦋b⦌) ⟶ j) : (totalTerm.{u} (a + b - 1)).obj j :=
  (if ha : 0 < a then
    ∑ k : Fin (a + 1), (-1 : ℤ) ^ k.val •
      totalGenerator (a - 1) b (a + b - 1) (by omega) j
        ((predecessorCoface a ha k, 𝟙 ⦋b⦌) ≫ f)
  else 0) +
  (-1 : ℤ) ^ a • (if hb : 0 < b then
    ∑ k : Fin (b + 1), (-1 : ℤ) ^ k.val •
      totalGenerator a (b - 1) (a + b - 1) (by omega) j
        ((𝟙 ⦋a⦌, predecessorCoface b hb k) ≫ f)
  else 0)

/-- Lift an integral module complex to abelian groups in the chosen universe.
Source: universe convention and evaluation clause, proof step 5
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def liftComplex (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  (((forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}) ⋙
    AddCommGrpCat.uliftFunctor.{u, 0}).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Evaluate a chain complex of diagrams at a bisimplex. Source: proof steps 1 and 5
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def evaluateComplex (C : ChainComplex
    (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}) ℕ)
    (j : SimplexCategory × SimplexCategory) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (((evaluation _ _).obj j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Abelian and pointwise exact structure, the natural free-generator bijection, projectivity
of representables and finite sums, and the specified projective epimorphism onto every diagram.

Source: agent-written proof steps 1–4, with Stacks Tag 08Q3 only as motivation
(blueprint: lem-sfb-free-bisimplex-projective-resolutions).

Proof: use the pointwise abelian presheaf and functor-colimit results at the opposite of the
product simplex category. Kernels and quotients compute kernels and cokernels pointwise;
the quotient detects epimorphisms, and kernels and images detect exactness. A map out of a
free representable is determined by its identity generator; its inverse sends an arrow to
the image of the chosen element under that arrow. These formulas commute with maps of
coefficients and with arrows of the indexing category. Lift the element through an epic
component to lift a representable map. Choose lifts for all summands and use the coproduct
universal property. For the sum indexed by all pairs `(i,x)`, the identity generator in the
`(j,z)` summand maps to `z`, proving componentwise surjectivity and hence epimorphy. -/
theorem diagram_projectivity :
    Nonempty (Abelian (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u})) ∧
    (∀ j : SimplexCategory × SimplexCategory,
      PreservesFiniteLimits ((evaluation _ AddCommGrpCat.{u}).obj j) ∧
      PreservesFiniteColimits ((evaluation _ AddCommGrpCat.{u}).obj j)) ∧
    (∀ (F G : SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}) (f : F ⟶ G),
      Epi f ↔ ∀ j, Function.Surjective (f.app j)) ∧
    (∀ S : ShortComplex (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}),
      S.Exact ↔ ∀ j, (S.map ((evaluation _ _).obj j)).Exact) ∧
    (∀ (i : SimplexCategory × SimplexCategory)
      (F : SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}),
      ∃ e : (representable i ⟶ F) ≃ F.obj i,
        (∀ f, e f = f.app i (generator (𝟙 i))) ∧
        (∀ (x : F.obj i) (j : SimplexCategory × SimplexCategory) (α : i ⟶ j),
          (e.symm x).app j (generator α) = F.map α x)) ∧
    (∀ i : SimplexCategory × SimplexCategory, Projective (representable.{u} i)) ∧
    (∀ (S : Type u) [Finite S] (i : S → SimplexCategory × SimplexCategory),
      Projective (∐ (fun s ↦ representable.{u} (i s)))) ∧
    (∀ F : SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u},
      ∃ a : (∐ (fun ix : (i : SimplexCategory × SimplexCategory) × F.obj i ↦
        representable.{u} ix.1)) ⟶ F,
        Epi a ∧ Projective (∐ (fun ix : (i : SimplexCategory × SimplexCategory) ×
          F.obj i ↦ representable.{u} ix.1)) ∧
        ∀ (i : SimplexCategory × SimplexCategory) (x : F.obj i),
          ((Sigma.ι (fun ix : (j : SimplexCategory × SimplexCategory) × F.obj j ↦
            representable.{u} ix.1) ⟨i, x⟩) ≫ a).app i (generator (𝟙 i)) = x) ∧
    EnoughProjectives (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}) := by
  sorry

/-- The two specified augmented projective resolutions, identified degree by degree with
representables and their finite sums, and evaluated as the existing unnormalized string and
tensor complexes. The generator equations fix the differentials, augmentations, and comparison
isomorphisms, rather than just asserting the existence of unspecified resolutions.

Source: agent-written proof steps 5–6 and 10, Stacks Tag 08Q3 as motivation only
(blueprint: lem-sfb-free-bisimplex-projective-resolutions).

Proof: an arrow out of `(n,n)` is a pair of monotone strings, and an arrow out of `(a,b)` is
a pair of strings of the separate degrees. The free-on-pairs tensor identification gives the
displayed evaluation isomorphisms. Diagonal cofaces delete pairs; separate cofaces delete
in the two coordinates with sign `(-1)^a` in the second. Double deletions cancel, and mixed
tensor terms have opposite signs, including the degree-zero omissions. Augmentations kill
edge boundaries. Representables and the finite antidiagonal sums are projective by steps
2–3. The cone calculations of steps 7–9 show every positive cycle and every degree-zero
augmentation-kernel element is a boundary, and the minimum vertex splits each augmentation.
Pointwise detection from step 1 then gives exactness of the augmented diagrams. -/
theorem projective_resolutions :
    ∃ (P Q : ChainComplex (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}) ℕ)
      (p : ∀ n : ℕ, P.X n ≅ representable.{u} (⦋n⦌, ⦋n⦌))
      (q : ∀ n : ℕ, Q.X n ≅ totalTerm.{u} n)
      (εP : P.X 0 ⟶ (Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
      (εQ : Q.X 0 ⟶ (Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
      (zP : P.d 1 0 ≫ εP = 0) (zQ : Q.d 1 0 ≫ εQ = 0),
      (∀ n, Projective (P.X n) ∧ Projective (Q.X n)) ∧
      (∀ (n : ℕ) (j : SimplexCategory × SimplexCategory)
        (α : (⦋n + 1⦌, ⦋n + 1⦌) ⟶ j),
        (p n).hom.app j ((P.d (n + 1) n).app j
          ((p (n + 1)).inv.app j (generator α))) =
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
          generator ((SimplexCategory.δ k, SimplexCategory.δ k) ≫ α)) ∧
      (∀ (a b : ℕ) (j : SimplexCategory × SimplexCategory) (α : (⦋a⦌, ⦋b⦌) ⟶ j),
        (q (a + b - 1)).hom.app j ((Q.d (a + b) (a + b - 1)).app j
          ((q (a + b)).inv.app j (totalGenerator a b (a + b) rfl j α))) =
          totalBoundary a b j α) ∧
      (∀ (j : SimplexCategory × SimplexCategory) (α : (⦋0⦌, ⦋0⦌) ⟶ j),
        εP.app j ((p 0).inv.app j (generator α)) = ULift.up (1 : ℤ) ∧
        εQ.app j ((q 0).inv.app j (totalGenerator 0 0 0 rfl j α)) = ULift.up (1 : ℤ)) ∧
      (ShortComplex.mk (P.d 1 0) εP zP).Exact ∧
      (ShortComplex.mk (Q.d 1 0) εQ zQ).Exact ∧
      Epi εP ∧ Epi εQ ∧
      (∀ n : ℕ, P.ExactAt (n + 1) ∧ Q.ExactAt (n + 1)) ∧
      (∀ p' q' : ℕ,
        ∃ (eP : evaluateComplex P (⦋p'⦌, ⦋q'⦌) ≅
            liftComplex.{u} (SimplexLatticeShuffle.productChains p' q'))
          (eQ : evaluateComplex Q (⦋p'⦌, ⦋q'⦌) ≅ liftComplex.{u}
            (SimplexLatticeShuffle.simplexChains p' ⊗ SimplexLatticeShuffle.simplexChains q')),
          (∀ (n : ℕ) (α : (⦋n⦌, ⦋n⦌) ⟶ (⦋p'⦌, ⦋q'⦌)),
            (eP.hom.f n) ((p n).inv.app _ (generator α)) =
              ULift.up (ModuleCat.freeMk (R := ℤ)
                ((ULift.up α.1, ULift.up α.2) : (Δ[p'] ⊗ Δ[q'] : SSet.{0}) _⦋n⦌))) ∧
          (∀ (a b : ℕ) (α : (⦋a⦌, ⦋b⦌) ⟶ (⦋p'⦌, ⦋q'⦌)),
            (eQ.hom.f (a + b)) ((q (a + b)).inv.app _
              (totalGenerator a b (a + b) rfl _ α)) =
            ULift.up ((HomologicalComplex.ιTensorObj
              (SimplexLatticeShuffle.simplexChains p')
              (SimplexLatticeShuffle.simplexChains q') a b (a + b) rfl).hom
              (ModuleCat.freeMk (R := ℤ) (ULift.up α.1) ⊗ₜ[ℤ]
                ModuleCat.freeMk (R := ℤ) (ULift.up α.2))))) := by
  sorry

open SimplexLatticeShuffle

/-- Prepend the least vertex to an unnormalized simplex, including when it is already first.
Source: proof steps 7–8, minimum-vertex variant of Stacks Tag 08Q3
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def prependString {p n : ℕ} (s : (Δ[p] : SSet.{0}) _⦋n⦌) :
    (Δ[p] : SSet.{0}) _⦋n + 1⦌ :=
  SSet.stdSimplex.objMk
    { toFun := Fin.insertNth 0 0 (SSet.stdSimplex.asOrderHom s)
      monotone' := Fin.insertNth_zero_monotone
        (SSet.stdSimplex.asOrderHom s).monotone 0 (Fin.zero_le _) }

/-- The least vertex of a simplex. Source: proof steps 7–8
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def minimumVertex (p : ℕ) : (Δ[p] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.objMk (OrderHom.const _ 0)

/-- The single-simplex cone operator, extended from the specified basis formula.
Source: proof step 8 (blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def simplexCone (p n : ℕ) : (simplexChains p).X n →ₗ[ℤ] (simplexChains p).X (n + 1) :=
  Finsupp.linearCombination ℤ (fun s ↦ ModuleCat.freeMk (R := ℤ) (prependString s))

/-- The product-simplex cone operator prepends `(0,0)` simultaneously in both coordinates.
Source: proof step 7 (blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def productCone (p q n : ℕ) : (productChains p q).X n →ₗ[ℤ]
    (productChains p q).X (n + 1) :=
  Finsupp.linearCombination ℤ (fun s ↦
    ModuleCat.freeMk (R := ℤ) (prependString s.1, prependString s.2))

/-- The single-simplex projection sends each vertex to the minimum and is zero in positive
homological degrees, namely `e ε` in degree zero. Source: proof step 8
(blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def simplexProjection (p : ℕ) : (n : ℕ) →
    (simplexChains p).X n →ₗ[ℤ] (simplexChains p).X n
  | 0 => Finsupp.linearCombination ℤ (fun _ ↦ ModuleCat.freeMk (R := ℤ) (minimumVertex p))
  | _ + 1 => 0

/-- The product-simplex projection is `e ε` in degree zero and zero otherwise.
Source: proof step 7 (blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def productProjection (p q : ℕ) : (n : ℕ) →
    (productChains p q).X n →ₗ[ℤ] (productChains p q).X n
  | 0 => Finsupp.linearCombination ℤ (fun _ ↦
      ModuleCat.freeMk (R := ℤ) (minimumVertex p, minimumVertex q))
  | _ + 1 => 0

/-- The canonical inclusion of a bidegree into the nonnegative tensor total complex.
Source: proof steps 5 and 9 (blueprint: lem-sfb-free-bisimplex-projective-resolutions). -/
def tensorInclusion (p q a b n : ℕ) (h : a + b = n) :
    (simplexChains p).X a ⊗[ℤ] (simplexChains q).X b →ₗ[ℤ]
      (simplexChains p ⊗ simplexChains q).X n :=
  (HomologicalComplex.ιTensorObj (simplexChains p) (simplexChains q) a b n h).hom

/-- The simplex cone contracts onto its minimum vertex, in degree zero and in every positive
degree, and its vertex augmentation is surjective.

Source: proof step 8, first-vertex variant of Stacks Tag 08Q3
(blueprint: lem-sfb-free-bisimplex-projective-resolutions).

Proof: delete the prepended vertex to obtain the original string. Deleting position `i+1`
is prepending zero after deleting position `i`, with the opposite sign. In positive degree
these terms cancel against `h ∂`; in degree zero the other endpoint is the minimum vertex,
giving `1-e ε`. Repeated vertices remain basis elements. The minimum vertex maps to one,
so its integral multiples prove surjectivity of the augmentation. -/
theorem simplex_contraction (p : ℕ) :
    ((simplexChains p).d 1 0).hom.comp (simplexCone p 0) =
      LinearMap.id - simplexProjection p 0 ∧
    (∀ n : ℕ,
      ((simplexChains p).d (n + 2) (n + 1)).hom.comp (simplexCone p (n + 1)) +
        (simplexCone p n).comp ((simplexChains p).d (n + 1) n).hom =
      LinearMap.id - simplexProjection p (n + 1)) ∧
    Function.Surjective (augmentation : (simplexChains p).X 0 →ₗ[ℤ] ℤ) := by
  sorry

/-- The product-simplex cone contracts onto `(0,0)` pointwise and has surjective augmentation.
No naturality of the cone in the target simplices is required or asserted.

Source: proof steps 7 and 10, first-vertex variant of Stacks Tag 08Q3
(blueprint: lem-sfb-free-bisimplex-projective-resolutions).

Proof: the coordinatewise minimum can always be prepended. The first deletion gives the
original string, while every later deletion is the negative of the cone on the corresponding
face. In degree zero the leftover term is the minimum vertex times the augmentation.
In positive degree the projection vanishes. The minimum pair vertex maps to one, proving
surjectivity. The calculation retains repeated pairs, including an initial minimum pair. -/
theorem product_contraction (p q : ℕ) :
    ((productChains p q).d 1 0).hom.comp (productCone p q 0) =
      LinearMap.id - productProjection p q 0 ∧
    (∀ n : ℕ,
      ((productChains p q).d (n + 2) (n + 1)).hom.comp (productCone p q (n + 1)) +
        (productCone p q n).comp ((productChains p q).d (n + 1) n).hom =
      LinearMap.id - productProjection p q (n + 1)) ∧
    Function.Surjective (augmentation : (productChains p q).X 0 →ₗ[ℤ] ℤ) := by
  sorry

/-- The explicitly characterized tensor cone and tensor projection obey the contraction
identity, and the tensor augmentation is surjective. The formulas on all homogeneous pure
tensors uniquely determine these maps, so the conclusion introduces the specified cone.

Source: agent-written proof steps 8–10, Stacks Tag 08Q3 as motivation only
(blueprint: lem-sfb-free-bisimplex-projective-resolutions).

Proof: use the free-on-pairs identification and the finite coproduct over each antidiagonal
to extend the displayed formulas linearly. Split `H` into `A=h_p ⊗ 1` and the signed term
`B=E_p ⊗ h_q`. The mixed terms of `∂A+A∂` have coefficients `(-1)^(a+1)` and `(-1)^a`,
so they cancel and leave `(1-E_p) ⊗ 1`. The term `B` is zero unless `a=0`. For `a=0`
its commutator gives `E_p ⊗ (1-E_q)`. For `a=1`, the only possible remaining term vanishes
because `E_p ∂=0`: the two vertices of every edge have opposite coefficients. For `a>1`
all terms vanish by degree. Thus the sum is `1-E_p ⊗ E_q`, including total degree zero.
The tensor of the two minimum vertices has augmentation one. Cycles in positive degree,
and degree-zero elements in the augmentation kernel, are boundaries by this identity. -/
theorem tensor_contraction (p q : ℕ) :
    ∃ (H : (n : ℕ) → (simplexChains p ⊗ simplexChains q).X n →ₗ[ℤ]
          (simplexChains p ⊗ simplexChains q).X (n + 1))
      (E : (n : ℕ) → (simplexChains p ⊗ simplexChains q).X n →ₗ[ℤ]
          (simplexChains p ⊗ simplexChains q).X n)
      (ε : (simplexChains p ⊗ simplexChains q).X 0 →ₗ[ℤ] ℤ),
      (∀ (a b : ℕ) (u' : (simplexChains p).X a) (v : (simplexChains q).X b),
        H (a + b) (tensorInclusion p q a b (a + b) rfl (u' ⊗ₜ[ℤ] v)) =
          tensorInclusion p q (a + 1) b (a + b + 1) (by omega)
            (simplexCone p a u' ⊗ₜ[ℤ] v) +
          (-1 : ℤ) ^ a • tensorInclusion p q a (b + 1) (a + b + 1) (by omega)
            (simplexProjection p a u' ⊗ₜ[ℤ] simplexCone q b v)) ∧
      (∀ (a b : ℕ) (u' : (simplexChains p).X a) (v : (simplexChains q).X b),
        E (a + b) (tensorInclusion p q a b (a + b) rfl (u' ⊗ₜ[ℤ] v)) =
          tensorInclusion p q a b (a + b) rfl
            (simplexProjection p a u' ⊗ₜ[ℤ] simplexProjection q b v)) ∧
      ((simplexChains p ⊗ simplexChains q).d 1 0).hom.comp (H 0) =
        LinearMap.id - E 0 ∧
      (∀ n : ℕ,
        ((simplexChains p ⊗ simplexChains q).d (n + 2) (n + 1)).hom.comp (H (n + 1)) +
          (H n).comp ((simplexChains p ⊗ simplexChains q).d (n + 1) n).hom =
        LinearMap.id - E (n + 1)) ∧
      (∀ (u' : (simplexChains p).X 0) (v : (simplexChains q).X 0),
        ε (tensorInclusion p q 0 0 0 rfl (u' ⊗ₜ[ℤ] v)) = augmentation u' * augmentation v) ∧
      Function.Surjective ε := by
  sorry

end AlgebraicTopology.FreeBisimplex
