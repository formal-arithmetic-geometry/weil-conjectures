/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.CoherentGroupPresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Polynomial.BigOperators

import Sheaf.AlgebraicGeometry.DiagonalizableGroup
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.Topology.ModuleObjectOpenDescent
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-! # Coherent weight decomposition for a trivial split-torus action

Source: Stacks Project, Groupoids, Tags 03LF, 0EKK and 0EKL;
Milne, Algebraic Groups, Theorem 12.12, pp.234--235
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

All actions are forward fibre actions. The character group consists of actual
homomorphisms of group schemes, and the character ring is its integral group ring.
The tensor source is written R ⊗ℤ G₀ so its standard left R-module structure is
available; the usual tensor symmetry identifies this with the displayed G₀ ⊗ℤ R.
The normalization below is exactly [A] ⊗ e^χ ↦ [A with character χ].
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.TrivialTorusCoherent

variable {F : Type u} [Field F]

/-- Every coherent linearization has its unique finite coherent character
subobjects, with their actual sum inclusions.

Source: Stacks, Tags 0EKK and 0EKL; Milne, Theorem 12.12, pp.234--235
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: steps 1--3 of the node. Identify T with the diagonalizable group of its
characters using lem-sfb-multiplicative-character-antiduality and
 def-sfb-diagonalizable-group. On Spec A, translate descent to the coaction
by lem-sfb-hopf-coaction-linearization, using the affine tilde/gamma adjunction
and module-pullback-affine-sections. With the forward convention the coaction
is sum p_χ(m) tensor e^(-χ). Compare coefficients in the counit and coassociativity
identities: sum p_χ = id, p_χ² = p_χ, and p_ψ p_χ = 0 for ψ ≠ χ. Their images
are exactly the weight modules, giving the direct sum and uniqueness. Testing
at the universal torus point proves uniqueness over nonreduced algebras too.
Coherent-ft-locnoeth and quasi-coherent-finite-type-affine give finite generators;
the union of their coefficient supports is finite. Affine-section-base-change
identifies restriction with scalar extension, carrying each projection to its
scalar extension. Module-object-open-descent glues their images across affine
subopens of overlaps. A finite affine cover, from quasi-compactness, makes the
global weight support finite. Finite generation locally gives coherence by
pqf-lem-coherent-ft-locnoeth. Rank zero and the empty scheme are included. -/
theorem existsUnique_weightDecomposition
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (M : Linearized T Z) :
    ∃! P : Character T → Subobject M.moduleObj, IsWeightDecomposition M P := by
  sorry

/-- Every ordinary coherent module admits the specified pure-character
linearization, uniquely on a fixed underlying module.

Source: Stacks, Tag 03LF and Milne, Theorem 12.12
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: on every test scheme let t act by multiplication by χ(t). The character
law gives identity and multiplication, and pullback of functions gives
naturality. Inverting χ(t) gives the inverse. This is the scalar character
linearization of step 8; its value on every test scheme fixes it uniquely. -/
theorem pure_character_exists
    (T : Grp (Over (Spec (.of F)))) (Z : Over (Spec (.of F)))
    (A : Coherent Z) (χ : Character T) :
    ∃ M : Linearized T Z, Nonempty (M.moduleObj ≅ A.val) ∧ IsPure M χ := by
  sorry

/-- Taking a character summand is exact on all equivariant short exact sequences.
The commuting squares specify its induced maps uniquely.

Source: Stacks, Tag 0EKL (blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: step 4. An equivariant map commutes with coactions by
lem-sfb-hopf-coaction-linearization_morphisms, hence with each coefficient
projection. Its restrictions to the weight submodules give the unique maps.
For surjectivity, project any local lift of a quotient section to its χ-part;
this is still a lift. Kernels and images are computed componentwise. The
coherent-kernel-cokernel-locnoeth lemma ensures coherence throughout. -/
theorem weight_summand_exact
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (A B C : Linearized T Z)
    (f : A.moduleObj ⟶ B.moduleObj) (g : B.moduleObj ⟶ C.moduleObj)
    (hf : Equivariant A B f) (hg : Equivariant B C g)
    (hex : ExactTriple A.moduleObj B.moduleObj C.moduleObj f g)
    (P : Character T → Subobject A.moduleObj)
    (Q : Character T → Subobject B.moduleObj)
    (S : Character T → Subobject C.moduleObj)
    (hP : IsWeightDecomposition A P) (hQ : IsWeightDecomposition B Q)
    (hS : IsWeightDecomposition C S) (χ : Character T) :
    ∃! fg : ((P χ : Z.left.Modules) ⟶ (Q χ : Z.left.Modules)) ×
        ((Q χ : Z.left.Modules) ⟶ (S χ : Z.left.Modules)),
      fg.1 ≫ (Q χ).arrow = (P χ).arrow ≫ f ∧
      fg.2 ≫ (S χ).arrow = (Q χ).arrow ≫ g ∧
      ExactTriple (P χ : Z.left.Modules) (Q χ : Z.left.Modules)
        (S χ : Z.left.Modules) fg.1 fg.2 := by
  sorry

/-- Weight summands commute with restriction and every base-field extension.
The pullback statement retains its meaning even if the extended base is not
Noetherian. It gives the actual pulled-back character summands and sum map.

Source: Stacks, Tag 0EKL (blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: steps 3--4. On an affine chart tensor the split sum identity with the
new coefficient algebra. Every projection becomes 1 tensor p_χ, with no
flatness assumption. Coefficient comparison at the universal torus point
identifies these images with the character summands of the pulled-back
linearization. Module-pullback-affine-sections and canonical affine gluing
identify this calculation with restriction and field extension of sheaves. -/
theorem weight_summand_restriction_fieldExtension
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (M : Linearized T Z) (P : Character T → Subobject M.moduleObj)
    (hP : IsWeightDecomposition M P) :
    (∀ U : Z.left.Opens, IsPulledBackDecomposition M P (openInclusion Z U)) ∧
      (∀ (K : Type u) [Field K] [Algebra F K],
        IsPulledBackDecomposition M P (fieldProjection Z K)) := by
  sorry

/-- Character summands of vector bundles are vector bundles; vanishing of their
fibres at every closed point forces the summand itself to vanish.

Source: Stacks, Tags 00NX, 01C6 and 005E
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: steps 5, 9--10. Each affine projection image is a direct summand of a
finite free module, hence finite projective. The finite-projective-standard-free-cover
lemma, affine-tilde-gamma-adjunction and spec-tilde-free-module make its sheaf
finite locally free. Its rank fibres are open by local bases and closed since
their complements are unions of the other rank fibres. If a summand is nonzero,
its nonzero-rank locus is nonempty and clopen. Scheme sobriety gives T₀, and
lem-sc-quasi-compact-kolmogorov-closed-point supplies a point closed in Z in
that locus. Its fibre has positive dimension, a contradiction. No Jacobson or
finite-type hypothesis is needed. -/
theorem weight_summand_locallyFree_and_closedFibres
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (M : Linearized T Z) (P : Character T → Subobject M.moduleObj)
    (hP : IsWeightDecomposition M P) (χ : Character T) :
    (M.moduleObj.IsFiniteLocallyFree →
      (P χ : Z.left.Modules).IsFiniteLocallyFree) ∧
      ((P χ : Z.left.Modules).IsFiniteLocallyFree →
        (∀ x : Z.left, IsClosed ({x} : Set Z.left) →
        Subsingleton (Scheme.Modules.residueFiber (P χ : Z.left.Modules) x)) →
        IsZero (P χ : Z.left.Modules)) := by
  sorry

/-- Tensor products exist with their canonical linearization and add weights.
This includes the full convolution formula for the character summands.

Source: Stacks, Tag 03LF and Tag 0EKL
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: step 6. Use the tensor coaction formula of
lem-sfb-hopf-coaction-linearization_tensor: multiplying e^(-χ) and e^(-ψ)
gives e^(-(χ+ψ)). The affine tensor sections comparison identifies this with
the usual tensor product of sheaves. Distribute the finite weight sums and
use the uniqueness of their coefficient projections. The resulting maps to
the weight-summand are the restrictions of the tensors of the inclusion maps;
their sum is an isomorphism. Coherence follows locally from finite presentations
over the Noetherian coefficient rings. -/
theorem tensor_weight_convolution
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (M N : Linearized T Z) :
    (∃ L : Linearized T Z, IsTensor M N L) ∧
      (∀ (L : Linearized T Z), IsTensor M N L →
        ∀ (P : Character T → Subobject M.moduleObj)
          (Q : Character T → Subobject N.moduleObj)
          (S : Character T → Subobject L.moduleObj),
          IsWeightDecomposition M P → IsWeightDecomposition N Q →
          IsWeightDecomposition L S →
          ∀ (e : L.moduleObj ≅ M.moduleObj ⊗ N.moduleObj),
            IsTensorWith M N L e →
            ∀ weight : Character T,
              ∃ f : ∀ a : {p : Character T × Character T // p.1 + p.2 = weight},
                (P a.val.1 : Z.left.Modules) ⊗ (Q a.val.2 : Z.left.Modules) ⟶
                  (S weight : Z.left.Modules),
                Nonempty (IsColimit (Cofan.mk (S weight : Z.left.Modules) f)) ∧
                ∀ a, f a ≫ (S weight).arrow =
                  ((P a.val.1).arrow ⊗ₘ (Q a.val.2).arrow) ≫ e.inv) := by
  sorry

/-- The character comparison is the unique R-linear isomorphism with the specified
normalization on every pure-character coherent module.

Source: Stacks, Tag 0EKL (blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: step 8. Send each pure-character generator to its equivariant class.
Exactness of weight extraction respects the short exact sequence relations.
Conversely send a linearized module to the finite sum of its ordinary weight
classes times their characters. The finite weight decomposition makes the two
maps inverse. Twisting shifts every weight, so both maps are R-linear. -/
theorem existsUnique_characterComparison
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left] :
    ∃! φ : CharacterRing T ⊗[ℤ] OrdinaryGroup Z ≃ₗ[CharacterRing T]
        EquivariantGroup T Z, IsCharacterComparison φ := by
  sorry

/-- Tensor operators by vector bundles exist, with their generator normalization.

Source: Stacks, Tags 00NX and 0EKL
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: steps 5--8. Locally tensoring with a finite free module is a finite direct
sum, hence preserves coherence and short exact sequences. Local bases glue these
facts and the tensor linearization. Thus tensoring respects the defining relations
of each coherent group, giving the indicated operators. Their values on generators
force uniqueness; equivariant tensoring commutes with character twists. -/
theorem tensor_operators
    (T : Grp (Over (Spec (.of F))))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left] :
    (∀ E : Z.left.Modules, E.IsFiniteLocallyFree →
      (∀ A : Coherent Z, ∃ B : Coherent Z, Nonempty (B.val ≅ E ⊗ A.val)) ∧
      ∃! op : OrdinaryGroup Z →+ OrdinaryGroup Z, IsOrdinaryTensorOperator E op) ∧
    (∀ E : Linearized T Z, E.moduleObj.IsFiniteLocallyFree →
      (∀ A : Linearized T Z, ∃ B : Linearized T Z, IsTensor E A B) ∧
      ∃! op : Module.End (CharacterRing T) (EquivariantGroup T Z),
        IsEquivariantTensorOperator E op) := by
  sorry

/-- Under the comparison, tensoring by E is the sum of tensoring by its weight
bundles, with the corresponding character factors.

Source: Stacks, Tag 0EKL (blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: steps 6 and 8. Tensor the finite character decomposition with a
pure-character coherent module. The resulting summands have characters χ + ψ.
Their short exact/direct sum relations give the formula on generators, and
R-linearity gives it on the full coherent group. -/
theorem comparison_tensor_weights
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (E : Linearized T Z) (hE : E.moduleObj.IsFiniteLocallyFree)
    (P : Character T → Subobject E.moduleObj) (hP : IsWeightDecomposition E P)
    (φ : CharacterRing T ⊗[ℤ] OrdinaryGroup Z ≃ₗ[CharacterRing T]
      EquivariantGroup T Z) (hφ : IsCharacterComparison φ)
    (k : ℕ) (χ : Fin k → Character T) (hinj : Function.Injective χ)
    (hsupp : ∀ a, (¬ IsZero (P a : Z.left.Modules)) ↔ ∃ i, χ i = a)
    (op : Module.End (CharacterRing T) (EquivariantGroup T Z))
    (hop : IsEquivariantTensorOperator E op)
    (ops : Fin k → OrdinaryGroup Z →+ OrdinaryGroup Z)
    (hops : ∀ i, IsOrdinaryTensorOperator (P (χ i) : Z.left.Modules) (ops i)) :
    ∀ (ψ : Character T) (x : OrdinaryGroup Z),
      op (φ (AddMonoidAlgebra.single ψ 1 ⊗ₜ[ℤ] x)) =
        ∑ i, φ (AddMonoidAlgebra.single (χ i + ψ) 1 ⊗ₜ[ℤ] ops i x) := by
  sorry

/-- The exterior-power identity holds as a polynomial of tensor operators.
The weight summands on the right are given the trivial linearization; their
characters occur only through the explicit e^(jχ) scalars. The product is in the
listed order, so it is meaningful even in the noncommutative endomorphism ring.

Source: Stacks, exterior algebra, Tag 00DM
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: step 7. On simultaneous local bases concatenate the bases of the weight
bundles. Splitting wedge monomials by their numbers of factors from each bundle
gives the exterior direct-sum isomorphism. A j-fold wedge from the χ-part has
forward character jχ. The free exterior-power basis lemma identifies these
maps, which glue because wedge is functorial. Bounded local ranks and a finite
affine cover bound every exterior degree. Tensor operators and the coherent-group
relations turn the direct-sum isomorphism into the displayed polynomial identity. -/
theorem exterior_operator_polynomial
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (E : Linearized T Z) (hE : E.moduleObj.IsFiniteLocallyFree)
    (P : Character T → Subobject E.moduleObj) (hP : IsWeightDecomposition E P)
    (k : ℕ) (χ : Fin k → Character T) (hinj : Function.Injective χ)
    (hsupp : ∀ a, (¬ IsZero (P a : Z.left.Modules)) ↔ ∃ i, χ i = a) :
    ∃ (b : ℕ) (L : ℕ → Linearized T Z)
      (A : Fin k → ℕ → Linearized T Z)
      (H : ℕ → Module.End (CharacterRing T) (EquivariantGroup T Z))
      (J : Fin k → ℕ → Module.End (CharacterRing T) (EquivariantGroup T Z)),
      (∀ q, IsExterior E q (L q) ∧ (L q).moduleObj.IsFiniteLocallyFree ∧
        IsEquivariantTensorOperator (L q) (H q)) ∧
      (∀ i j, Nonempty ((A i j).moduleObj ≅
          Scheme.Modules.exteriorSheaf (P (χ i) : Z.left.Modules) j) ∧
        IsPure (A i j) 0 ∧ (A i j).moduleObj.IsFiniteLocallyFree ∧
        IsEquivariantTensorOperator (A i j) (J i j)) ∧
      (∀ q, b < q → H q = 0 ∧ ∀ i, J i q = 0) ∧
      (∑ q ∈ Finset.range (b + 1), Polynomial.monomial q (H q)) =
        (List.ofFn (fun i : Fin k =>
          ∑ j ∈ Finset.range (b + 1), Polynomial.monomial j
            ((AddMonoidAlgebra.single (j • χ i) 1 : CharacterRing T) • J i j))).prod := by
  sorry

/-- A finite family of vector bundles has a finite clopen constant-rank partition;
ordinary and equivariant groups and their character comparison restrict by products.

Source: Stacks, Tags 01C6, 01IA and 0EKL
(blueprint: lem-sfb-trivial-torus-coherent-weight-decomposition).

Proof: steps 9 and 8. Rank is locally constant by finite local bases. Quasi-
compactness makes its image finite; intersect the rank fibres of the finitely
many bundles and discard empty intersections. These are disjoint clopens covering
Z. Restriction and extension by zero along their inclusions are mutually inverse
on coherent modules, linearizations and exact sequences. They induce the two
product isomorphisms below. Pure-character generators restrict to pure-character
generators, so their normalized comparisons commute. Tensor and exterior powers
are computed componentwise on the disjoint union. -/
theorem finite_clopen_rank_partition
    (T : Grp (Over (Spec (.of F)))) (r : ℕ)
    (hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (Z : Over (Spec (.of F))) [IsLocallyNoetherian Z.left] [CompactSpace Z.left]
    (n : ℕ) (E : Fin n → Z.left.Modules)
    (hE : ∀ j, (E j).IsFiniteLocallyFree) :
    ∃ (m : ℕ) (U : Fin m → Z.left.Opens),
      (∀ i, IsClopen (U i : Set Z.left)) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧ iSup U = ⊤ ∧
      (∀ i j, ∃ d : ℕ,
        (testModule (E j) (openInclusion Z (U i))).IsFiniteLocallyFreeOfRank d) ∧
      ∃ (π : OrdinaryGroup Z ≃ₗ[ℤ] ∀ i, OrdinaryGroup (openBase Z (U i)))
        (piEq : EquivariantGroup T Z ≃ₗ[CharacterRing T]
          ∀ i, EquivariantGroup T (openBase Z (U i)))
        (φ : CharacterRing T ⊗[ℤ] OrdinaryGroup Z ≃ₗ[CharacterRing T]
          EquivariantGroup T Z)
        (φs : ∀ i, CharacterRing T ⊗[ℤ] OrdinaryGroup (openBase Z (U i))
          ≃ₗ[CharacterRing T] EquivariantGroup T (openBase Z (U i))),
        IsCharacterComparison φ ∧ (∀ i, IsCharacterComparison (φs i)) ∧
        (∀ (A : Coherent Z) i,
          (∃ B : Coherent (openBase Z (U i)),
            Nonempty (B.val ≅ testModule A.val (openInclusion Z (U i)))) ∧
          ∀ B : Coherent (openBase Z (U i)),
            Nonempty (B.val ≅ testModule A.val (openInclusion Z (U i))) →
              π (ordinaryClass A) i = ordinaryClass B) ∧
        (∀ (M : Linearized T Z) i,
          (∃ N : Linearized T (openBase Z (U i)),
            IsRestriction (openInclusion Z (U i)) M N) ∧
          ∀ N : Linearized T (openBase Z (U i)),
            IsRestriction (openInclusion Z (U i)) M N →
              piEq (equivariantClass M) i = equivariantClass N) ∧
        (∀ (x : CharacterRing T ⊗[ℤ] OrdinaryGroup Z) i,
          piEq (φ x) i = φs i (TensorProduct.map (LinearMap.id :
            CharacterRing T →ₗ[ℤ] CharacterRing T)
            ((LinearMap.proj i).comp π.toLinearMap) x)) ∧
        (∀ (V : Z.left.Modules) (op : OrdinaryGroup Z →+ OrdinaryGroup Z),
          V.IsFiniteLocallyFree → IsOrdinaryTensorOperator V op →
          ∀ i (opi : OrdinaryGroup (openBase Z (U i)) →+
            OrdinaryGroup (openBase Z (U i))),
          IsOrdinaryTensorOperator (testModule V (openInclusion Z (U i))) opi →
          ∀ x, π (op x) i = opi (π x i)) ∧
        (∀ (V : Linearized T Z)
          (op : Module.End (CharacterRing T) (EquivariantGroup T Z)),
          V.moduleObj.IsFiniteLocallyFree → IsEquivariantTensorOperator V op →
          ∀ i (Vi : Linearized T (openBase Z (U i)))
            (opi : Module.End (CharacterRing T) (EquivariantGroup T (openBase Z (U i)))),
          IsRestriction (openInclusion Z (U i)) V Vi →
          IsEquivariantTensorOperator Vi opi →
          ∀ x, piEq (op x) i = opi (piEq x i)) := by
  sorry

end AlgebraicGeometry.TrivialTorusCoherent
