module

public import Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.Monoidal

/-! # Counital integral diagonal of cubical lattice chains

Source: the agent-written integral cubical diagonal and six-step proof in the DAG
(blueprint: lem-sfb-integral-cubical-chain-diagonal). The route location is paragraph (3)
of the main-20261015 blueprint's direct-images proof; that paragraph does not itself
assert this formula. An exact external reference remains WANTED, as in the DAG source.

Mathlib's tensor complex uses the total differential with sign `(-1)^a` on the second
factor of bidegree `(a,b)`. Its unit is the integers in degree zero. All counit and
augmentation equations below are equations of chain maps, using the canonical unitors.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace IntegralLatticeCubical

/-- The square-zero clause with the canonical index transports, in Mathlib's forward
composition notation. Source: the differential-square clause of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction).

Proof: apply the first clause of `contraction` at degree `n + 2`; the two canonical
transports in `incomingBoundary` identify its target indices with `n + 1` and `n`.
Functoriality of these equality transports gives exactly the same composite. -/
theorem chainComplex_square (r : ℕ) (n : ℕ) :
    ModuleCat.ofHom (incomingBoundary r ((n + 1 : ℕ) : ℤ)) ≫
      ModuleCat.ofHom (incomingBoundary r (n : ℤ)) = 0 := by
  sorry

/-- The cubical complex as a Mathlib chain complex; all objects and differentials are
the existing free modules and signed cubical boundaries, with no choices of data.
Source: the complex clause of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def chainComplex (r : ℕ) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of ℤ (Chains r (n : ℤ)))
    (fun n ↦ ModuleCat.ofHom (incomingBoundary r (n : ℤ))) (chainComplex_square r)

/-- The degree-zero augmentation kills the incoming differential.
Source: the augmentation-boundary clause of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction).

Proof: `chainComplex.d 1 0` is `incomingBoundary r 0`, whose target transport is the
identity. Apply `(contraction r).2.1`, the equation `augmentation.comp (boundary r 1) = 0`.
-/
theorem augmentationMap_condition (r : ℕ) :
    (chainComplex r).d 1 0 ≫ ModuleCat.ofHom (augmentation r) = 0 := by
  sorry

/-- The augmentation to the integers in degree zero, extended by zero in positive degrees.
Source: the augmented-complex clause of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def augmentationMap (r : ℕ) :
    chainComplex r ⟶ (ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  (ChainComplex.toSingle₀Equiv (chainComplex r) (ModuleCat.of ℤ ℤ)).symm
    ⟨ModuleCat.ofHom (augmentation r), augmentationMap_condition r⟩

/-- Translation commutes with the bundled cubical differential.
Source: the translation-equivariance clause of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction).

Proof: the translation-boundary equation in `contraction` at degree `n + 1` is precisely
this equality after transporting the target degree along `(n + 1) - 1 = n`.
The casts leave the lattice point and direction subset unchanged. -/
theorem translationMap_condition (r : ℕ) (w : Fin r → ℤ) (n : ℕ) :
    ModuleCat.ofHom (translate r ((n + 1 : ℕ) : ℤ) w) ≫ (chainComplex r).d (n + 1) n =
      (chainComplex r).d (n + 1) n ≫ ModuleCat.ofHom (translate r (n : ℤ) w) := by
  sorry

/-- The chain map translating every cell by `w`, with unchanged direction subset.
Source: the translation formula of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def translationMap (r : ℕ) (w : Fin r → ℤ) :
    chainComplex r ⟶ chainComplex r :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (translate r (n : ℤ) w))
    (translationMap_condition r w)

/-- The sum `u_A` of the ordered standard basis vectors in the direction set `A`.
Source: the displayed formula for `u_A` in the DAG statement
(blueprint: lem-sfb-integral-cubical-chain-diagonal). -/
def directionSum (r : ℕ) (A : Finset (Fin r)) : Fin r → ℤ :=
  ∑ i ∈ A, unitVector r i

/-- The integral shuffle sign, counting the inversion pairs `c < a` in `A × C`.
Source: the displayed definition of `epsilon(A,C)` in the DAG statement
(blueprint: lem-sfb-integral-cubical-chain-diagonal). -/
def partitionSign (r : ℕ) (A C : Finset (Fin r)) : ℤ :=
  (-1 : ℤ) ^ ((A.product C).filter (fun p ↦ p.2 < p.1)).card

/-- The tensor of two cubical cells, included into total degree `n`; zero if the two
cardinalities do not sum to `n`. In every diagonal summand they do sum to `n`.
This is Mathlib's canonical tensor-summand inclusion, not a new tensor product.
Source: the total-degree convention in the DAG statement and proof step 1
(blueprint: lem-sfb-integral-cubical-chain-diagonal). -/
noncomputable def tensorCell (r n : ℕ) (v w : Fin r → ℤ) (A C : Finset (Fin r)) :
    (HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).X n :=
  HomologicalComplex.ιMapBifunctorOrZero (chainComplex r) (chainComplex r)
    (curriedTensor (ModuleCat.{0} ℤ)) (ComplexShape.down ℕ) A.card C.card n
    (cell r (A.card : ℤ) v A ⊗ₜ[ℤ] cell r (C.card : ℤ) w C)

/-- The finite signed partition formula extended linearly on the existing free basis.
The powerset enumerates exactly the ordered disjoint partitions `(A, I \ A)` of `I`.
Source: the displayed formula for `Delta[v,I]` in the DAG statement
(blueprint: lem-sfb-integral-cubical-chain-diagonal). -/
noncomputable def diagonalComponent (r n : ℕ) :
    Chains r (n : ℤ) →ₗ[ℤ]
      (HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).X n :=
  Finsupp.linearCombination ℤ fun c ↦
    ∑ A ∈ c.2.val.powerset, partitionSign r A (c.2.val \ A) •
      tensorCell r n c.1 (c.1 + directionSum r A) A (c.2.val \ A)

/-- The specified finite integral formula is a translation-equivariant chain map, with
both strict counits and the double augmentation identity. The component equality fixes
the map on the entire free module, rather than assuming a diagonal as extra data.
The final clause is the rank-zero normalization under the existing augmentation
identification of the unique vertex with `1`.

Source: the full agent-written DAG statement and its six-step finite-sum proof
(blueprint: lem-sfb-integral-cubical-chain-diagonal).

Proof plan:
1. Use `lem-sfb-integral-lattice-cubical-contraction` for boundary squared zero and
augmentation times boundary zero, and the existing free-module and tensor-product
universal properties (`def-weil-pbc-free-module`, `def-weil-pbc-module-tensor-product`).
Each finite partition term has total degree `|I|`, so the displayed linear maps exist.
The tensor differential squares to zero: its cross coefficients are
`(-1)^(a-1) + (-1)^a = 0`; at `a = 0` the first boundary is zero directly.
2. Fix a removed direction `i` and partition `B,C` of the remaining directions.
Let `p` count `b < i`, `q` count `c < i`, `t` count `i < b`, and `N` count `c < b`.
The first-factor boundary sign is `(-1)^(N+q+p)` and the second-factor sign, including
the tensor sign, is `(-1)^(N+t+|B|+q)`. Since `|B| = p+t`, they agree.
3. With common sign `s`, the four terms are
`s ([v+u_i,B] tensor [v+u_B+u_i,C] - [v,B] tensor [v+u_B+u_i,C])` and
`s ([v,B] tensor [v+u_B+u_i,C] - [v,B] tensor [v+u_B,C])`.
The middle terms cancel, leaving exactly the diagonal of the `i`-face boundary.
Every term has a unique removed direction and remaining partition. Sum to obtain the
chain-map equation (`def-weil-pbc-module-chain-complex-homology`); empty directions
and zero source degrees give zero on both sides.
4. Translation sends both vertices to `v+w` and `v+w+u_A`; commutativity of lattice
addition identifies this with translation in both tensor factors, with unchanged sign.
5. Extend the augmentation by zero in positive degrees; it is a chain map by step 1.
After left augmentation only `A` empty survives, with sign one. After right augmentation
only `C` empty survives, again with sign one. The standard unitors send `1 tensor x` and
`x tensor 1` to `x`. Bilinearity proves these are the canonical unit identifications.
6. Double augmentation is zero in positive degree because one part is nonempty; in degree
zero its unique summand goes to one. Thus it is the augmentation as a chain map.
For rank zero there is one vertex and one empty partition, giving `1 tensor 1`.
-/
theorem diagonal (r : ℕ) :
    ∃ Δ : chainComplex r ⟶
        HomologicalComplex.tensorObj (chainComplex r) (chainComplex r),
      (∀ n : ℕ, (Δ.f n).hom = diagonalComponent r n) ∧
      (∀ w : Fin r → ℤ,
        translationMap r w ≫ Δ =
          Δ ≫ HomologicalComplex.tensorHom (translationMap r w) (translationMap r w)) ∧
      (Δ ≫ HomologicalComplex.tensorHom (augmentationMap r) (𝟙 (chainComplex r))) ≫
        (HomologicalComplex.leftUnitor (chainComplex r)).hom = 𝟙 (chainComplex r) ∧
      (Δ ≫ HomologicalComplex.tensorHom (𝟙 (chainComplex r)) (augmentationMap r)) ≫
        (HomologicalComplex.rightUnitor (chainComplex r)).hom = 𝟙 (chainComplex r) ∧
      (Δ ≫ HomologicalComplex.tensorHom (augmentationMap r) (augmentationMap r)) ≫
        (HomologicalComplex.leftUnitor
          (HomologicalComplex.tensorUnit (ModuleCat.{0} ℤ) (ComplexShape.down ℕ))).hom =
          augmentationMap r ∧
      (r = 0 → (Δ.f 0) (cell r 0 0 ∅) = tensorCell r 0 0 0 ∅ ∅) := by
  sorry

end IntegralLatticeCubical
