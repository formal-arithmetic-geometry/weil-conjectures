## Worker report

The module `Sheaf.LinearAlgebra.RootDatumLatticeEmbedding` states
`RootDatumLattice.lattice_embedding`, with proof `sorry`, and defines the canonical
objects appearing in that statement. The node's statement and dependencies are
unchanged. There are no new nodes or dependency repairs and no disputed statements.

Sources read: Milne, Algebraic Groups (2017), printed pp. 614--618,
C.29, C.34--C.35, C.41--C.44 (PDF pages 626--630), including the statement
and proof of the rational root/central decomposition and the weight-lattice
inclusions. The node's nine proof steps are included in the theorem docstring.
The rank and finite-index claims follow the node's expanded denominator arguments.
The named exercise is the source recorded in the node for the rational projection
form of this comparison.

Hypotheses, matched individually:

- A free abelian group of finite rank is `M : Type u`, `[AddCommGroup M]`,
  `[Module.Free ℤ M]`, `[Module.Finite ℤ M]`. The integer action is the canonical
  one for an additive commutative group; no extra structure is supplied.
- A finite subset of nonzero roots is `R : Set M`, `hR : R.Finite`,
  `hzero : (0 : M) ∉ R`.
- The bijection to a subset of the integral dual is `c : R → M →ₗ[ℤ] ℤ`
  with `hc : Function.Injective c`. Its codomain subset is its image, so
  injectivity is exactly the prescribed bijection to a subset, with no
  surjectivity onto the whole dual imposed.
- The normalization is `hnorm : ∀ a : R, c a a = 2`.
- The integral reflections permute the roots by
  `hperm : ∀ a : R, Set.BijOn (Module.preReflection (a : M) (c a)) R R`.
  Mathlib's preReflection is precisely `m - c a m • a`.
- The generated automorphism group is finite by `hW : Finite
  (Subgroup.closure (Set.range (fun a : R ↦ Module.reflection (hnorm a))))`.
  Mathlib reflection is the same map bundled as an involutive integer-linear
  automorphism, and integer-linear automorphisms are the automorphisms of the
  underlying abelian group.
- Reducedness is `hred`, the set equality between the rational line through
  `1 ⊗ a` intersected with the image of `R`, and `{1 ⊗ a, -(1 ⊗ a)}`.

Objects and every conclusion clause:

- `E` is `ℚ ⊗[ℤ] M`. Tensor symmetry identifies it canonically with the node's
  `M ⊗[ℤ] ℚ`. The map of the integral lattice is
  `TensorProduct.mk ℤ ℚ M 1`, sending `m` to `1 ⊗ m`.
- `rootSpan R` is `Submodule.span ℚ` of the image of `R`, hence exactly `V`.
  `root R a` is this same tensor, regarded as a vector in `V`.
- `rationalCoroot` composes `c` with the integral inclusion into `ℚ` and
  applies Mathlib `LinearMap.liftBaseChange ℚ`. Thus its value on `q ⊗ m`
  is `q * c(m)`, the canonical rational extension. `coroot R c a` is its
  composition with `V.subtype`, exactly the restricted functional.
- `centralSpace R c` is the infimum of the kernels of these extensions,
  exactly the common annihilator `Z`.
- The existential `h : IsCompl (rootSpan R) (centralSpace R c)` asserts
  `E = V ⊕ Z`. This is a conclusion, not a hypothesis. Mathlib
  `projectionOnto` for `h` and `h.symm` gives the two canonical projections.
- The first conjunct is `Submodule.span ℚ (Set.range (root R)) = ⊤`,
  the assertion that the roots span `V`.
- The next conjunct gives `coroot R c a (root R a) = 2`.
- The next gives `Set.BijOn` of each restricted root reflection on the
  root set in `V`.
- The integrality clause is `∀ a b : R, ∃ n : ℤ,
  coroot R c a (root R b) = (n : ℚ)`.
- Reducedness inside `V` is the next rational-line/intersection equality,
  again with precisely the root and its negative on the right.
- `Submodule.span ℚ (Set.range (coroot R c)) = ⊤` says that the restricted
  coroots span the entire rational dual of `V`.
- Uniqueness quantifies over each rational functional `f` on `V` with
  `f (root R a) = 2` and whose preReflection maps the root set into itself,
  and concludes `f = coroot R c a`. This is the stronger usual root-set
  characterization explicitly established in proof step 4 of the node.
- `weightLattice R c` is the intersection of the preimages of the range
  of `ℤ → ℚ` under the restricted coroots (viewed as integer-linear maps).
  It is therefore precisely the stated `P`, with its actual additive data.
- `Nonempty (Module.Basis (Fin (Module.finrank ℚ (rootSpan R))) ℤ
  (weightLattice R c))` is freeness of `P` of rank `dim V`, including
  finite generation, rather than only a potentially infinite free-module assertion.
- `rootLattice R` is `Submodule.span ℤ (Set.range (root R))`, exactly `Q_R`.
  Its inclusion in `P` is a conjunct. Finiteness of its index is expressed
  as `Finite (P ⧸ (rootLattice R).comap P.subtype)`, the actual quotient
  of `P` by the included root lattice, with no arbitrary inclusion map.
- `centralLattice R c h` is the range of the composite of the integral
  lattice map and the central projection, exactly `C = π_Z(M)`.
  A basis indexed by `Fin (Module.finrank ℚ (centralSpace R c))` gives
  precisely its finite freeness and rank `dim Z`.
- The existential `hp` asserts that every projected root component of
  an integral lattice element belongs to `P`, exactly `π_V(M) ⊆ P`.
  It is a conclusion, not an added integrality hypothesis.
- `embedding R c h hp` is constructed as the product of the canonical
  root projection with codomain restricted using `hp`, and the central
  projection with codomain restricted to its image. No map is chosen.
  A product is the two-term direct sum of abelian groups.
- Its injectivity is `Function.Injective (embedding R c h hp)`.
  `Finite ((P × C) ⧸ LinearMap.range (embedding R c h hp))` states
  exactly that its cokernel is finite.
- The root identity is stated componentwise: its first coordinate,
  coerced to `V`, equals `root R a`, and its second coordinate equals zero.
  This avoids inserting a separately assumed proof that the root lies in `P`.
- The final conjunct states `(c a m : ℚ) = coroot R c a (π_V (1 ⊗ m))`,
  exactly the required equality between the original and projected coroot evaluations.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`,
  `Module.Free` (class and docstring read, with its basis-existence field).
- `def-weil-submodule-span`: the node's `mathlib_match`,
  `Mathlib.LinearAlgebra.Span.Defs`, `Submodule.span` (definition and
  docstring read: the infimum of submodules containing the set).
- Proof input `lem-sfb-finite-spanning-reflection-uniqueness`:
  `Mathlib.LinearAlgebra.Reflection`, `Module.Dual.eq_of_preReflection_mapsTo`;
  its finite/spanning, normalization and MapsTo signature was read in full.
  This module is publicly imported because its reflection definitions also
  occur in the statement.
- Proof input `lem-weil-subgroup-finite-free-abelian-group-free`:
  `Mathlib.LinearAlgebra.FreeModule.PID`, `Submodule.basisOfPid`;
  the finite-index-basis hypothesis and finite integral basis output were read.
- Proof input `lem-trf-fg-torsionfree-group-free`: the same PID module,
  `Module.basisOfFiniteTypeTorsionFree'`; the finite-type, torsion-free
  hypotheses and sigma of a natural number and finite basis were read.
  The PID module is imported privately as a proof dependency.

No dependency record needs repair. All lattice/subspace helpers belong to the
objects introduced by this very statement, so they are declared in its own module
and listed in `lean.declarations`, as permitted for canonical constructions.
There is no second definition of RootPairing or RootSystem: the listed one-sided
root-system clauses of the node are rendered explicitly, using Mathlib's spans,
linear maps, reflections, projections, submodule ranges and quotients.

Edge cases checked before and after writing:

- `R = ∅`: the rational root span is bottom; its restricted root set is empty;
  the central kernel intersection is top; the weight lattice in the zero
  root space is zero. The central projection is the identity after the
  evident subtype identification. `C` is the image of `M`, and `j` is
  `(0,id)` after that identification. Every root-indexed condition is
  vacuous; the dual of the zero space is zero, so the dual spanning assertion
  still holds. No `Nonempty R`, positive rank, or nontrivial module is assumed.
- `M = 0`: `hzero` forces `R = ∅`; all basis indices are empty and all
  quotient groups are trivial, hence finite.
- Rank-one semisimple case `M = ℤ`, roots `{1,-1}`, coroots `±2 id`:
  `V = ℚ`, `Z = 0`, `P = (1/2)ℤ`, and the image of `j` has index two.
  The definition therefore does not accidentally force the image to be all of `P × C`.
- Mixed case `M = ℤ²`, roots `±(1,0)`, positive-root coroot
  `c(x,y) = 2x + y`: the rational central direction is `ℚ(-1,2)`,
  `π_V(x,y) = (x+y/2,0)`, `π_Z(x,y) = (-y/2,y)`,
  `P = (1/2)ℤ(1,0)`, and `C = ℤ(-1/2,1)`.
  In these integral target bases `j(x,y) = (2x+y,y)` and its image has
  index two. This checks the embedding direction, the projected central
  lattice (rather than the integral kernel), and coroot compatibility.
- Universe `u` is explicit and arbitrary. No universe equality, dimension
  positivity, choice of basis in the input, or strengthened root-pairing
  assumption has been introduced.

Searches made:

- `msearch.py leanfinder`: "A free abelian group with a finite reduced root
  set and coroot functionals embeds with finite cokernel in its weight
  lattice plus the projected central lattice". Eight hits, including
  `RootDatum`, `RootSystem.mk'`, `RootPairing.mk''` and coroot/root span
  results; none states the whole theorem from these one-sided hypotheses.
- `msearch.py loogle`: `RootPairing, "lattice"`. Two invariant-root-submodule
  order-instance hits, neither the statement nor its weight lattice.
- `msearch.py grep`: `weightLattice|weight.lattice|liftBaseChange` in
  `LinearAlgebra`. No hits. The lift API was then found by direct source
  search in `Mathlib.RingTheory.TensorProduct.Basic`, and used directly.
- `msearch.py leansearch`: "A finite reduced root datum decomposes rationally
  as root span plus coroot annihilator and its character lattice embeds with
  finite cokernel into the weight lattice plus a central lattice".
  Eight hits including `RootPairing.isCompl_rootSpan_ker_rootForm` and
  `RootPairing.IsRootSystem.mk`. Read `RootPairing` and `RootDatum` definitions,
  and `isCompl_rootSpan_ker_rootForm` and `ker_rootForm_eq_dualAnnihilator`
  in `RootSystem/Finite/Nondegenerate.lean`: these require an already
  constructed paired root datum and give neither this integral embedding
  nor the conversion from the present hypotheses. They do not match the item.
- Direct `rg` searches for root datum, `rootDatum`, `weightLattice`, and
  the item's blueprint id in `lean/WeilConjectures` and `lean/Sheaf`:
  no duplicate. Focused searches for `rootSpan`, `rootLattice`,
  `rationalCoroot`, `centralSpace` in their LinearAlgebra directories and
  the Sheaf GroupTheory directory found none of these constructions.
- `tools/blueprint_refs.py search 'weight lattice'`: zero blueprint nodes.
  The DAG's root-system/lattice hits are this item and its downstream
  realization/enlargement consumers. No independent helper notion is added.
- Direct rationalization search found the existing
  `AddCommGroup.rationalizationMap`; its real definition is precisely
  `TensorProduct.mk ℤ ℚ M 1` viewed as an additive map. This module uses
  the Mathlib tensor map itself and does not introduce a duplicate
  rationalization-map definition.

Validation: `scompile.py Q145 lem-sfb-root-datum-lattice-embedding` compiled
both the sandbox module and its intended library module with no errors or
unexpected warnings. The initial compile diagnosed that `Module.Finite`
needed its public definition import; `Mathlib.RingTheory.Finiteness.Defs`
was added, and the clean compile then passed. `set_option autoImplicit false`
is present. The sole postponed proof is the node's named theorem; every
helper definition has actual data and uses existing Mathlib structural proofs.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
