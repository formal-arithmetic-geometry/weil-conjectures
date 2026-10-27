## Worker report

The module `Sheaf.RepresentationTheory.EquivariantContinuousCochainPrism` states
`ContinuousCohomology.exists_equivariantContinuousPrism`, with one `sorry` proof.
Its accompanying structure `ContinuousCohomology.EquivariantContinuousPrism` packages
exactly the node's complexes, evaluations, operators, and identities. No mathematical
claim is proved, and no definition takes data from a postponed existence theorem.
Only the item's `lean` field changes. There are no new or repaired dependency nodes,
statement corrections, or disputed statements.

### Hypotheses and clauses

- A topological field is `E : Type u`, `[Field E]`, `[TopologicalSpace E]`, and
  `[IsTopologicalDivisionRing E]`. This uses the dependency `def-weil-field`'s
  `Field` match, read in `Mathlib.Algebra.Field.Defs` (line 180), imported through
  `Mathlib.Topology.Algebra.Field`. No assumption on characteristic is imposed.
- A topological group is `G : Type v`, `[Group G]`, `[TopologicalSpace G]`, and
  `[IsTopologicalGroup G]`. It is unrestricted by compactness or separation.
  The node's preliminary group J is the same arbitrary group, named G throughout.
- The finite set, including the empty set, is `S : Type z` with `[Fintype S]`.
  The functions `a : S → C(G,G)` are exactly the specified continuous maps.
- The permutation hypothesis is `hperm : ∀ g, ∃ π : Equiv.Perm S, ∀ s x,
  a s (g*x) = g*a (π s) x`. The permutation may depend arbitrarily on g and works
  simultaneously for every s and x. Neither multiplicative compatibility nor
  continuity of these permutations is assumed.
- A topological vector space with a linear group action is `A : TopRep.{w} E G`.
  Its fields supply the additive group, module, topology, continuous addition and
  jointly continuous scalar multiplication. Its `ρ : ContRepresentation E G A`
  supplies continuous linear operators satisfying the group laws. The separate
  binder `hA : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)` imposes exactly the
  required joint continuity of the action (not merely continuity for fixed g).
- `D A hA` is supplied simultaneously for every such coefficient representation.
  The structure's `B` is an integer-indexed complex in abstract `ModuleCat E`.
  Its `eval n` is an injective E-linear map into the functions on `Fin (n+1) → G`.
  `range` says its image is EXACTLY the jointly continuous functions satisfying
  `F (fun i ↦ g*x i) = A.ρ g (F x)`. Thus it specifies B^n, with precisely the
  pointwise vector-space structure, up to unique evaluation-preserving isomorphism;
  it does not substitute arbitrary spaces or an iterated-continuous-map model.
  The ambient carrier universe `max v w` contains the actual function space;
  scalar, group, coefficient, and finite-index universes are explicitly bound.
- `delta` specifies the differential by the sum over `j : Fin (n+2)` with
  scalar `(-1 : E)^j.val` and tuple `x ∘ j.succAbove`. This is deletion of exactly
  coordinate j, in the stated order. Being a cochain complex includes delta²=0.
  `negative` imposes the zero extension at EVERY negative integer.
- `L : B ⟶ B` is an E-linear cochain endomorphism, and `L_formula` is exactly
  `Σ_s F(a_s(x_0),...,a_s(x_n))`. Its codomain ensures joint continuity and
  equivariance by `range`; no continuity of the operator on a function-space
  topology is asserted.
- `prism : Homotopy L (Fintype.card S • 𝟙 B)` uses Mathlib's `Homotopy`
  (`Mathlib.Algebra.Homology.Homotopy`, structure and comm field read at lines
  140–150). Its `hom (n+1) n` is K_(n+1). Its comm equation is
  L_n = K_(n+1) delta + delta K_n + |S| id, equivalently exactly the node's
  delta K_n + K_(n+1) delta = L_n - |S| id. Natural scalar multiplication is
  the repeated identity sum and equals the action of the cardinal's image in E,
  including positive characteristic.
- `bottom` specifies K_0 (and negative-degree components) as zero. Its target
  B^(-1) is a zero object by `negative`.
- `K_formula` is the double sum over `s : S` and `i : Fin (n+1)` with scalar
  `(-1:E)^i.val`. The tuple is
  `Fin.insertNth i.succ (a s (x i)) (fun j ↦ if j ≤ i then x j else a s (x j))`.
  `insertNth` at the successor of i keeps x_0,...,x_i, inserts a_s(x_i), and
  shifts the transformed suffix a_s(x_(i+1)),...,a_s(x_n) right by one place.
  This is the node's K in degree n+1, with n≥0, and hence covers every positive
  degree. Its source and target are linear ModuleCat objects; range again
  guarantees continuity and equivariance of the output.
- `degree_zero` explicitly states K_1 delta F evaluated at x equals
  `Σ_s (F(a_s x) - F(x))`. It includes the node's endpoint orientation.
- A coefficient map `b : A ⟶ W` in `TopRep` is exactly a continuous equivariant
  E-linear map. The existence conclusion supplies the uniquely pinned
  `bStar : (D A hA).B ⟶ (D W hW).B`; the first conjunct says evaluation of
  bStar is postcomposition with b. Thus this is the canonical b_* of the node,
  not an arbitrary unspecified morphism. The second conjunct is
  L_A ≫ bStar = bStar ≫ L_W; the final conjunct is
  K_A(i,j) ≫ bStar_j = bStar_i ≫ K_W(i,j) for every integer i,j.
  These are exactly both simultaneous naturalities, with the SAME family a
  and the SAME choice D for all coefficients and coefficient maps.
- There are no completeness, local compactness, T2, discrete topology, or
  compact group binders. All statements use abstract vector spaces.

### Existing declarations and dependency imports

`def-weil-field` is a Mathlib node with match `Field`; no dependency repair is
needed. The module uses `TopRep`, `TopRep.Hom`, `ContRepresentation`, `C(G,G)`,
`ModuleCat`, `CochainComplex`, `Homotopy`, `IsZero`, `Equiv.Perm`, and
`Fin.insertNth`/`Fin.succAbove` from the imported Mathlib modules. I read the
full TopRep structure and its Hom interface in `Continuous/TopRep.lean`,
ContRepresentation and ContIntertwiningMap in `Continuous/Basic.lean`, and the
Homotopy structure in `Algebra/Homology/Homotopy.lean`.

The proof dependency `def-weil-pbc-free-module` is recorded on `Module.Free` in
`Mathlib.LinearAlgebra.FreeModule.Basic`; its docstring and class signature
were read, and its module is a plain proof import. The other proof dependency,
`lem-trf-coefficient-bar-prism-homotopy`, currently has neither a Lean record nor
a Mathlib match, so it has no module to import. It is explicitly named in the
proof docstring as the future proof input; it is not needed for the statement.
No proof-dependency node has been restated here.

The existing `JointContinuousCochainCoordinates` in
`Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates` was read
in full. It packages an additional inhomogeneous complex, coordinate iso, and
derived-category size assumption. The present specification is of the prism
operators themselves, not a second definition of the coordinate isomorphism or
of a separately existing named homogeneous space. The evaluation-image encoding
follows that accepted interface without requiring its unrelated extra data.

### Edge cases

For S empty the permutation is the unique empty permutation, both finite sums
are zero, and L is homotopic to 0 via zero K. For degree zero the prism tuple
is (x_0,a_s(x_0)), so delta F evaluates to F(a_s(x_0))-F(x_0), with the displayed
sign. For degree one, K_1 F is Σ_s F(x_0,a_s(x_0)); for degree two its two
summands are F(x_0,a_s x_0,a_s x_1)-F(x_0,x_1,a_s x_1), as required. Negative
degrees are zero. Zero coefficient spaces, the trivial group, repeated maps,
identity maps, nonfaithful actions, and non-Hausdorff topologies are all admitted.
For characteristic two the signs and cardinal scalar reduce in E, without
changing the formulas. No nonemptiness of S or inversion of its cardinal enters.

### Searches

The launcher msearch queries were run with group Q108 and the assigned item:

1. LeanFinder: `Equivariant finite family of continuous group self maps gives
   signed prism homotopy on homogeneous continuous cochains`. Eight hits,
   including the newer-index ContinuousCohomology.homogeneousCochains and
   MultiInd.complex, inhomogeneousCochains.d, and Homotopy.mkCoinductiveAux₃.
   None states this finite-family, explicitly signed, joint-continuous prism.
2. Loogle: `TopRep.homogeneousCochains`. Twelve hits including that definition,
   its differential lemmas, and ContinuousCohomology.cochainsMap. I read the
   pinned local Basic.lean: this complex uses iterated C(G,C(G,...)) and
   invariants. It is not the arbitrary-group jointly continuous tuple model
   without an exponential-law assumption, and does not give these operators.
3. Mathlib grep: `prism|homogeneousCochains`, subdirectory RepresentationTheory.
   Twenty-five hits, again ordinary homogeneous definitions and functoriality,
   with no finite-family prism theorem.
4. LeanSearch: `Prism homotopy on jointly continuous equivariant homogeneous
   group cochains natural in coefficients for a permuted finite family`.
   Eight hits: Cochain.ofHomotopy, topological homotopy casts, generic continuous
   and ordinary cohomology, and mapping-cone homotopies. No exact match.
5. Project rg: `homogeneousCochains|ContinuousCohomology|continuous.*[Cc]ochain|[Pp]rism`
   over lean/Sheaf and lean/WeilConjectures. Found the existing finite-index
   transfer statement and homogeneous coordinate interface, which were read.
   The transfer has additional compact/profinite hypotheses and a special
   coset family; it is not this theorem for arbitrary permuted families.
6. Exact item-id search in lean/WeilConjectures found no declaration. Searches
   `prism|finiteFamily|permut.*family` in both RepresentationTheory directories
   gave the specialized transfer. Searches of
   `equivariantContinuousPrism|EquivariantContinuousPrism` across Mathlib,
   lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json found no
   name collision. DAG searches of homogeneous/jointly continuous notions
   identified the coordinate and differential lemmas, not an existing
   finite-family prism declaration.

### Validation

The module compiled through the prescribed `scompile.py`, both under the
sandbox name and its final library module name (about two seconds each), with
no errors or warnings. The only theorem is left as `by sorry`, as required.
Every universe and variable is explicit (`set_option autoImplicit false`).

## Second reading by Q108

No second worker was started: the dispatcher brief forbids starting agents and
specifies the maintainer's independent review after this direct delivery.
The worker checked each hypothesis and clause against the node and the Stacks
019S calculation as described above; this is not claimed as an independent review.
