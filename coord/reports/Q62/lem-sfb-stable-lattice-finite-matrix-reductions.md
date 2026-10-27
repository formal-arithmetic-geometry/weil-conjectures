## Worker report

The module `Sheaf.RepresentationTheory.StableLatticeFiniteMatrixReductions` states
`Padic.exists_stable_lattice_finite_matrix_reductions`. Its sole theorem has proof `sorry`.
No definition, dependency repair, new node, or statement correction was needed. The node
copy changes only `lean`. The source was read directly with `pdftotext`: Stanford Weil II
seminar lecture 19, Proposition 1.1.9, printed p. 3, second and third bullets. The node
expands the stable lattice and its finite lattice quotients into matrix coordinates.

Hypotheses and objects correspond as follows:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded spectral norm is installed
  by `letI := spectralNorm.nontriviallyNormedField ℚ_[l] E`.
- The integers, chosen uniformizer, and quotient rings are exactly the imported
  `coefficientExtensionIntegers l E`, `coefficientExtensionUniformizer l E`, and
  `coefficientExtensionRing l E n`. The latter is definitionally the quotient by
  `coefficientExtensionIdeal l E n = (Ideal.span {π}) ^ n`. The identity
  `Ideal.span_singleton_pow` identifies this ideal with `(π^n)`.
- The compact topological group has the explicit `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, and `CompactSpace` binders on `G : Type v`.
- The finite-dimensional vector space has `AddCommGroup`, `Module E`, and
  `FiniteDimensional E` binders on `V : Type w`. Its topology is `moduleTopology E V`.
  In finite dimension this is precisely its norm topology: the recorded
  `LinearEquiv.toContinuousLinearEquiv` identifies coordinates over the complete
  nontrivially normed spectral field with any given Hausdorff norm-topological model.
  Thus this presentation is the same finite-dimensional topology, as in the recorded
  stable-lattice dependency; it does not impose a choice of norm or restrict the spaces.
- The representation is `ρ : G →* (V ≃ₗ[E] V)`, with exactly the joint continuity
  hypothesis `Continuous (fun p : G × V ↦ ρ p.1 p.2)`.
- The rank `r` is written directly as `Module.finrank E V`; no positivity is assumed.
  Restriction of scalars to the recorded integer subring uses `Module.compHom V ...subtype`.

Each conclusion has its own rendering:

- The lattice is `Λ : Submodule (coefficientExtensionIntegers l E) V`. The witness
  `b : Module.Basis (Fin (Module.finrank E V)) ... Λ` asserts it is finite free of rank
  exactly `r`; a finite basis also gives finite generation. Fullness is the explicit
  equality `Submodule.span E (Λ : Set V) = ⊤`.
- Stability is equality of sets `∀ g, (ρ g) '' (Λ : Set V) = (Λ : Set V)`.
- The field basis is `e : Module.Basis (Fin (Module.finrank E V)) E V` and
  `∀ j, (b j : V) = e j` says these are the same vectors after inclusion of the lattice.
- `A : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank E V)) ...` is the integral
  homomorphism. Mathlib's GL is `(Matrix ... ...)ˣ`, so it records both matrix inverse
  identities exactly as requested. The coordinate identity is
  `ρ g (e j) = ∑ i, ((A g i j : coefficientExtensionIntegers l E) : E) • e i`.
  Row index `i` and column index `j` have the orientation of the node.
- The principal-ideal-adic lattice topology is explicitly equated to
  `TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance`.
  The restricted action is a witness `a : G × Λ → Λ` with `Continuous a` and the
  pointwise equation `(a p : V) = ρ p.1 (p.2 : V)`. Continuity here uses the inherited
  subspace topology; the preceding equality makes this also the required adic continuity.
- Every positive integer level is `∀ (n : ℕ), 1 ≤ n → ...`. The bound excludes zero
  levels, without restricting rank zero.
- The reduced homomorphism `Aₙ` is identified by equality with
  `(Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (... n))).comp A`.
  This is the canonical entrywise reduction, rather than an unspecified finite action.
- `Finite (coefficientExtensionRing l E n)` asserts finiteness of `R_n` and
  `Finite Aₙ.range` asserts finiteness of the exact subgroup `Q_n = A_n(G)`.
- `@Continuous G _ inferInstance ⊥ Aₙ` installs the discrete topology directly on the
  whole target group. Likewise `@Continuous G Aₙ.range inferInstance ⊥ Aₙ.rangeRestrict`
  asserts continuity of the canonical corestriction with discrete image. The final
  `Function.Surjective Aₙ.rangeRestrict` gives surjectivity; `rangeRestrict` is already
  a bundled group homomorphism. No arbitrary image group or map is substituted.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, with the publicly imported coefficient
  constructions in `Sheaf.NumberTheory.Padics.CoefficientExtension` listed above.
- `Mathlib.LinearAlgebra.Matrix.Defs`, `Matrix`, publicly exposed by
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`. Its `GeneralLinearGroup`
  and `GeneralLinearGroup.map` give the exact matrix-unit group and entrywise map.
- Proof imports: `Sheaf.RepresentationTheory.ProfiniteStableLattice`,
  `Padic.exists_stable_lattice`; `Mathlib.Topology.Algebra.Valued.LocallyCompact`,
  `Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`.
- Other proof dependencies are exposed through existing public imports:
  `spectralNorm.completeSpace` in `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`,
  `LinearEquiv.toContinuousLinearEquiv` in
  `Mathlib.Topology.Algebra.Module.FiniteDimension`, and
  `Padic.extension_integers_dvr` in `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
  Their source signatures and the full coefficient and stable-lattice docstrings were read.

Edge cases: rank zero uses `Fin 0`, with empty bases, a zero lattice and singleton matrix
unit groups and images. There is no `Nonempty` index or positive-rank assumption. The
coefficient ring finiteness still appears independently of rank. Positive levels include
`n = 1`. The prime `2`, trivial groups, and representations with kernel are included.
No faithfulness, profiniteness, Hausdorff assumption on `G`, or countability is added.
Universes `u v w` are explicit and independent. Every variable is bound explicitly.

Searches made with the prescribed `msearch.py` wrapper (recorded in `searches.jsonl`):

- LeanFinder: `A compact group representation on a finite dimensional p adic vector
  space has a stable lattice and continuous finite matrix reductions`. Eight hits,
  including compactness of p-adic integers and properness; no complete statement match.
- Loogle: `Matrix.GeneralLinearGroup.map, MonoidHom.rangeRestrict`. Zero hits to the
  combined query. Their exact declarations were subsequently read locally in the
  general-linear-group and subgroup-kernel modules and used.
- Mathlib grep: `stable_lattice|finite.*matrix.*reduc|continuous.*rangeRestrict`.
  Four hits, concerning unrelated normed operators or restricted continuous linear maps.
- LeanSearch: `A continuous compact group representation over a finite extension of
  p adic numbers admits an invariant lattice with continuous finite reductions`.
  Eight hits: representation invariants, open subgroup finite quotients, and p-adic
  compactness, with no theorem containing the node's combined conclusions.
- Project/source `rg -n` for
  `stable_lattice|stableLattice|finite_matrix_reductions|finiteMatrixReductions|lem-sfb-stable-lattice-finite-matrix-reductions`
  in `lean/WeilConjectures` and `lean/Sheaf` found the existing stable-lattice theorem,
  its core and topology lemmas, and uses in l-adic/Weil-sheaf modules. The private
  `matrix_stable_lattice` in `Sheaf.Paper.RealWeilSheaves` was read: it supplies only
  an integral basis, fullness and stability on `E^n`, with no finite reductions or
  lattice topology clauses, so is not an exact existing statement.
- The intended new declaration name was also searched in both source roots and
  `dag/lean_names_upstream.json`; no existing declaration was found.

Server validation: prescribed `scompile.py` compiled the module cleanly in both sandbox
and module-path modes (8.4 s and 2.8 s respectively). No warnings were emitted.
No statement dispute or node fault was found.

## Second reading by Q62

I reopened the node and completed module for a separate clause-by-clause self-check.
The independent maintainer review remains external to this worker, as required by the
remote dispatcher brief; this section does not claim a second worker participated.
The coefficient subring and uniformizer are the recorded ones, both bases have the same
index and underlying vectors, and the matrix formula uses the correct row/column order.
The principal-ideal adic topology, inherited topology and restricted action refer to the
same lattice. The finite-level map is fixed to the actual quotient-map reduction and its
range is the actual image, with both discrete topologies explicit. The quantifier on levels
is positive and there is no quantifier or typeclass excluding rank zero. The basis witness
already gives finite generation, freeness and the exact rank, so no clause was lost by
expressing these together. No mismatch requiring a change was found.
