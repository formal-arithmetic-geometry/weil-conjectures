## Worker report

The module `Sheaf.Algebra.Homology.FreeComplexResidueDegreeCancellation` states
`CochainComplex.exists_localized_homotopyEquiv_zero_degree`. No definitions or
proofs are added. The single theorem has `sorry` as its whole proof. The node is
unchanged outside its `lean` record.

Hypothesis and clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`; the prime is
  `(p : Ideal R) [p.IsPrime]`, and the degree is `(i : ℤ)`.
- The cochain complex is `(P : CochainComplex (ModuleCat.{max u v} R) ℤ)`.
  Both universes are explicit and independent. Original and localized terms live
  in `ModuleCat.{max u v}`, so the module universe contains the ring universe,
  as required by Mathlib's scalar-extension additive instance. The arbitrary v
  permits any module size; smaller presentations can be universe lifted.
- Each term has a finite basis: `hfree : ∀ j, Module.Free R (P.X j)` together
  with `hfinite : ∀ j, Module.Finite R (P.X j)`. A finitely generated free module
  has a finite basis; conversely a finite basis gives both predicates.
- The specified residue field is literally `FractionRing (R ⧸ p)`, with its
  canonical R-action given by the composite of `Ideal.Quotient.mk p` and
  `algebraMap (R ⧸ p) (FractionRing (R ⧸ p))`. Since p is prime, the quotient
  is a domain, so the fraction ring is the field of fractions described by the
  node. This does not replace it with an arbitrary field or coefficient map.
- Ordinary termwise tensor extension is `ModuleCat.extendScalars` followed by
  `mapHomologicalComplex (ComplexShape.up ℤ)`. This uses S tensor P instead of
  P tensor S, canonically identified by tensor commutativity over R; the maps
  are the same scalar-extended differentials under that identification.
- Vanishing of the specified cohomology is `hresidue : IsZero (...homology i)`.
- The principal open is `∃ f : R, f ∉ p`; its ring is `Localization.Away f`.
- The existential Q is an integer cochain complex over that ring. Its two
  quantified Free and Finite conditions say every term is finite free.
- `Nonempty (HomotopyEquiv ... Q)` gives chain maps in both directions and
  homotopies from both composites to the identities. Mathlib's Homotopy has
  degree -1 for cochain complexes, with the differential-homotopy equation
  requested by the node.
- `IsZero (Q.X i)` says the middle term is zero as a module, allowing any
  presentation of the zero module, including the zero module with empty basis.
- Away from `{i-1,i,i+1}`, the equality of ModuleCat objects says the terms
  agree literally with the original scalar extensions. The subsequent `HEq`
  compares their differentials between any two such degrees; with those object
  equalities it is exactly equality after transport of the source and target.
  It includes the shape-forced zero differentials as well as adjacent ones.
- For either adjacent degree, the maps a into the original localized term and
  b back satisfy `a ≫ b = 𝟙 (Q.X j)`. Thus Q's term is a direct summand of
  the corresponding original term. It is finite free by the earlier clauses;
  the split-monomorphism formulation is equivalent to a submodule summand.
- Finally `∀ j, IsZero (P.X j) → IsZero (Q.X j)` states preservation of every
  zero degree, including adjacent degrees.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`: the node includes the cochain-complex and cohomology
  infrastructure, used here through `CochainComplex` and
  `HomologicalComplex.homology`. No derived category object is necessary for
  this chain-level assertion. Its recorded module is imported.
- `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`: used for both P and Q;
  `Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs` expresses finiteness.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`: used by
  `ModuleCat.extendScalars` in `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`.
  The functor's object and map definitions were read: they are S tensor M and
  the scalar extension of the linear map.
- `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`: the
  powers localization, with its ring and algebra structure supplied by
  `Mathlib.RingTheory.Localization.Away.Basic`.
- Further existing infrastructure: `FractionRing` in
  `Mathlib.RingTheory.Localization.FractionRing`, `HomotopyEquiv` in
  `Mathlib.Algebra.Homology.Homotopy`, and ModuleCat's abelian structure.

Source and edge-case checks: Read the full direct matrix proof of Stacks Tag
068U in `literature/stacks-project/more-algebra.tex`, lemma-cut-complex-in-two.
Its bounded-above reduction is needed for the larger pseudo-coherent derived
splitting, not for these three-degree matrix operations. The node supplies the
rank-one induction and both homotopies explicitly, and the declaration docstring
records all six proof steps. The zero complex and empty middle basis admit f=1
and the identity equivalence; no nonzero-rank assumption is added. A zero ring
has no prime ideal, so no extra nontriviality hypothesis is needed. Negative i,
unbounded complexes, arbitrarily large term universes, nonreduced rings and
all characteristics are allowed. If either adjacent original term is zero,
the direct-summand and zero-preservation conditions force that term of Q to
remain zero. The finite-basis assumption is per term and does not impose a
uniform rank bound. No statement fault or disputed clause was found.

Searches (2026-10-15):

- `msearch.py ... leansearch`: "Cancel an exact residue field degree of a finite
  free cochain complex after localization". Service unavailable, Internal
  Server Error; not treated as a negative search result.
- `msearch.py ... leanfinder`: "A finite free cochain complex with vanishing
  residue field cohomology admits a homotopy equivalent complex with that degree
  zero after principal localization". Eight hits concerning K-projectivity and
  homotopy orthogonality; none states this cancellation result.
- `msearch.py ... loogle`: `"HomotopyEquiv", "ModuleCat"`. Two hits:
  `Rep.standardComplex.forget₂ToModuleCatHomotopyEquiv` and its degree-zero
  formula. These concern a particular representation resolution, not this lemma.
- `msearch.py ... grep`: `residue.*(complex|homotopy)|complex.*residue|cut.*complex`.
  Eight hits in complex numbers, ExactSequence, and smoothness/cotangent files;
  none gives the statement.
- Local `rg` with the same residue/complex pattern and the exact item id across
  upstream WeilConjectures and project Sheaf found several related geometric
  or bounded residue-complex results but no identical declaration. Opened
  `FiniteFreeResidueLocalHomotopy.lean` and `FiniteFreeStalkUnitCancellation.lean`:
  they concern scheme sheaves with support bounds, so are not this ring-level,
  unbounded, arbitrary-degree assertion. The exact item id has no upstream match.
- Local `rg` of `dag/lean_names_upstream.json`, upstream WeilConjectures and
  project Sheaf found no occurrence of the chosen declaration name. Local
  Mathlib searches located and the source reads checked extendScalars,
  HomotopyEquiv, FractionRing, Localization.Away, Module.Free, and Module.Finite.

Validation: server-only compilation via scompile.py, nice 19, two threads,
60 seconds per file. Delivery dry run via deliver2.py --no-push; no delivery
is pushed by this worker. The second reader supplies the independent reading.

## Second reading by NJ

Independently read the node, its six proof steps, this module, the four dependency
node records, and their actual Mathlib declarations. Read Stacks
`more-algebra.tex`, lemma-cut-complex-in-two (Tag 068U), including its complete
direct matrix proof. Its initial bounded-above replacement concerns the larger
pseudo-coherent derived assertion; the matrix cancellation itself involves only
three degrees and requires no support bound. The node explicitly extracts that
chain-level assertion. No source-wide Noetherian, local-ring, characteristic,
or field hypothesis is missing. No statement correction is needed.

Object/hypothesis/conclusion checklist, in node order:

1. Commutative ring R: `{R : Type u} [CommRing R]`. Exact.
2. Prime ideal p: `(p : Ideal R) [p.IsPrime]`. Exact; no maximality assumption.
3. Residue field Frac(R/p): `FractionRing (R ⧸ p)` with coefficient map
   `(algebraMap (R ⧸ p) (FractionRing (R ⧸ p))).comp (Ideal.Quotient.mk p)`.
   Exact: the prime quotient is a domain, so its non-zero-divisors are exactly
   its nonzero elements. This is the specified fraction field and canonical map.
4. Integer degree and cochain complex: `(i : ℤ)` and
   `(P : CochainComplex (ModuleCat.{max u v} R) ℤ)`. Exact differential direction.
   Both universes are bound. The arbitrary module universe is enlarged to contain
   the ring universe for scalar extension; smaller carriers have universe-lifted
   presentations. No restriction on the sizes of finite bases is imposed.
5. Each term has a finite basis: `hfree` and `hfinite`, each universally quantified
   over integer degrees. Exact: over the nontrivial ring supplied by a prime,
   a finite generating family bounds the cardinality of a basis. No boundedness
   or uniform rank bound is assumed.
6. Ordinary termwise tensor with the residue field: `extendScalars` mapped to
   homological complexes of shape `up ℤ`. Its definitions send M to S tensor M
   and a map to `s tensor m ↦ s tensor f(m)`. Tensor symmetry canonically identifies
   this with the node's M tensor S, including the differentials. Exact.
7. Vanishing H^i: `hresidue : IsZero (...homology i)`. Exact categorical zero
   object in the abelian category of modules, not `IsZero` on a bare carrier type.
8. Principal localization: `∃ f : R, f ∉ p ∧ ...`, ring `Localization.Away f`
   and its canonical `algebraMap`. Exact powers localization R[1/f].
9. Finite-free replacement complex: existential Q over that same localization,
   followed by `∀ j, Module.Free ...` and `∀ j, Module.Finite ...`. Exact.
10. Chain homotopy equivalence: `Nonempty (HomotopyEquiv ... Q)`. Exact: inspected
    the structure's two chain maps and both homotopies. `Homotopy.hom` is supported
    where `c.Rel j i`; for `up ℤ` it lowers degree by one, and `comm` is the dh+hd
    equation. Choosing the opposite sign gives either convention for the difference.
11. Q^i=0: `IsZero (Q.X i)`. Exact zero module, independent of its presentation.
12. Unchanged terms outside {i-1,i,i+1}: the first universal concluding clause
    gives literal equality of ModuleCat objects with their scalar extensions.
    Exact, and satisfiable by retaining those original objects in the construction.
13. Unchanged differentials between those terms: the next clause quantifies both
    j and k outside the set and gives `HEq (Q.d j k) (...map (P.d j k))`.
    With the preceding object equalities this is equality after transport of both
    endpoints. It imposes no condition on arrows incident to a changed degree.
    Nonadjacent, shape-forced zero differentials add no additional restriction.
14. Adjacent terms are finite free direct summands: for `j = i-1 ∨ j = i+1`,
    maps a from Q's term to the original localized term and b back satisfy
    `a ≫ b = 𝟙 (Q.X j)`. Exact split inclusion/retraction, with finite freeness
    already asserted. It does not incorrectly require the complementary summand
    of an arbitrary split inclusion to be free.
15. Every original zero term remains zero: `∀ j, IsZero (P.X j) → IsZero (Q.X j)`.
    Exact, including both adjacent degrees. The existential quantifier order
    chooses one f and one Q satisfying all clauses simultaneously.

Dependency signatures were opened, not inferred from names: `Module.Free`
(`exists_basis`), `Module.Finite` (`fg_top`), `TensorProduct` (bilinearity
quotient), `Localization.Away` (localization at powers), and the recorded
`DerivedCategory`/`HasDerivedCategory` in DerivedCategory.Basic. Only the
cochain/homology infrastructure of the latter node is needed here, so there is
no unnecessary derived-category existence instance. `extendScalars.obj'`,
`map'`, `Homotopy`, and `HomotopyEquiv` were also opened. All notions are existing
public infrastructure. There are no new definition nodes or dependency modules
in this delivery and no missing notion requiring one.

Edge cases: empty middle basis and the zero complex admit f=1 and identity
cancellation; empty adjacent bases remain zero by the final clause. At i=0,
negative degrees, and arbitrary integers, the three degrees remain distinct.
Unbounded complexes and independently varying finite ranks are covered. The
zero ring has no prime ideal, exactly as in the node. Nonreduced rings and every
characteristic are admitted. There is no scheme or index-set nonemptiness
hypothesis to check. Universes u and v and every binder are explicit.

Independent searches used different wording from the first report:

- `msearch.py ... leanfinder "A finite free complex can have a term removed up
  to chain homotopy after localizing where residue cohomology vanishes"`: eight
  hits on K-projective/injective null homotopies, CM5b, and maps from/to single
  complexes. None is local residue-degree cancellation.
- `msearch.py ... grep 'homotopy.*localiz|localiz.*homotopy|cancel.*complex'`:
  25 hits, principally group homology and model-category localization. No match.
- Local `rg -i 'pivot|cancel.*(degree|free complex)|residue.*homotopy'` across
  upstream WeilConjectures and project Sheaf found cancellation candidates.
  Opened `ChainComplex.exists_nat_homotopy_cancellation_of_isUnit_entry`,
  `ChainComplex.exists_splitting_of_isUnit_entry`,
  `CochainComplex.exists_finiteFree_cancel_split_top`, and the bounded-resolution
  cancellation module: these take supplied unit pivots or split top maps and
  have different index/support hypotheses and conclusions; none chooses a
  localization from residue exactness or eliminates the whole middle degree.
  Opened the signature of `exists_restrict_homotopyEquiv_single_of_residue`:
  it is a bounded nonnegative complex of scheme modules, also a different result.
- Searched the exact proposed name in the upstream declaration inventory and
  Mathlib: absent. The report's earlier LeanSearch service failure is recorded
  as unavailable, not as evidence of absence.

No mismatch found; no Lean or node changes were needed. The header, source and
blueprint docstrings, six-step proof account, public names, line widths, imports,
and absence of private definitions/local notation were checked. The sole proof
is exactly `by sorry`, and there are no hollow definitions. Extracting the
signature from `theorem` to `:=` matches `lean.statement` verbatim.

Validation: scompile.py compiled the sole delivered file successfully on the
server in 1.3 seconds, nice 19, two threads, 60-second limit, with no diagnostic.
