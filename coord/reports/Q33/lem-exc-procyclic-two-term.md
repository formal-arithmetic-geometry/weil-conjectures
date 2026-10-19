## Worker report

The module `Sheaf.RepresentationTheory.ProcyclicTwoTerm` states
`Rep.exists_procyclic_twoTerm_computation`, with proof `sorry`.
It expresses “computed by the two-term complex” as a functorial two-term complex and
natural isomorphisms from the recorded continuous cohomology functors to its homology
in every degree. This follows the source's final identification with the right derived
invariant functors, rather than replacing them by ordinary abstract-group cohomology.

The blueprint source was read on the project server at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term.md`.
Its statement and all three proof paragraphs agree with the DAG statement. The module's
docstring carries all nine expanded DAG proof steps, including the periodic partial sums,
the coinduced effacements, and the natural comparison and universal-property argument.
No statement correction or disputed statement is needed; the explicit statement in the sandbox matches the live node and source intent.

Hypothesis and clause correspondence:

- A prime number l is `(l : ℕ) [Fact l.Prime]`.
- The nonnegative integer s is `(s : ℕ)`, including zero.
- A finite ring A is `(A : Type u) [Ring A] [Finite A]`. Commutativity, nontriviality,
  and finiteness of M are not assumed.
- Being killed by l^s is `hA : (l ^ s : ℕ) • (1 : A) = 0`.
  In any unital ring this is equivalent to annihilation of every element, by multiplying
  the equality by that element; it therefore annihilates every A-module as well.
- The additive l-adic integers are the existing `PadicInt l`, written `ℤ_[l]`.
  `Multiplicative ℤ_[l]` changes additive notation to the multiplicative convention of
  `Rep`, preserving the group and topology. The usual p-adic topology is used without
  introducing an arbitrary topology. Mathlib's `PadicInt.toZModPow`, its kernel theorem,
  and its compatible lift construction describe the same inverse-limit topology.
- The generator τ = 1 is `Multiplicative.ofAdd (1 : ℤ_[l])`. In particular this is
  not `1 : Multiplicative ℤ_[l]`, which would mean additive zero.
- All discrete continuous A[G]-modules are the objects of
  `DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])`. This is exactly the recorded
  open-stabilizer category, with arbitrary module universe w and equivariant linear maps.
  There is no additional topology, faithfulness, continuity or finiteness hypothesis on M.
- The complex is `K`, a functor to `CochainComplex (ModuleCat.{w} A) ℕ`.
  `e₀ M` and `e₁ M` identify its degree-zero and degree-one terms with M.
  The first two conjuncts make those identifications natural in every coefficient map f.
- The third conjunct specifies the only potentially nonzero differential, in these
  coordinates: `e₁ M (d 0 1 x) = M.obj.ρ τ (e₀ M x) - e₀ M x`.
- The fourth conjunct, `∀ M n, 2 ≤ n → IsZero ((K.obj M).X n)`, makes every other term zero.
  The ℕ index leaves no negative terms. The complex structure already enforces zero
  differentials between nonadjacent degrees and square-zero.
- The last clause is, for every `q : ℕ`, a natural isomorphism
  `discreteContinuousCohomologyFunctor ... A q ≅ K ⋙ homologyFunctor ... q`.
  Thus it identifies the actual right derived invariant functors with this complex's
  cohomology, including kernel in degree zero, cokernel in degree one and zero above.
  Naturality is retained by using functor isomorphisms, rather than objectwise bijections.

There are no new definitions or nodes. The existential complex is specified up to its
natural coordinate isomorphisms by its two terms, differential and zero terms; it is not
an arbitrary map or a construction obtained by choosing unconstrained existence data.
No definition has postponed data or any proof obligation hidden as `sorry`.

Dependency declarations used:

- `def-weil-l-adic-numbers`: its Mathlib match is used through `PadicInt` in
  `Mathlib.NumberTheory.Padics.PadicIntegers`, publicly supplied by
  `Mathlib.NumberTheory.Padics.ProperSpace`. Read the Padic/PadicInt definitions and the
  reduction, kernel and lift signatures in `Mathlib.NumberTheory.Padics.RingHoms`.
- `def-exc-continuous-cohomology`: `Rep.discreteContinuousCohomologyFunctor` in
  `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`. Its full source and docstring
  were read locally and confirmed with `scompile.py --source`. This is the finite-ring,
  ordinary right-derived-invariants interface, whose comparison with continuous cochains
  is `Rep.continuousCochains_derived_invariants` in
  `Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants`.
- Its representation category is the existing `Rep.DiscreteContinuousRep` from
  `WeilConjectures.RepresentationTheory.DiscreteContinuousRep`, whose open-stabilizer
  definition was read in the side framework checkout.
- The complexes and homology use Mathlib's `CochainComplex` and
  `HomologicalComplex.homologyFunctor`; no private replacement is introduced.
- `Mathlib.NumberTheory.Padics.ProperSpace` and
  `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` supply the existing compactness
  and disconnectedness instances needed by continuous cohomology. They are inferred,
  not added as mathematical hypotheses.

Every recorded proof-dependency module is imported directly: discrete modules abelian,
coinduced embedding, open normal stabilizer, effaceable universality, continuous cochain
 delta-functor, coinduced acyclicity, continuous-cochain short exactness, delta-functor,
ordinary derived category, and the homology long exact sequence and its naturality.
These are proof-only imports; the coefficient category, PadicInt, and continuous
cohomology dependency are public imports. No outside source was changed.

Edge cases checked:

- s = 0 implies 1 = 0 in A, so A and each unital A-module are zero; the statement
  correctly includes this case without assuming a nonzero ring.
- The zero module and the zero ring give a zero complex and zero cohomology in all degrees.
- Trivial action makes d = 0, giving M in degrees zero and one and zero above, as expected
  for l-primary discrete coefficients of Z_l.
- Nontrivial action is retained through the actual representation evaluated at the
  additive generator. The group identity is not mistaken for that generator.
- q = 0 and q = 1 are included explicitly through e₀, e₁ and the comparison for all q;
  n = 2 starts the zero terms. No positive-degree condition hides degree zero.
- M can be infinite and can live in any universe w; A has independent universe u, while
  PadicInt is the genuine Mathlib type in universe zero. No universe equation is imposed.

Searches for an existing statement (2026-10-16):

- `msearch.py leanfinder`, query “Continuous cohomology of the additive l-adic integers
  with discrete l-primary torsion coefficients is computed by the two-term complex M
  to M with differential generator minus identity”: eight hits, including continuous
  cochain infrastructure and `Rep.FiniteCyclicGroup.moduleCatCochainComplex`.
  None states this result. The finite-cyclic complex has alternating norm and generator
  differentials and a finite abstract group, rather than continuous Z_l-cohomology.
- `msearch.py loogle`, query `"continuousCohomology"`: twelve hits on Mathlib's
  homogeneous cohomology, cocycles and functoriality. Read its Basic source/docstring;
  these give the general complex, not the procyclic computation.
- `msearch.py grep`, query
  `procyclic|PadicInt.*[Cc]ohomology|[Cc]ohomology.*PadicInt`, in RepresentationTheory:
  zero hits.
- `msearch.py leansearch`, query “Continuous cohomology of Z_p with discrete p-primary
  torsion coefficients computed by the two term complex generator minus identity”:
  unavailable, Internal Server Error. This is not evidence of absence.
- Direct `rg` of the same procyclic/PadicInt-cohomology expressions and the node id in
  `WeilConjectures/` and `lean/Sheaf`: zero hits. Broader continuous-cohomology searches
  found the recorded dependency and its infrastructure, which were read and reused.
- Read the upstream naming/definition conventions and the CompactObject example and
  its node record. The chosen declaration name has no existing project or Mathlib match.

Validation: the required `scompile.py` compiled the module successfully, with no errors
or warnings. The theorem is the sole postponed declaration. The node copy changes only
`lean`, with its signature copied verbatim and UTC date recorded.


## Second reading by Q33

I read the source node, its corrected sandbox copy, and
`Sheaf.RepresentationTheory.ProcyclicTwoTerm.lean` item by item.

- The prime is rendered by `(l : ℕ) [Fact l.Prime]`; this matches the source's
  prime \(\ell\), with no characteristic or nonzero-ring assumption added.
- The exponent is `(s : ℕ)`, so `s = 0` is included. The finite coefficient ring is
  `(A : Type u) [Ring A] [Finite A]`, and `hA : (l ^ s : ℕ) • (1 : A) = 0`
  expresses that the ring is killed by \(\ell^s\), including the zero ring.
- The group is `Multiplicative ℤ_[l]`, using the existing `PadicInt l` and its
  usual topology; the generator is explicitly
  `Multiplicative.ofAdd (1 : ℤ_[l])`, so it is additive one rather than the
  multiplicative identity (additive zero).
- The coefficient objects are exactly
  `DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])`, hence discrete
  continuous A-linear representations with arbitrary module universe `w`.
- The computed complex is the functor `K` into
  `CochainComplex (ModuleCat.{w} A) ℕ`. The linear equivalences `e₀` and `e₁`
  identify its degree-zero and degree-one terms with the underlying module, and
  the first two conjuncts state their naturality for every equivariant map.
- The differential clause is
  `e₁ M (((K.obj M).d 0 1).hom x) =
  M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) (e₀ M x) - e₀ M x`, exactly
  \(\tau\cdot m-m\). The clause `2 ≤ n → IsZero ((K.obj M).X n)` makes all
  higher natural degrees zero; there are no negative degrees in the `ℕ` complex.
- For every `q`, the final clause gives a natural functor isomorphism (wrapped in
  `Nonempty`) from `discreteContinuousCohomologyFunctor` to the q-th homology of
  `K`, so it expresses the source's continuous-cohomology computation in all
  degrees and retains coefficient naturality.

The edge cases are covered: `s = 0`, the zero ring and zero module, trivial and
nontrivial actions, `q = 0`, `q = 1`, `n = 2`, and arbitrary module universe `w`.
No negative degree or characteristic restriction is introduced. The inverse-limit
and PadicInt searches were checked in Mathlib's Padics modules; the representation
and continuous-cohomology declarations were read in the shared Lean framework.
The `leanfinder`, `loogle`, and grep searches recorded in `searches.jsonl` found only
general continuous-cohomology or finite-cyclic infrastructure, not this procyclic
PadicInt computation; direct `rg` searches of the project and source returned no
duplicate declaration. `scompile.py` compiled the module cleanly.

The live node already contains the explicit prime, exponent, group topology,
generator, and dependency citations used by the Lean statement. I found no mismatch
between that node, its source place, and the module, and no statement correction is
needed. The sole citer `lem-exc-dvr-galois` still holds because it applies the formula
to `Z_l(1)` after choosing a generator.

