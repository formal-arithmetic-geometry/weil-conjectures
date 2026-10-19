## Worker report

The module `Sheaf.TraceFormula.LocalUIFlatCokernel` states
`Module.flat_of_universally_exact` with proof `sorry`. It renders the M₃ clause of
Stacks Project, Algebra Tag 058P (`lemma-ui-flat-domain`): a universally exact
sequence of R-modules, represented by R-linear maps `f : M₁ →ₗ[R] M₂` and
`g : M₂ →ₗ[R] M₃`, has flat M₃ when M₂ is flat.

The ring hypothesis is `{R : Type u} [CommRing R]`. The three module objects are
independent universes `v`, `w`, and `z`, each with `AddCommGroup` and `Module R`
instances. The maps are `f` and `g`. For the arbitrary testing module, the
binder `∀ (N : Type (max u t)) [AddCommGroup N] [Module R N]` uses an arbitrary universe
containing the ring universe; its three clauses are rendered as
`Function.Injective (f.rTensor N)`,
`Function.Exact (f.rTensor N) (g.rTensor N)`, and
`Function.Surjective (g.rTensor N)`. The final hypothesis is the typeclass
binder `[Module.Flat R M₂]`, and the conclusion is `Module.Flat R M₃`.
The proof docstring records the three source proof steps: form the tensor exact
diagram and use middle flatness, prove M₁ flat by tensor-injectivity, and chase
the diagram for an arbitrary injection to prove M₃ flat.

The statement dependency is `def-weil-pbc-flat-ring-map`, recorded as
`Module.Flat` in `Mathlib.RingTheory.Flat.Basic` and `RingHom.Flat` in
`Mathlib.RingTheory.RingHom.Flat`; the module imports
`Mathlib.RingTheory.Flat.Basic`. No private flatness notion is introduced.

Edge cases checked include zero modules, the split short exact sequence, and the
non-flat torsion example `0 → ℤ --2→ ℤ → ℤ/2 → 0`, which is not universally exact
and therefore does not satisfy the hypothesis. The test universe contains the ring universe, preventing a vacuous hypothesis
for a ring too large to act on any nonzero small module. Smaller testing modules
can be transported by `ULift`; `N = 0` is included. The three tensor-map clauses
also retain the injective, exact, and surjective parts separately.

Searches made: `msearch.py ... leanfinder "universally exact sequence of module
linear maps flat middle module flat cokernel"` returned only general
`Module.Flat` exactness lemmas and no theorem for this cokernel criterion;
`msearch.py ... loogle "Module.Flat rTensor_exact Function.Exact LinearMap.rTensor"`
returned no matching theorem (the query itself had an application type mismatch);
`msearch.py ... grep "universally.exact|flat.*cokernel|cokernel.*flat"
Mathlib/RingTheory` returned no matching theorem. Repository `rg` searches found
only unrelated scheme, complex, and ideal-specific flat-cokernel results. The
DAG search for `lem-trf-local-ui-flat-cokernel`, Tag 058P, and “universally exact”
found no duplicate statement module. The recorded dependency declaration was
opened and checked against its full signature and docstring.

## Second reading by Q43

I reread the restored base node and the Lean file line by line. Its `R` is a
commutative ring; `f` and `g` have exactly the three independent module objects
specified by the node; and the universal quantifier over `N : Type (max u t)` carries
only the required additive-group and R-module structures. The first, middle, and
last clauses of universal exactness match the node's injectivity, exactness, and
surjectivity requirements through `LinearMap.rTensor`. The flatness assumption is
exactly `[Module.Flat R M₂]`, and the conclusion is exactly `Module.Flat R M₃`.
No hypothesis or clause was added, dropped, weakened, or strengthened. The node's
proof texts and blueprint attribution were restored to the accepted Q39 base,
including the full final diagram chase. The per-file `scompile.py` check is clean
with no errors or warnings.

Final rereading corrected the test-universe binder from `Type t` to
`Type (max u t)`, as required by brief-stage2 §2: without this, all small test
modules can be zero for a sufficiently large field, making the hypothesis
vacuous. This is a size convention, not a restriction on any of the three modules
in the sequence. The docstring now gives the full restored three-step chase,
including middle-row exactness, bottom-row injectivity, left-column exactness,
and middle-column injectivity, rather than the incorrect last inference in the
returned stage-1 head. The source Tag 058P and Mathlib flatness definitions were
opened and read directly. No natural-language node fields changed.

A corrected Loogle query, `Module.Flat, Function.Exact, LinearMap.rTensor`,
returned `Module.Flat.rTensor_exact`, `Module.Flat.iff_rTensor_exact`, and
`Module.Flat.iff_rTensor_exact′`; these characterize tensoring by one flat
module, rather than flatness of the last term of a universally exact sequence.
A LeanSearch query, “universally exact sequence of modules with flat middle term
has flat last term”, was also run; its results are recorded by `msearch.py` in
`searches.jsonl`. Exact-name searches in the upstream name index, Mathlib,
upstream sources, and side-project sources found no existing declaration named
`Module.flat_of_universally_exact`. Final wrapper compilation after the universe
and docstring corrections succeeded: sandbox 3.8 s and library file 2.6 s,
with no diagnostics.
