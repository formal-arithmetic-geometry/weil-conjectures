## What changed

Filled both proofs in `lean/Sheaf/AlgebraicGeometry/FpqcMorphismsDescend.lean`.
All existing statements, definitions, universes, docstrings, and imports are unchanged.
Added the proved private helper `effectiveEpi_of_fpqc_singleton`, which derives an
`EffectiveEpi` from fpqc subcanonicity via the existing Mathlib sheaf API.

`baseChangeMap_compatible` is proved by repeated pullback extensionality and the
projection identities of `pullbackLeftPullbackSndIso`.

`fpqc_morphisms_descend` follows all five steps of the existing node plan.
Base change stability gives the fpqc cover `pullback.fst pU f`. The private helper
makes it an effective epimorphism. For arbitrary maps `g₁,g₂` into `U ×ₛ X` with
equal `U` components, their `X` components define a map into `X ×ₛ X`; the
resulting map into the first iterated pullback becomes `g₂` under the canonical
comparison isomorphism. Precomposing the datum equation with this map and
projecting to `W` proves the compatibility needed by `EffectiveEpi.desc`.
Its factorization identity and epimorphism cancellation prove that the descended
map is over `S`. Pullback extensionality reconstructs `β`; cancellation proves
injectivity. This realizes the existing overlap argument through arbitrary
scheme-valued test maps, without needing a separately named overlap isomorphism.

The sources were checked at [Stacks 02W0](https://stacks.math.columbia.edu/tag/02W0),
[0241](https://stacks.math.columbia.edu/tag/0241),
[023Q](https://stacks.math.columbia.edu/tag/023Q), and
[022D(3)](https://stacks.math.columbia.edu/tag/022D).
The literature text is absent from this clone; the online primary sources were read.
The Lean proof retains the DAG route and its existing proof dependencies, so no
node changes or new nodes are needed. The unit record `sk-prop-h2` has no realized
statement or step nodes to bypass.

Searches: Lean Finder for compatible morphisms descending along effective
 epimorphisms found `EffectiveEpi.desc`, `.fac`, and `.uniq`; Loogle confirmed
`Sieve.effectiveEpimorphic_singleton`; grep located the pullback-pasting projection
identities. The existing two Mathlib leaf nodes already provide the substantive
base-change and representable-descent inputs. No Sheaf or WeilConjectures import
is needed beyond the existing Mathlib imports.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.baseChangeMap_compatible` and
`AlgebraicGeometry.Scheme.fpqc_morphisms_descend`, both attached to
`lem-galois-fpqc-morphisms-descend`. Also proved the private helper
`AlgebraicGeometry.Scheme.effectiveEpi_of_fpqc_singleton`.

No `sorry` remains, and none is split off. Local compilation is clean.
Explicit `#print axioms` checks for both public theorems show only
`propext`, `Classical.choice`, and `Quot.sound`.
No additional hypotheses, including quasi-compactness of the singleton morphism,
were introduced: the given fpqc covering membership is used directly.

## No longer needed

None. Both public imports are needed by the statements and definitions.
All three existing proof dependencies remain used:
`lem-galois-fpqc-covering-base-change`, `def-pc-fibre-product`, and
`lem-weil-pbc-fpqc-representable-descent`. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The representable descent leaf's recorded
Mathlib match suffices for general fpqc singleton covering membership; one need
not impose the stronger hypothesis `QuasiCompact f` used by Mathlib's convenient
flat-surjective effective-epi instance. No changes to the contract were needed.


## Second reading by U2

1. Interface: PASS. Read the whole delivered module and its diff against the
repository. The only existing declaration changes replace the two `sorry` proofs.
Both theorem signatures, both noncomputable definitions, universes, variables,
docstrings, and imports are byte-for-byte unchanged. The new helper is private;
there is no statement change or change record.

2. Proof and axioms: PASS. Independently compiled the delivered module locally
with lcompile.py: clean, no warnings. Read both proofs, including the construction
of `t` and `l`, the two projections proving `hl`, and projection of `hc` to `W`.
These give compatibility for all pairs of test maps with equal composites to the
cover, exactly the hypothesis of `EffectiveEpi.desc`. Its factorization identity
and epi cancellation establish the map over `S`, reconstruct the original `β`,
and prove injectivity. No `sorry`, forbidden declaration, or hollow definition
occurs. A scratch copy checks axioms of both definitions, both public theorems,
and the private helper; only the three permitted axioms occur.

3. Split-off statements: PASS, none. The private helper is proved from fpqc
subcanonicity and the singleton effective-epimorphism/sheaf equivalence, rather
than assuming descent. Its hypothesis is covering membership, so it does not
silently impose quasi-compactness. Identity covers, empty schemes where covering
membership holds, and arbitrary non-separated target schemes require no extra
hypothesis in either the helper or the argument.

4. Shortest route and pruning: PASS. Independently searched Loogle for
`CategoryTheory.EffectiveEpi.desc` and Mathlib by the expressions
`fpqc.*[Dd]escent|[Dd]escent.*fpqc|effectiveEpi.*singleton`, and searched lean/.
Read the upstream `Over.DescentDatum.existsUnique_hom_of_isPullback`: it requires
quasi-compactness and transport data, so applying it would add requirements and
translations. The chosen direct Mathlib route is appropriate. Both public imports
supply statement/definition API; no proof-only public import was added. All three
old proof dependencies are genuinely used, so `No longer needed: None` is complete.
Read dag/units/sk-prop-h2.json: its realized statement and step lists are empty;
no realized unit node is bypassed. Read the cited primary sources
[02W0](https://stacks.math.columbia.edu/tag/02W0) and
[023Q](https://stacks.math.columbia.edu/tag/023Q): their full-faithfulness and
representable-descent assertions agree with this route.

5. DAG agreement: PASS. Read lem-galois-fpqc-morphisms-descend and its base-change
and representable-descent leaf nodes. The five existing steps are realized by
base-change stability, the test-map form of the double-overlap universal property,
representable descent, cancellation to prove the map is over `S`, and pullback
reconstruction plus uniqueness. The recorded proof, proof_deps, and document
proof_origin still describe the actual argument; no node edit or new node is
needed.

Changes by the second reader: appended this review and expanded the scratch axiom
check to every declaration. No Lean proof, interface, import, or DAG repair was
necessary.
