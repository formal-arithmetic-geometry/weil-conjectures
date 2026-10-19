## Worker report

This repairs the returned stage-2 packet at immutable head eb1d762f2abd. The module
`Sheaf.RingTheory.QuasiFiniteComposition` states
`RingHom.finiteType_and_isQuasiFiniteAtPrime_comp`, with `sorry` as its sole proof.
No definition, new node, dependency repair, or statement correction is needed.
The source read is Stacks Project, Algebra, Tag 00PO
(`lemma-quasi-finite-composition`), algebra.tex lines 30342-30360, together with
Tags 00PK and 00PL for the isolated-fibre meaning of quasi-finiteness.

Hypotheses and conclusion, clause by clause:

- Arbitrary commutative rings A, B, C are `{A : Type u} {B : Type v} {C : Type w}`
  with `[CommRing A] [CommRing B] [CommRing C]`. The universes are independent and
  explicitly declared; `set_option autoImplicit false` checks variable binding.
- The given homomorphisms are `(f : A →+* B) (g : B →+* C)`.
  No algebra structure independent of these maps is assumed.
- Finite type of both maps is `(hf : f.FiniteType) (hg : g.FiniteType)`.
  These are the dependency's recorded `RingHom.FiniteType` predicate. Definitionally
  they are the `Algebra.FiniteType` witnesses for `f.toAlgebra` and `g.toAlgebra`.
- Quasi-finiteness at every prime of B is
  `(hfq : ∀ q : PrimeSpectrum B,
  @Algebra.IsQuasiFiniteAtPrime A B _ _ f.toAlgebra hf q)`.
  Every prime of B is included, with no condition on its contraction.
- Quasi-finiteness at every prime of C for g is the analogous `hgq`, with base B,
  target C, algebra `g.toAlgebra`, and finite-type witness `hg`.
- The composite is exactly `g.comp f`. The conclusion
  `∃ hgf : (g.comp f).FiniteType, ∀ r : PrimeSpectrum C,
  @Algebra.IsQuasiFiniteAtPrime A C _ _ (g.comp f).toAlgebra hgf r`
  asserts finite type and the isolated-fibre property at every prime of C.
  The existential proof witness lets the recorded quasi-finite predicate use
  finite type only after it has been concluded. It adds no hypothesis or data:
  `hgf` is a proof of a proposition. This is the dependent form of the two stated
  conclusions. There is no `let`, hidden map, or assumed composite finite type.

Dependencies read and used:

- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType` (definition at line 217); its full signature and docstring
  were read, as were `Algebra.FiniteType` and the finite-generator formulation.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`:
  `WeilConjectures.RingTheory.QuasiFiniteAtPrime`,
  `Algebra.IsQuasiFiniteAtPrime`. The old source checkout lacks this module;
  `scompile.py --source WeilConjectures.RingTheory.QuasiFiniteAtPrime` supplied
  the published source and full docstring. It defines the open singleton of the
  canonical fibre prime using `PrimeSpectrum.preimageHomeomorphFiber`. The fibre
  ring is `κ(p) ⊗[R] S`, canonically the factor swap of the node's ring. Its
  finite-type parameter is passed explicitly in every use.
- Proof dependencies are imported without `public`: `Mathlib.AlgebraicGeometry.Scheme`
  for `AlgebraicGeometry.Spec` (`def-weil-affine-spectrum`),
  `Mathlib.RingTheory.Localization.AtPrime.Basic` for `Localization.AtPrime`
  (`def-weil-pbc-localization-at-prime`), and
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` for `Ideal.Fiber`,
  `Ideal.ResidueField`, and `PrimeSpectrum.preimageOrderIsoFiber`
  (`lem-weil-pbc-fibre-ring-primes-bijection`). Their signatures and docstrings
  were read. The latter bijection is a Mathlib match and needs no new record.
  Finite type and quasi-finite-at-prime proof dependencies are already public
  statement imports. The declaration docstring carries all three DAG proof steps,
  including the finite generators, clearing the fibre denominator, and the
  product witness `g(b) * c`.

Edge cases checked before writing: zero rings are permitted; if C is zero there
are no target primes, but finite type is still concluded. If B is zero, a unital
map to C forces C to be zero, so there is no missed prime case. Identity maps and
finite field extensions have isolated fibre primes. Empty fibres do not impose
conditions, while all primes of a nonempty fibre remain quantified. Empty finite
lists of algebra generators and nilpotents require no extra assumptions. No
Noetherian, domain, reduced, nonzero, injectivity, or characteristic assumption
has been introduced. No statement dispute or source error was found.

Searches actually run through `msearch.py` in this repair:

- LeanFinder: `composition of finite type ring maps quasi-finite at every prime is
  quasi-finite at every prime` returned eight hits, including
  `RingHom.QuasiFinite.comp`, `.stableUnderComposition`, `Algebra.QuasiFinite.trans`,
  and essential-finite-type composition results.
- Loogle: `RingHom.QuasiFinite.comp, Algebra.IsQuasiFiniteAtPrime` returned zero
  hits and explicitly reported the project identifier unknown. This is not used
  as evidence of absence from the project.
- Loogle: `RingHom.QuasiFinite.comp, RingHom.FiniteType.comp` returned zero hits.
- Mathlib grep, subdirectory `RingTheory`, query
  `QuasiFinite.*comp|isQuasiFiniteAtPrime.*comp|IsQuasiFiniteAtPrime` returned four
  lines in `RingTheory/RingHom/QuasiFinite.lean`: comp, of_comp, comp_iff, and
  stableUnderComposition.
- LeanSearch: `finite type ring maps with isolated points in every residue field
  fibre are stable under composition` returned eight hits, including
  `RingHom.QuasiFinite.stableUnderComposition`,
  `RingHom.finiteType_stableUnderComposition`, and the scheme composition instance.

I read `RingHom.QuasiFinite.comp` and its predicate in Mathlib. It composes
`Algebra.QuasiFinite`, which is fibrewise module-finiteness and does not require
finite type. It is not this node's statement using the recorded isolated-fibre
predicate. The equivalence requires the fibre-topology bridge, not just
specialization. Finite-type composition alone covers only the first conclusion.
The source-tree searches by item id and by `IsQuasiFiniteAtPrime`,
`isQuasiFiniteAtPrime`, and composition patterns found no existing exact theorem
in the reference project source. Searches of `lean/Sheaf` and
`dag/lean_names_upstream.json` found the definition and related permanence,
localization, finite-map and four-ring lemmas, not this composition statement.
In particular `QuasiFiniteAtPrimePermanence` was opened: it restricts scalars from
an already quasi-finite composite and does not state composition. No second
notion is defined here. Search results remain in the sandbox's `searches.jsonl`;
the item's historical `mathlib_searches` is preserved unchanged.

## Repairs to the returned delivery

1. Missing artifact and record: added the actual Lean module and complete `lean`
   record, including the exact verbatim signature, declaration, file, module,
   branch `newtargets-dag`, group N6, UTC date, and `existing: false`.
2. Missing clean compile evidence: ran the required `scompile.py N6
   lem-trf-quasi-finite-composition` on the delivered file. Both wrapper checks
   passed: sandbox 2.0 s and library module 2.9 s, with no errors or warnings.
   The theorem's only proof is the required stage-2 `sorry`.
3. Report format: replaced the stage-1 report with this exact `## Worker report`
   section, hypothesis/clause correspondence, sources, dependencies, edge cases,
   actual searches, and repair evidence. Per the direct-delivery instruction,
   no independent second reading is claimed by the author; the delivery wrapper
   inserts the standard section recording the maintainer-review arrangement.
4. Unauthorized item-node field: restored every non-`lean` field from the current
   shared node. In particular, the returned head's appended `mathlib_searches`
   entries are absent. A parsed JSON comparison reports exactly `['lean']` as
   the changed keys. The statement, dependencies, proof, and review metadata
   remain exactly those of the current base. The wrapper builds on freshly
   fetched `newtargets-dag`, so the old split commit is not reused as the base.

The author re-read the signature against every clause above and found no
mismatch. All Lean lines are at most 100 characters. The required delivery dry
run passed on commit c307fc788d: server preflight and compilation both accepted
the three-file packet. The final dry run is repeated after this report update.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
