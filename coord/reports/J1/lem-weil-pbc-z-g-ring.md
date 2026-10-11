## Worker report

The module `Sheaf.RingTheory.IntGRing` states `Int.isGRing : IsGRing ℤ` with a
`sorry` proof. It defines no new notion. The source is Stacks Project, More on
Algebra, Proposition 07PX, item (3), checked at
https://stacks.math.columbia.edu/tag/07PX (the local literature file is absent).

Hypothesis and clause correspondence: the node has no hypotheses. Its object
“the ring Z” is Mathlib's `ℤ` with its canonical commutative-ring instance. Its
sole conclusion “is a G-ring” is exactly `IsGRing ℤ`. There are no extra binders,
Noetherian assumptions, or additional clauses. No universe or prime is restricted.
The theorem docstring gives all four proof steps recorded in the node.

Dependency used: `def-weil-pbc-g-ring`, module `Sheaf.RingTheory.GRing`, declaration
`IsGRing (R : Type u) [CommRing R] : Prop`. I read its full signature and docstring,
and its definitions `Algebra.IsGeometricallyRegular` and `RingHom.IsRegular`.
It requires Noetherianity and regularity of every prime-localization completion
map; regularity includes flatness and geometric regularity of all fibres.
The dependency is usable without repair.

Edge cases checked: the zero prime of Z is included (localization Q with zero-adic
completion itself); nonzero primes give DVR localizations with characteristic-zero
fraction field. The conclusion retains all prime ideals and all finite purely
inseparable test extensions, including the identity extension. There are no
index sets, extra hypotheses, or choice of a different integer ring.

Searches for an existing statement:
- `msearch.py leanfinder`, query “The ring of integers Z is a G-ring: all its local
  completion maps are regular”: eight unrelated integer-ring and completion hits;
  no G-ring theorem.
- `msearch.py loogle`, query `"IsGRing"`: zero hits.
- `msearch.py grep`, query `isGRing|G-ring|geometrically.?regular`, in Mathlib
  `RingTheory`: zero hits.
- `msearch.py leansearch`, query “The integers are a G-ring”: service unavailable
  (Internal Server Error), recorded in `searches.jsonl`; no verdict assigned.
- `rg` over `WeilConjectures` for `IsGRing|G-ring|geometrically.?regular` and
  `lem-weil-pbc-z-g-ring`: no matching declarations. Search of `lean/Sheaf`
  found the shared G-ring definition and related permanence results, but no
  theorem asserting `IsGRing ℤ`.
- Name collision checks over Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no existing `Int.isGRing` declaration.

No statement correction, new nodes, dependency modules, or disputed statements.

## Second reading by J1

I independently read the item node, its sandbox copy and IntGRing.lean, the
full dependency node def-weil-pbc-g-ring and its recorded GRing.lean module.
The local Stacks checkout is absent. I read the upstream more-algebra.tex
at label proposition-ubiquity-G-ring and the official tag pages
https://stacks.math.columbia.edu/tag/07PX,
https://stacks.math.columbia.edu/tag/07GH and
https://stacks.math.columbia.edu/tag/07BZ. Item (3) of 07PX unconditionally
asserts that the integers are a G-ring; the characteristic-zero qualifier
belongs to the separate Dedekind-domain item (4).

The complete object/hypothesis/conclusion list and correspondence is:

- Object: the commutative ring of integers Z. Lean: `ℤ`, with its canonical
  `CommRing` instance supplied to `IsGRing`. Verdict: exactly the same ring.
- Hypotheses: none. Lean: `theorem isGRing : IsGRing ℤ` has no binders or
  section variables. Verdict: no added assumption, including Noetherianity.
- Sole conclusion: Z is a G-ring as defined by def-weil-pbc-g-ring.
  Lean: `IsGRing ℤ`, from the imported `Sheaf.RingTheory.GRing`.
  Verdict: exact. Unfolding the recorded definition gives `IsNoetherianRing ℤ`
  and, for every prime ideal, regularity of the canonical map from
  `Localization.AtPrime p` to its maximal-ideal `AdicCompletion`.
  Thus Noetherianity is asserted, not assumed, and no prime is omitted.

I checked the dependency's actual definitions, not merely their names:
`RingHom.IsRegular` installs the algebra of its map, asserts `f.Flat`, and
quantifies over every prime with `Algebra.IsGeometricallyRegular p.ResidueField
(p.Fiber S)`. Mathlib's `Ideal.Fiber` is the residue-field tensor product.
`Algebra.IsGeometricallyRegular` asserts Noetherianity and regularity of the
base change for every finite purely inseparable field extension.
Mathlib's `IsRegularRing` extends Noetherianity and requires every prime
localization to be regular local. These agree with the dependency node and
07GH/07BZ. The test extension universe is `max u v`, which includes every
finite extension up to isomorphism; it does not make testing vacuous.
No dependency module, missing notion, or new definition node is needed.

Edge cases: the prime `(0)` is included and gives the field Q with its
zero-maximal-ideal completion; all nonzero primes are included and give DVR
localizations. In particular the residue characteristics p, including p = 2,
are unrestricted: geometric regularity tests still include the identity
field extension. The concrete ring Z requires no universe binder; all
universes in its imported predicate are bound. Empty index sets, empty
schemes, zero objects and n = 0 are not parameters of this statement.
There is no nonzero-prime or positive-degree condition hiding in its type.

Independent searches, using terms different from the worker's:

- `msearch.py ... leanfinder "Integers have geometrically regular formal fibres
  at every prime ideal"`: eight hits about smoothness, quasi-finiteness,
  DVR equivalences and regular sequences; none states this claim.
- `msearch.py ... loogle '\"isGRing\"'`: zero hits.
- `msearch.py ... grep 'formal.?fib|IsExcellent|isGRing'`: zero Mathlib hits.
- `rg -n -i 'formal.?fib|IsExcellent|isGRing|G-ring|lem-weil-pbc-z-g-ring'`
  on WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: the project
  contains the shared GRing definition and general permanence/formal-fibre
  lemmas, but no integer G-ring theorem. No upstream declaration matches.
  The shared predicate is used directly; no private replacement is present.

The module and theorem docstrings cite 07PX(3) and the exact blueprint id.
The theorem docstring tracks all four node proof steps: Noetherianity and
localizations, the zero-prime field case, the characteristic-zero DVR
completion case, and exhaustion of primes, with the cited support nodes.
The only declaration has a `sorry` proof; there are no definitions, local
notations, local instances, extra results, or unbound variables. The import
is used and the namespace/name/topic follow the conventions. The node's
`lean.statement` is verbatim `theorem isGRing : IsGRing ℤ`.

Mismatches found: none. Changes: appended this independent second-reading
report only; the correct Lean module and node record are unchanged.

Validation: `scompile.py J1 lem-weil-pbc-z-g-ring` compiled IntGRing.lean
with exit code 0 in 1.6 seconds and no warnings. The required
`deliver2.py J1 lem-weil-pbc-z-g-ring --no-push` printed OK: the delivery
passes preflight and compiles.
