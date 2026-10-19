## Worker report

The module `Sheaf.RingTheory.FinitelyPresentedAlgebraModuleGenericFreeness` states
`Module.exists_free_away_of_finitePresentation`, with `sorry` as its entire proof.
No definitions, new nodes, dependency modules, or statement corrections are needed.
The source was read in `literature/stacks-project/algebra.tex`, label
`lemma-generic-flatness-finitely-presented` (Tag 051S), including its proof.

Hypotheses and conclusion, clause by clause:

- A commutative integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`.
- A commutative R-algebra A: `(A : Type v) [CommRing A] [Algebra R A]`.
- A presentation by finitely many variables and finitely many relations:
  `[Algebra.FinitePresentation R A]`. Its `out` is a surjection from
  `MvPolynomial (Fin n) R` with finitely generated kernel, exactly the stated quotient.
  This permits n = 0 and the zero ideal (zero relations).
- An A-module L: `(L : Type w) [AddCommGroup L] [Module A L]`.
  `[Module R L] [IsScalarTower R A L]` expresses precisely restriction of this
  action along the given R-algebra map, not a further condition on the A-module.
  Indeed the tower identity with the algebra element 1 forces the R-action to
  be r • l = (algebraMap R A r) • l, and that restricted action always exists.
- Finite presentation of L over A: `[Module.FinitePresentation A L]`, not over R.
- A nonzero base element: `∃ a : R, a ≠ 0 ∧ ...`.
- The localized base R[1/a]: `Localization.Away a`.
- The localized module L_a: `LocalizedModule.Away a L`, whose existing quotient
  construction uses `Submonoid.powers a`. Its `LocalizedModule.mk_eq` identifies
  two fractions exactly when a further denominator equalizes the cross-products;
  for additive groups this is the displayed annihilating-power criterion.
  The canonical module structure over `Localization.Away a` is used.
- Freeness, without finite rank: `Module.Free (Localization.Away a)
  (LocalizedModule.Away a L)`. `Module.Free.exists_basis` quantifies over an
  arbitrary index type, whose basis representation is the finitely supported
  direct sum. It imposes no finite-index assumption.
- No Noetherian hypothesis: none occurs. The three carrier universes u, v, w
  are independent and explicitly bound.

Dependency declarations inspected and used:

- `def-sc-finitely-presented-module`: `Mathlib.Algebra.Module.FinitePresentation`,
  `Module.FinitePresentation`; read the class and `exists_fin'` giving the
  finite free right-exact presentation.
- `def-weil-ring-localization-away`: recorded module
  `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`; imported
  transitively through `Mathlib.RingTheory.Localization.Away.Basic` for its ring
  structure. Read the abbreviation and localization-away documentation.
- `def-weil-pbc-module-localization-away`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule.Away`;
  read the fraction relation, `mk_eq`, and localized scalar structure.
- Algebra finite presentation and free modules use Mathlib's existing classes,
  respectively `Mathlib.RingTheory.FinitePresentation` and
  `Mathlib.LinearAlgebra.FreeModule.Basic`.
- Proof dependencies: finite-type Noetherian permanence is already available
  through the finite-presentation import; tensor-product universal properties
  are imported proof-only through `Mathlib.RingTheory.TensorProduct.Basic` (the actual location of
  `LinearMap.liftBaseChangeEquiv`, `liftBaseChange_tmul`, and
  `liftBaseChangeEquiv_symm_apply` in this pinned checkout; the proof dependency
  record names the older LinearAlgebra path).
  The Noetherian algebra-module generic-freeness proof dependency has no Lean
  record and hence no module to import yet. Its later proof import is for the
  maintainer. All seven node proof steps are included in the theorem docstring.

Edge cases checked mathematically: L = 0 (empty basis, a = 1); A = 0
(then every unital A-module is zero); zero polynomial variables; zero algebra
relations; zero module generators/relations; R a field; non-Noetherian domain;
and A = R[x], L = A (typically infinite rank over R, so a finite basis
conclusion would be incorrect). The zero base ring is excluded by IsDomain,
exactly as by the integral-domain hypothesis. There is no finite-rank restriction.

Searches, performed with the prescribed msearch.py wrapper (logs in searches.jsonl):

- LeanFinder: "A finitely presented module over a finitely presented algebra
  over an integral domain becomes free over the base after inverting one nonzero
  element". Eight hits, led by
  `Module.FinitePresentation.exists_free_localizedModule_powers`. Read its full
  source signature and docstring in `Mathlib/RingTheory/Localization/Free.lean`:
  it requires finite presentation over the BASE R and does not match this node.
  The PID freeness results and finite-module cover theorem also do not match.
- Loogle: `Module.Free, Algebra.FinitePresentation`. Two hits: a cotangent
  presentation theorem and `Module.Finite.exists_free_surjective`; neither is
  this statement.
- Mathlib grep: `generic.*free|exists_free_localizedModule|genericFreeness`.
  Six hits, localized finite-presentation freeness and unrelated polynomial names.
- LeanSearch: "Generic freeness for finitely presented algebra module pairs
  over an integral domain". Service unavailable (Internal Server Error).
- Project/upstream rg: `generic.*[Ff]ree|genericFreeness|exists_free_localizedModule|
  lem-pur-fp-algebra-module-generic-freeness`. Upstream FreeLocus has generic
  freeness for BASE-finite modules and Noetherian algebra-module generic FLATNESS;
  read its signatures and documentation. Side `GenericFlatness.lean` gives
  flatness of an algebra localization, not freeness of a general localized
  algebra-module pair. Other hits concern geometric finite-rank situations.
- Name collision search for `GenericFreeness|exists_free_away_of_finitePresentation|
  generic_freeness_of_finitePresentation` in upstream names, project and side
  sources, and a Mathlib search for the chosen theorem name: no collision.

No statement dispute or fault in the item's statement was found.

## Second reading by NB

Independently read the node and its seven proof steps, the complete statement and
proof of Stacks Algebra Tag 051S (`lemma-generic-flatness-finitely-presented`),
and the delivered Lean file. The source introduces a ring map, a domain base,
a finitely presented algebra, and a finitely presented module over that algebra;
there is no standing Noetherian hypothesis. Verdict: the Lean states exactly
the node and source. No mathematical or syntactic mismatch was found, and no
module or node change was needed.

Object/hypothesis/conclusion checklist, in source order:

- Base commutative integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`.
  Exact; in particular the zero base ring is excluded.
- Commutative R-algebra A and its fixed structure map: `(A : Type v)
  [CommRing A] [Algebra R A]`. Exact; neither injectivity nor a domain
  hypothesis on A is imposed.
- Finitely many polynomial variables and relations: `[Algebra.FinitePresentation R A]`.
  Read the class in `Mathlib.RingTheory.FinitePresentation`: its `out` is a
  surjective algebra map from `MvPolynomial (Fin n) R` with finitely generated
  kernel. This is precisely the displayed finite quotient presentation.
- A-module L: `(L : Type w) [AddCommGroup L] [Module A L]`. Exact.
  `[Module R L] [IsScalarTower R A L]` supplies restriction along the algebra
  map. This is no extra mathematical hypothesis: the tower law applied to
  `r • (1 : A)` acting on l forces `r • l = (algebraMap R A r) • l`;
  conversely every A-module carries this restriction.
- Finite presentation over A: `[Module.FinitePresentation A L]`. Exact, not
  finite presentation over R. Read the dependency's class and `exists_fin'`
  in `Mathlib.Algebra.Module.FinitePresentation`: finite generators and a
  finitely generated relation kernel give the node's finite exact presentation.
- One nonzero element of the base: `∃ a : R, a ≠ 0 ∧ ...`. Exact existential
  order; a may depend on the algebra-module pair.
- Localized base: `Localization.Away a`. Exact dependency declaration; read
  its abbreviation as `Localization (Submonoid.powers a)` and the ring
  localization import. This inverts a in R, not an arbitrary element of A.
- Localized module: `LocalizedModule.Away a L`. Exact dependency declaration;
  read its abbreviation, quotient relation and `LocalizedModule.mk_eq` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`. Its relation is the existence
  of a power of a equalizing cross products, equivalently annihilating their
  difference. The standard localized scalar action is used.
- Free over the localized base: `Free (Localization.Away a)
  (LocalizedModule.Away a L)` in namespace Module. Exact; read
  `Module.Free.exists_basis`, which allows an arbitrary basis index type and
  whose basis representation is a finitely supported sum. No finite-rank
  conclusion or freeness over A is substituted.
- No Noetherian assumption: absent, as required. Universes u, v, w are bound
  independently; the localization universe is their appropriate maximum.
  A basis can always be indexed by a subset of its carrier, so the universe
  of `Free.exists_basis` excludes no free module.

Edge cases: zero L uses the empty basis and a = 1; zero A forces zero L and
is permitted; zero variables, zero relations, and zero module generators or
relations are permitted by the two finite-presentation classes. Fields in any
characteristic and non-Noetherian domains are included. For A = R[x], L = A,
the basis can be infinite, as required. No scheme, n > 0, finite-index,
characteristic-zero, or extra universe hypothesis is introduced.

Independent searches (in addition to reading the first worker's results):
LeanFinder query “After localizing a non-Noetherian domain, a finitely presented
module over a finitely presented algebra is a free module over the base domain”
returned eight related results, principally
`Module.FinitePresentation.exists_free_localizedModule_powers`. Read its full
signature: it requires finite presentation over the base, and hence does not
cover this node. Loogle `Algebra.FinitePresentation, Module.Free` returned only
a cotangent-presentation result and `Module.Finite.exists_free_surjective`;
neither is this theorem. LeanSearch query “A finitely presented algebra and
finitely presented module over it are generically free over an integral domain”
was unavailable (Internal Server Error). Searches are recorded by msearch.py.
Independently ran rg with `generic.?free|free.*finitepresentation|free.*finitetype`
over upstream WeilConjectures, side lean/Sheaf and Mathlib's FreeLocus, and
searched the relevant finite-presentation/localization sources. Read upstream
`Module.Finite.exists_free_localizedModule_powers_of_isDomain`: it requires
base-finite modules. Upstream generic flatness and side
`Algebra.exists_nonzero_flat_localizationAway` give flatness rather than this
module freeness statement. No exact existing statement was found. An exact
name search in Mathlib, upstream, side sources and dag/lean_names_upstream.json
found no collision.

No new definition nodes or dependency modules are present or necessary.
The dependency declarations all encode the notions their nodes specify.
Read the proof tools `Algebra.FiniteType.isNoetherianRing` and
`LinearMap.liftBaseChangeEquiv` with its pure-tensor/restriction formulas.
The latter lives in the imported RingTheory tensor module in this checkout.
The Noetherian generic-freeness dependency remains unstated, so has no import.
The seven numbered docstring steps match the node: presentations, coefficient
subring, scalar-extension identification, Noetherian generic freeness, the
localized comparison, localization of the coefficient base, and scalar
extension of a possibly infinite basis. Source and blueprint annotations,
100-column convention, explicit universes and binders, and the sole `sorry`
proof were checked. There are no definitions or file-local encodings.
The recorded `lean.statement` is verbatim the file signature. No statement
correction or citer review is needed.
