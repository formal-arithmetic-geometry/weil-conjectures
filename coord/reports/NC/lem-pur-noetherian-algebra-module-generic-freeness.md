## Worker report

The module `Sheaf.RingTheory.NoetherianAlgebraModuleGenericFreeness` states
`Module.noetherian_algebra_module_generic_freeness`, with its whole proof `sorry`.
The source read was Stacks Algebra, Tag 051R,
`lemma-generic-flatness-Noetherian` (algebra.tex, lines 28457–28528).
The node's statement agrees with the source; no correction or new node is needed.
The declaration docstring records all eight proof steps of the node, including
its zero-generic-algebra case and the dimension-drop argument.

Hypothesis and clause correspondence:

- The commutative Noetherian domain R is `(R : Type u) [CommRing R]
  [IsNoetherianRing R] [IsDomain R]`. In particular, the zero base ring is
  excluded by exactly the source's domain hypothesis.
- The commutative finite type R-algebra B is `(B : Type v) [CommRing B]
  [Algebra R B] [Algebra.FiniteType R B]`. The equivalence with a quotient of
  a polynomial ring in finitely many variables is
  `Algebra.FiniteType.iff_quotient_mvPolynomial''`, read at FiniteType.lean:172–180;
  its surjection identifies B with the quotient by its kernel. This includes n = 0.
- The finitely generated B-module is `(M : Type w) [AddCommGroup M]
  [Module B M] [Module.Finite B M]`. The additional structure binders
  `[Module R M] [IsScalarTower R B M]` specify restriction of scalars along
  the given algebra map, not an extra mathematical hypothesis: every B-module
  has this structure, and compatibility forces `r • m = (algebraMap R B r) • m`
  by applying the tower identity to 1 in B.
- `∃ a : R, a ≠ 0 ∧ ...` gives precisely the nonzero base scalar.
- `Localization.Away a` is the recorded R[1/a].
- `LocalizedModule.Away a M` uses the same restricted R-action on M and is
  precisely the fractions module in the node. Basic.lean:103 `LocalizedModule.mk_eq`
  gives equality iff some denominator power kills the cross difference;
  the `Away` abbreviation at Basic.lean:1478 specializes to powers of a.
- `Module.Free (Localization.Away a) (LocalizedModule.Away a M)` asserts
  the existence of an arbitrary basis, equivalently an isomorphism with a
  direct sum of copies of R_a. FreeModule/Basic.lean:43–44 quantifies over an
  arbitrary type, with no Fintype assumption or finite-rank conclusion.
  Independent universes u, v, w allow the rings and module to have different sizes.

Recorded statement dependencies used, with their source signatures/docstrings read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbreviation
  for `IsNoetherian R R`; lines 195–207 identify this with finite generation
  of every ideal (def-weil-pbc-noetherian-ring).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, lines 116–119,
  finite generation of the top submodule (def-weil-finitely-generated-module).
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`,
  lines 140–144, localization at powers (def-weil-ring-localization-away).
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`,
  with its fraction quotient construction and induced localized-ring action
  (def-weil-pbc-module-localization-away).

Proof-plan imports include Mathlib Noether normalization, prime filtration,
`WeilConjectures.Mathlib.RingTheory.NoetherNormalization` (the dimension theorem),
and `Sheaf.RingTheory.NoetherNormalizationOverDomain` (the recorded domain
normalization theorem). The other proof-only definitions, `ringKrullDim` and
`MvPolynomial`, and finite-type Noetherian permanence are supplied by these imports.

Edge cases checked mathematically before writing: M = 0 is free on the empty basis;
B = 0 forces M = 0 and is allowed (no Nontrivial B binder). A noninjective R → B
is allowed; the source explicitly treats a nonzero kernel by killing the algebra.
For B = R[x], M = B, freeness can have infinite rank over R, which this statement
allows. For R a field, a = 1 works. Finite presentations with zero variables and
empty prime filtrations are retained. No characteristic or rank is restricted.

Searches actually run through msearch.py:

- LeanFinder: “A finite module over a finite type algebra over a Noetherian
  integral domain becomes free over the base after localizing at a nonzero
  scalar”. Eight hits, principally
  `Module.FinitePresentation.exists_free_localizedModule_powers` and
  localization finiteness results. The former's full signature was read at
  Localization/Free.lean:78–91: it requires finite presentation over the base
  and generic freeness already, so does not match this algebra-module result.
- Loogle: `Module.Free, Algebra.FiniteType`: zero hits.
- LeanSearch: “generic freeness of a finite module over a finite type algebra
  over a Noetherian domain”: unavailable, HTTP Internal Server Error.
- Mathlib grep: `generic.*free|exists_free_localizedModule|Free.*FiniteType`:
  seven hits, involving FreeLocus, Localization/Free and unrelated free algebras.
- rg over upstream WeilConjectures and project lean/Sheaf for
  `generic.*[Ff]ree|generic_freeness|lem-pur-noetherian-algebra-module-generic-freeness`:
  found upstream FreeLocus, chart/sheaf generic freeness and the project's
  GenericFlatness proof commentary. Upstream FreeLocus's finite-module theorem
  is finite over the base; its finite-algebra-module theorem concludes flatness,
  not freeness. None states this node. The upstream module's docstring and
  finite-base result were opened to verify this distinction.
- rg for `noetherian_algebra_module_generic_freeness` in upstream and project
  Lean sources returned no name collision.

Validation uses only scompile.py on the server, with nice 19, two threads and
60 seconds per file. The first compile requested a public import for
`Localization.Away`; this was fixed by publicly importing its recorded module.

## Second reading by NC

I independently read the sandbox node, its eight proof steps and Lean module,
Stacks algebra.tex, Tag 051R (lemma-generic-flatness-Noetherian), and the
chapter's conventions (commutative unital rings, including the zero ring).
The source has exactly the four hypotheses in the node; no ambient field,
characteristic, injectivity, or nonzero-algebra hypothesis is implicit.

Object, hypothesis and conclusion checklist (all pass):

1. Base R: `(R : Type u) [CommRing R] [IsNoetherianRing R] [IsDomain R]`
   renders a commutative Noetherian integral domain, exactly. I opened the
   dependency def-weil-pbc-noetherian-ring and Mathlib's definition and
   `isNoetherianRing_iff_ideal_fg`: all ideals are finitely generated.
2. Algebra B: `(B : Type v) [CommRing B] [Algebra R B]
   [Algebra.FiniteType R B]` renders the commutative finite type R-algebra.
   I read `Algebra.FiniteType.iff_quotient_mvPolynomial''`: the surjection
   from `MvPolynomial (Fin n) R` gives exactly the node's finite polynomial
   quotient presentation, including n = 0. The algebra map need not be injective.
3. Module M: `(M : Type w) [AddCommGroup M] [Module B M]
   [Module.Finite B M]` renders a finitely generated B-module. I opened
   def-weil-finitely-generated-module and `Module.Finite`, whose `fg_top`
   is precisely finite generation, rather than finiteness of the carrier.
4. Restricted R-action: `[Module R M] [IsScalarTower R B M]` supplies
   the action needed to form M_a. It imposes no additional mathematical
   condition on a B-module: restriction along `algebraMap R B` always supplies
   it, and compatibility with the B-action forces exactly that action by
   applying the tower identity to `r`, `1 : B`, and `m`.
5. Nonzero scalar and quantifier order: `∃ a : R, a ≠ 0 ∧ ...` follows all
   the input binders. The scalar may depend on the whole algebra-module pair,
   exactly as in the node and source.
6. Base localization: `Localization.Away a` is the recorded declaration of
   def-weil-ring-localization-away. I opened its abbreviation: localization
   at `Submonoid.powers a`, namely R[1/a].
7. Module localization: `LocalizedModule.Away a M` is the recorded declaration
   of def-weil-pbc-module-localization-away, not a substitute. I opened that
   node, the abbreviation and `LocalizedModule.mk_eq`: its quotient identifies
   fractions exactly when a further power kills the cross difference, as
   in the node, and has the induced `Localization.Away a`-module action.
8. Freeness: `Module.Free (Localization.Away a) (LocalizedModule.Away a M)`
   says exactly that this module has a basis. I read `Module.Free.exists_basis`,
   `free_iff_set`, and `Free.of_basis`: the index can be any set of basis
   elements, without a finite-index or finite-rank condition. Thus this is
   precisely an isomorphism with a direct sum of copies of R_a.

Edge cases: zero M and zero B are allowed, with the empty basis; zero R is
excluded exactly by the integral-domain hypothesis. A nonzero kernel of R to B
is allowed, as required by the source's zero-localization case. For B = R[x]
and M = B the conclusion permits an infinite monomial basis. A field base
permits a = 1. Zero-variable polynomial presentations, empty filtrations and
generic dimension zero are retained. No characteristic restriction occurs.
The independent bound universes u, v, w impose no relation between sizes of
R, B and M. The basis can be reindexed by its image inside the module, so the
universe used by `Module.Free` excludes no possible basis. Scheme and index-set
hypotheses do not occur in this algebraic statement.

Independent searches used different wording from the worker:

- LeanFinder through msearch.py: “Finite algebra module over Noetherian domain
  is free after inverting a nonzero element of base”: eight hits, principally
  `Module.Finite.left`, finite fraction-field extensions and PID freeness.
  None states algebra-module generic freeness over an arbitrary Noetherian domain.
- Loogle through msearch.py: `Module.Free, IsNoetherianRing`: zero hits.
- LeanSearch through msearch.py: “finite algebra module generically free over
  integral Noetherian base”: unavailable (Internal Server Error), recorded
  as unavailable rather than treated as a negative search result.
- rg in Mathlib, upstream WeilConjectures, project lean/Sheaf and the upstream
  names table for `generically.*free`, `free.*localiz`, `genericFreeness`,
  `generic_freeness`, and the proposed declaration name. I opened Mathlib's
  `Module.FinitePresentation.exists_free_localizedModule_powers`: it assumes
  finite presentation over the base and freeness at a prior localization.
  I also opened upstream Spectrum/Prime/FreeLocus.lean:123, the finite-base
  generic-freeness theorem, which requires `Module.Finite A M`, absent here.
  That file's algebra-module theorem `exists_flat_localizedModule_powers`
  concludes flatness, not freeness. The other project hits use these results
  in special geometric situations. There is no matching existing declaration
  or collision with this theorem's full name.

There are no new definition nodes or dependency modules in this delivery and
no statement correction. All four statement dependencies have usable recorded
Mathlib declarations, publicly imported. I read the proof-plan imports and
checked the eight numbered docstring steps against the node: fraction exactness,
bases and extensions, generic dimension induction and zero case, normalization,
a common cokernel annihilator, strict dimension drop, the domain case, and
prime-filtration reduction are all present. Source and blueprint tags are
present on the module and theorem. There are no new definitions, hollow data,
file-local notation or instances, hidden let/show binders, or proved theorems.
All variables and universes are explicitly bound. The node's lean.statement is
verbatim the theorem signature, excluding its proof.

Mismatches found: none. Changes: this independent second-reading section only;
the correct Lean module and node record were retained unchanged.
Compilation passed cleanly through scompile.py on the server: 1.1 seconds,
nice 19, two threads, 60-second per-file limit, no errors or warnings.
