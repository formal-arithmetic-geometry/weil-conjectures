## Worker report

The module `Sheaf.RingTheory.PuncturedIdempotentComplement` states
`RingHom.exists_surjective_complement_of_localization_idempotent`, with its proof
left as `sorry`. No definitions, auxiliary theorems, or new nodes are needed.
The source was read directly in `literature/stacks-project/more-algebra.tex`,
Tag 0C2A, `lemma-glueing-sum-components-open`, including its proof.

Hypotheses and conclusion, matched clause by clause:

- A commutative ring R: `{R : Type u} [CommRing R]`.
- A finitely generated ideal K, allowing an empty generating list:
  `(K : Ideal R) (hK : K.FG)`. Mathlib's `Ideal.FG` means that K is the span
  of a finite subset; that subset can be empty. An enumerated list is not
  used by either hypothesis or conclusion, so no generators are chosen in
  the statement.
- A homomorphism of commutative rings u: `{E : Type v} [CommRing E]`
  and `(u : R →+* E)`. The ring universes are independent.
- Every f in K: `∀ f ∈ K` in both hypothesis and conclusion, not only
  the finite generators.
- R_f and E_f: `Localization.Away f` and `Localization.Away (u f)`.
- An idempotent e_f in R_f: `∃ e : Localization.Away f, IsIdempotentElem e`.
  `IsIdempotentElem e` means `e * e = e`, equivalently `e^2 = e`.
- The given map u_f exhibits E_f as localization at e_f:
  `@IsLocalization.Away (Localization.Away f) _ e (Localization.Away (u f)) _
  (Localization.awayMap u f).toAlgebra`.
  The algebra structure is explicitly the one induced by u_f, preventing an
  unrelated abstract ring isomorphism from satisfying the hypothesis.
  This is precisely the localization characterization in the recorded
  dependency `def-weil-ring-localization-away` and its `mathlib_match`.
- A commutative ring E' and a surjective ring homomorphism v from R:
  `∃ (E' : Type u) (_ : CommRing E') (v : R →+* E'), Function.Surjective v ∧ ...`.
  Taking E' in R's universe excludes no case: every surjective image of R
  is isomorphic to the quotient by its kernel, and the source construction
  specifically takes E' = R/J.
- The map (u,v)_f itself is an isomorphism:
  `Function.Bijective (Localization.awayMap (u.prod v) f)`.
  Its codomain is the localization of the product E × E' at `(u f, v f)`.
  Bijectivity of this ring homomorphism is exactly being a ring isomorphism;
  no arbitrary isomorphism or separate factorwise replacement is asserted.

The statement-dependency record was read in full. It records
`Localization.Away` in `Mathlib.GroupTheory.MonoidLocalization.Away`;
the ring API is imported through `Mathlib.RingTheory.Localization.Away.Basic`.
The same recorded node's `mathlib_match` explicitly gives
`IsLocalization.Away`, also used here. The source signatures and docstrings
of these declarations and `Localization.awayMap` were read. No localization
or induced map is defined a second time.

The stated proof dependencies are imported privately:

- `lem-weil-pbc-localization-quotient-commute` has the Mathlib match
  in `Mathlib.RingTheory.Localization.Ideal` (quotient-localization instance)
  and `IsLocalization.algEquiv` in `Mathlib.RingTheory.Localization.Basic`.
  Their source signatures were read; these give the compatibility used in
  proof step 5. The instance is imported through the former module.
- `def-weil-pbc-module-localization-away` records `LocalizedModule.Away`
  in `Mathlib.Algebra.Module.LocalizedModule.Basic`, which is imported.
- `lem-weil-pbc-cover-module-exact` records `RingTheory.coverModuleExact`
  in `WeilConjectures.RingTheory.CoverModuleExact`, which is imported.
  Its full signature and proof docstring were read, including both
  injectivity and unique gluing clauses and the empty-cover case.

The theorem docstring includes all eight DAG proof steps: empty generators;
uniform fraction representatives satisfying actual idempotence relations;
equality of the idempotents on overlaps using both product identities;
uniform rescaling; the complementary quotient and quotient-localization
compatibility; decomposition at an idempotent; the canonical product
comparison; and injectivity plus gluing over the cover for an arbitrary f in K.

Edge cases checked mathematically before writing:

- K = 0 and an empty generating list: f must be zero and all localizations
  in question are zero rings. E' = R and v = id suffice.
- Nilpotent f, including f = 0: the localizations are zero rings, which are
  allowed because there is no `Nontrivial` hypothesis.
- R itself the zero ring: ring homomorphisms force E to be the zero ring
  as well; the same quotient conclusion is allowed.
- K = R: the hypothesis at f = 1 is localization at a global idempotent;
  the complementary quotient gives the usual product decomposition.
- Local idempotents zero and one: they respectively allow a zero E_f or
  an isomorphic E_f, with the complementary factor respectively R_f or zero.
- No hypothesis requires u globally surjective, R Noetherian, or K proper.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query “A ring map which is localization
  at an idempotent away from a finitely generated ideal admits a complementary
  quotient with product locally isomorphic to the ring”: eight hits, including
  `IsLocalization.Away.quotient_of_isIdempotentElem`,
  `IsLocalization.away_of_isIdempotentElem`, and
  `RingHom.prod_bijective_of_isIdempotentElem`. These handle a given global
  idempotent, not one quotient working on the punctured ideal.
- `msearch.py ... loogle '"IsIdempotentElem", "Localization"'`: four hits,
  the single-idempotent surjectivity/localization/quotient results; no match.
- `msearch.py ... leansearch` with query “A ring map which is localization
  at an idempotent outside a finitely generated ideal admits a complementary
  quotient ring”: eight hits, including the preceding idempotent results,
  `IsLocalization.of_surjective`, and
  `AlgEquiv.prodQuotientOfIsIdempotentElem`; no simultaneous complementary quotient.
- `msearch.py ... grep
  'quotient_of_isIdempotentElem|prodQuotientOfIsIdempotentElem|punctured.*complement'
  RingTheory`: four hits in Localization/Away/Lemmas, Idempotents, Ideal/Pure,
  and Unramified/Basic. The matching idempotent declarations were read and
  do not state this gluing result.
- `rg` over both project source trees with the item id and
  `punctured.*[Ii]dempotent|[Ii]dempotent.*[Cc]omplement|glueing.sum.components`:
  only unrelated geometric or linear idempotent constructions.
- The required `grep -rn` for the item id over `lean/WeilConjectures`
  returned no declaration. A further `rg` of `dag/lean_names_upstream.json`
  and `lean/Sheaf` for the new declaration name and gluing terminology
  likewise found no existing statement.

Validation: `scompile.py NB lem-per-punctured-idempotent-complement` compiled
the sandbox module and its library-path form cleanly, with no errors or warnings
(2.2 seconds and 1.6 seconds). All variables and universes are explicit;
the module uses no file-local definitions, notation, instances, or let binders.
Only the item's `lean` field changes in the copied node. No statement fault,
statement correction, dependency repair, or disputed statement was found.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
