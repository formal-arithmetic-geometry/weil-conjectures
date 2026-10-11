## Worker report

The module `Sheaf.RingTheory.PopescuDelocalizeHeightZero` states
`Algebra.canBePopescuResolved_of_local_height_zero`, with `sorry` as its only proof.
No definition is added and the node is unchanged outside `lean`.

Hypotheses and clauses, in node order:

- Commutative rings R, A, Λ: the three explicit type binders in universes u, v, t
  and their `CommRing` instances. R is Noetherian: `[IsNoetherianRing R]`.
- A and Λ are R-algebras: `[Algebra R A] [Algebra R Λ]`; A is finitely
  presented over R: `[FinitePresentation R A]`.
- The specified R-algebra map A → Λ is `α : A →ₐ[R] Λ`.
- The prime ideal q of Λ is `q : PrimeSpectrum Λ`, whose ideal is `q.asIdeal`.
- The radical extended singular ideal h_A is exactly `Algebra.popescuIdeal α`,
  from the recorded dependency, defined as `(Ideal.map α.toRingHom
  (Algebra.singularIdeal R A)).radical`.
- The contraction p is `q.asIdeal.under R`, definitionally the preimage under
  `algebraMap R Λ`. Its primality and the lies-over relation are Mathlib instances.
- R_p is `Localization.AtPrime (q.asIdeal.under R)` and Λ_q is
  `Localization.AtPrime q.asIdeal`.
- A_p is Mathlib's base-change tensor product `R_p ⊗[R] A`. This uses the factors
  in the order opposite to the node's `A ⊗[R] R_p`, canonically identified by
  `Algebra.TensorProduct.comm`. Its R_p-algebra structure is the usual left-factor
  structure; finite presentation is supplied by `Algebra.FinitePresentation.baseChange`.
- Hypothesis (1): `hminimal : (popescuIdeal α).IsMinimalPrime q.asIdeal`.
- Hypothesis (2): `hlocal` uses `Algebra.CanBePopescuResolved` at the localized
  base R_p and algebra A_p. Its map is the canonical `AlgHom.liftEquiv` applied
  to `(IsScalarTower.toAlgHom R Λ Λ_q).comp α`. This sends `s ⊗ a` to
  the product of the image of s in Λ_q and the localized image of α(a).
  The `letI` supplies Mathlib's canonical
  `Localization.AtPrime.algebraOfLiesOver p q.asIdeal`, without a private
  definition or an extra hypothesis. `IsLocalRing.closedPoint Λ_q` is its
  maximal ideal qΛ_q, by `Localization.AtPrime.map_eq_maximalIdeal`.
- Hypothesis (3): `hdim : ∀ P : Ideal Λ_q, P.IsPrime → P.IsMaximal` is exactly
  the node's explicit meaning of dimension zero. The localization is nonzero
  and local since q is prime, so this also says its maximal ideal is its only prime.
- Conclusion: `CanBePopescuResolved α q`, with the original R, A, Λ and map α.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its
  `isNoetherianRing_iff_ideal_fg` interpretation.
- `Sheaf.RingTheory.PopescuResolution`: `Algebra.popescuIdeal`,
  `Algebra.IsPopescuResolution`, and `Algebra.CanBePopescuResolved`. Read their
  full definitions and docstrings; the existential intermediate carrier has
  universe `max u v`, just as in the recorded dependency.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  also `Localization.AtPrime.algebraOfLiesOver` for the canonical base structure.
- `Sheaf.RingTheory.SingularIdeal`: `Algebra.singularIdeal`, as used by
  `Algebra.popescuIdeal` (imported transitively). Read the full singular-ideal
  definition and its source docstring.
- Further Mathlib tools: `Ideal.IsMinimalPrime`, `AlgHom.liftEquiv`,
  `IsScalarTower.toAlgHom`, `IsLocalRing.closedPoint`; Noetherian localization
  and finite-presentation base change are supplied by the two stability imports.

Edge cases checked before writing: no assumption that Λ is Noetherian or
Artinian is made. A prime q excludes the zero target ring automatically, rather
than by an additional nontriviality hypothesis. If h_A is the unit ideal,
minimality cannot hold. A=0 likewise admits no map into a ring with a prime.
The statement covers dimension-zero nonreduced and non-Noetherian local rings:
`hdim` only concerns prime ideals. Empty lists of generators and variables are
allowed by the proof; the docstring records their empty-sum/product interpretation.
Universes u, v, t are independent, and the base change has carrier universe
max u v; the resolution dependency's universe does not restrict possible
finite-presentation resolutions. No positivity, characteristic, domain, or
Noetherian condition on Λ was introduced.

Searches (the online/Mathlib searches are recorded in `searches.jsonl`):

- LeanSearch, "Delocalizing a Popescu resolution at a prime of height zero":
  unavailable, returned Internal Server Error; no verdict assigned to that service.
- LeanFinder, "Delocalizing a resolution of a finite presentation algebra at a
  prime of height zero": eight hits, on finite presentation of localizations and
  smooth loci. None states the Popescu resolution or this descent statement.
- Loogle, "IsLocalization.map, Algebra.TensorProduct.lift": zero hits.
- msearch grep, "popescu|delocalize|resolve.*height", Mathlib/RingTheory: zero hits.
- rg of the source `WeilConjectures/`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for "delocalize", "CanBePopescuResolved",
  "canBePopescuResolved_of", and the item id: only the project's already
  recorded `PopescuResolution` definitions; no existing theorem.
- Additional Mathlib source searches located `Localization.AtPrime.algebraOfLiesOver`,
  `AlgHom.liftEquiv`, `Algebra.FinitePresentation.baseChange`,
  `Ideal.IsMinimalPrime`, and `IsLocalRing.closedPoint`, whose signatures and
  docstrings were opened before use.

Source check: the local repository lacks `literature/stacks-project/smoothing.tex`.
Opened https://stacks.math.columbia.edu/tag/07FA: its three hypotheses and
conclusion agree with the node. The node already corrects the proof's Artinian
claim and the calculation of B_z; those corrections are carried into the
seven-step declaration docstring. No statement correction or dispute is needed.

Validation: server single-file compilation and delivery dry run (results below).

Server compilation passed in 1.5 seconds with no errors or warnings.
`deliver2.py E1 lem-weil-pbc-popescu-delocalize-height-zero --no-push` printed
OK: compilation and preflight passed except for the independent second reading,
which the second reader supplies. Nothing was pushed.

## Second reading by E1

Independent reading of the sandbox node and module, all four statement-dependency
nodes and their recorded declarations, and Stacks `smoothing.tex`,
`section-local`, `situation-local`, and `lemma-delocalize-height-zero`.
The local literature checkout has no Stacks TeX; I read the actual TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/smoothing.tex,
and checked the tagged presentation at https://stacks.math.columbia.edu/tag/07FA
and its standing situation https://stacks.math.columbia.edu/tag/07F7.
The node has no `statement_change`; no correction or citer audit is needed.

Object, hypothesis and conclusion checklist (in node order):

1. Commutative rings R, A, Lambda: `{R : Type u} {A : Type v} {Λ : Type t}`
   and the three `CommRing` instances. Verdict: exact; independent universes.
2. R Noetherian: `[IsNoetherianRing R]`. I opened the recorded Mathlib
   `Noetherian.Defs` declaration and `isNoetherianRing_iff_ideal_fg`:
   this means every ideal is finitely generated. Verdict: exact.
3. A and Lambda are R-algebras, A finitely presented, and the specified map:
   `[Algebra R A] [Algebra R Λ] [FinitePresentation R A]` and
   `(α : A →ₐ[R] Λ)`. Mathlib `FinitePresentation` means a surjection
   from a finite-variable polynomial algebra with finitely generated kernel.
   Verdict: exact; no Noetherian assumption on Lambda or extra algebra map.
4. Prime q of Lambda: `(q : PrimeSpectrum Λ)` packages its ideal and
   primality, with no maximality or height assumption at this point.
   Verdict: exact.
5. The extended radical singular ideal h_A: `popescuIdeal α`, whose recorded
   definition is `(Ideal.map α.toRingHom (singularIdeal R A)).radical`.
   I opened `PopescuResolution.lean` and `SingularIdeal.lean` and compared
   their full definitions with their DAG nodes. `singularIdeal` is the radical
   of the ideal generated by elements with smooth principal localization;
   neither definition has postponed data. Verdict: the same notion.
6. Contracted prime p: `q.asIdeal.under R`. I opened `Ideal.under` in
   `Ideal.Over`: it is exactly `Ideal.comap (algebraMap R Λ) q.asIdeal`.
   Its primality and lies-over relation are inferred, not assumed additionally.
   Verdict: exact.
7. Localizations R_p and Lambda_q: `Localization.AtPrime (q.asIdeal.under R)`
   and `Localization.AtPrime q.asIdeal`. I read the recorded abbreviation,
   localization at the prime complement, in `Localization.AtPrime.Basic`.
   Verdict: the node's localizations.
8. A_p and its induced map: the source of `AlgHom.liftEquiv` is
   `R_p ⊗[R] A`, with its left-factor R_p-algebra structure. The node writes
   `A ⊗[R] R_p`; tensor symmetry identifies these as R_p-algebras.
   I opened `AlgHom.liftEquiv` and `liftEquiv_tmul`: the displayed map sends
   `s ⊗ a` to the image of s times the localized image of `α a`.
   `IsScalarTower.toAlgHom` supplies the canonical map Lambda to Lambda_q.
   The local `letI` is precisely Mathlib's `algebraOfLiesOver`, defined using
   the local ring hom induced by R to Lambda; it supplies canonical data,
   not another hypothesis. Verdict: exact base change and induced map.
9. Hypothesis (1): `(hminimal : (popescuIdeal α).IsMinimalPrime q.asIdeal)`.
   I opened `Ideal.IsMinimalPrime`: minimal among prime ideals containing
   the specified ideal, not minimal among all primes of Lambda.
   Verdict: exact, including containment of h_A.
10. Hypothesis (2): `hlocal` is `CanBePopescuResolved` for that same induced
    R_p-algebra map, at `IsLocalRing.closedPoint Lambda_q`. I opened
    `closedPoint` (maximal ideal packaged as a prime), and
    `IsLocalization.AtPrime.map_eq_maximalIdeal`, identifying this ideal
    with q Lambda_q. R_p Noetherian and A_p finitely presented are inferred
    from localization stability and `FinitePresentation.baseChange`, supplied
    by the two corresponding imports. Verdict: exactly the localized problem,
    without additional finite type, flatness or smoothness hypotheses.
11. Hypothesis (3): `hdim : ∀ P : Ideal Lambda_q, P.IsPrime → P.IsMaximal`.
    This is the node's explicitly stated meaning of dimension zero.
    Lambda_q is nonzero local because q is prime; thus it also has precisely
    one prime ideal. Verdict: exact, without requiring it to be Artinian.
12. Conclusion: `CanBePopescuResolved α q` for the original map and prime.
    Its recorded definition existentially supplies B, its commutative ring
    and R-algebra structures, beta and gamma; `IsPopescuResolution` requires
    finite presentation over R, `gamma.comp beta = alpha`, h_A contained
    in h_B, and h_B not contained in q. Verdict: every conclusion clause,
    with the same factorization and quantifier order as the node.

Edge cases: all characteristics are allowed, with no field or domain
assumption. A prime q already excludes a zero Lambda, and maps from a zero
R or A into such a Lambda cannot exist; no extra nontriviality binder was
introduced. Empty lists of generators, relations or variables (including n=0)
are allowed by finite presentation and by the seven-step proof description.
There is no scheme or test-index quantifier in this statement. Nonreduced,
non-Noetherian zero-dimensional Lambda_q is covered: only primes being
maximal is assumed. The resolution carrier universe `max u v` is the recorded
dependency's choice; any finitely presented intermediate algebra has a
finite-polynomial quotient model in that universe. The local base-change
carrier lives in `max u v`, so the localized resolution has the same bound.
No bound on the independent target universe t is imposed.

Independent searches, using wording different from the worker's (also logged
by msearch in `searches.jsonl`):

- LeanFinder: "Descent of a factorization enlarging the smooth locus from
  localizations at minimal primes" returned eight hits, chiefly smooth-locus
  openness, principal localizations, and standard smoothness. No hit states
  the resolution descent or existential factorization of this node.
- Loogle: `Ideal.IsMinimalPrime, Localization.AtPrime` returned zero hits.
- LeanSearch: "A factorization of a finitely presented ring algebra enlarging
  the singular ideal descends from a zero dimensional localization" returned
  Internal Server Error; recorded unavailable, without a service verdict.
- Direct rg, case-insensitive `07FA|height.zero.*resolv|resolv.*height.zero|
  delocaliz|popescu`, over Mathlib/RingTheory, the source `WeilConjectures`,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`: only the existing
  resolution definitions, an unrelated G-ring approximation docstring, and
  unrelated Gabriel-Popescu category theory. No existing statement found.

No new definition nodes or dependency modules occur in this delivery; none is
needed. The four recorded statement dependencies are usable as they stand.
I checked all seven proof-docstring steps against the node: finite generators,
elementwise nilpotence and denominator clearing, weak delocalization to C,
the auxiliary B and map, smoothness after inverting zc', smoothness after
inverting a_l y_l, and both radical-ideal conditions of the resolution.
The docstring preserves the node's repairs to the source's proof without
changing its statement. There is one theorem with `sorry` and no definition
or proved auxiliary statement in the delivered module. Header, namespace,
source/blueprint references and line lengths follow the conventions.

Mismatches and changes: none found in the Lean or node. Left both intact;
added this independent reading and its search evidence to the report.
The node's `lean.statement` was checked character-for-character against the
signature up to `:=`; all universes and variables are explicitly bound.
Independent server single-file compilation passed in 1.6 seconds, exit 0,
without warnings. Delivery dry run and push are performed after this reading.
