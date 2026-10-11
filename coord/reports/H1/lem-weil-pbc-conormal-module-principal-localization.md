## Worker report

The module `Sheaf.RingTheory.ConormalModulePrincipalLocalization` states
`Algebra.Extension.conormalModule_principalLocalization`, with `sorry` as its only proof.
No definition, dependency module, or node correction is needed.

### Hypotheses and clauses

- A commutative ring R: `{R : Type u} [CommRing R]`.
- An R-algebra S: `{S : Type v} [CommRing S] [Algebra R S]`.
- An element g of S: `(g : S)`.
- S_g, localization at the powers of g: `Localization.Away g`. Its canonical R-algebra
  structure is the composite R → S → S_g. Using the canonical localization loses no case:
  any ring representing this localization is canonically isomorphic as an S-algebra.
- Nonnegative integers n,m: `(n m : ℕ)`; zero is included.
- Polynomial rings in n and m variables: `MvPolynomial (Fin n) R` and
  `MvPolynomial (Fin m) R`. Relabelling variables 1,…,n by `Fin n` is immaterial.
- Surjective R-algebra homomorphisms α and β: the two `→ₐ[R]` binders and
  `hα : Function.Surjective α`, `hβ : Function.Surjective β`.
- I=ker α and J=ker β: the kernels of `ofSurjective α hα` and `ofSurjective β hβ`.
  `ofSurjective` uses exactly the input algebra homomorphism as its structure map.
- I/I² is an S-module and J/J² is an S_g-module: Mathlib's
  `(ofSurjective α hα).Cotangent` and `(ofSurjective β hβ).Cotangent` are type synonyms
  for the kernel conormal quotients, with `Algebra.Extension.Cotangent.module` providing
  the quotient scalar actions. These clauses are supplied by the structures on the objects,
  rather than existentially choosing unrelated module structures.
- (I/I²)_g: `LocalizedModule.Away g (ofSurjective α hα).Cotangent`, carrying the canonical
  `Localization.Away g`-module instance.
- Free summands of ranks m and n: `(Fin m → Localization.Away g)` and
  `(Fin n → Localization.Away g)`. For a finite index set, this is exactly the finite direct
  sum (every function is finitely supported). Binary direct sums are module products `×`.
- Existence of the stated S_g-linear isomorphism, with the free ranks in the stated order:
  `Nonempty ((LocalizedModule.Away g (ofSurjective α hα).Cotangent ×
  (Fin m → Localization.Away g)) ≃ₗ[Localization.Away g]
  ((ofSurjective β hβ).Cotangent × (Fin n → Localization.Away g)))`.

### Dependencies and source reading

- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`; the ring structure and algebra used here
  are imported through `Mathlib.RingTheory.Localization.Away.Basic`. Read its definition
  as `Localization (Submonoid.powers g)` and the signature/docstring of
  `IsLocalization.Away` in the ring localization module.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`; also read `MvPolynomial.algHom_ext` there and
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`. Imported transitively
  through `Mathlib.RingTheory.Extension.Basic`.
- `def-weil-pbc-module-localization-away`: `LocalizedModule.Away`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`. Also read `LocalizedModule.mkLinearMap`
  and `IsLocalizedModule.lift`, as in its lean record. Only the localized object is needed
  by this statement; the canonical-map clause of that definition is not needed here.
- Conormal quotients use the existing `Algebra.Extension.ofSurjective`,
  `Algebra.Extension.Cotangent`, and `Algebra.Extension.Cotangent.module`, all read with
  their signatures and docstrings in `Mathlib.RingTheory.Extension.Basic`.

The referenced local Stacks TeX file is absent on this machine. Read the primary source
https://stacks.math.columbia.edu/tag/00S6 instead. Its statement is the node's statement;
finite type follows already from the finite-variable surjection α, so an extra finite-type
hypothesis is unnecessary. The declaration docstring carries the node's six proof steps
and names the ingredients. No statement dispute or node fault was found.

### Edge cases

- n=0 or m=0: `Fin 0` is empty, the corresponding polynomial ring has no variables and
  the corresponding function module is the zero module. No positivity assumption occurs.
- g=0 or nilpotent: S_g is the zero ring and both sides are zero modules. No nonzero or
  non-zero-divisor assumption occurs.
- g is a unit (including g=1): localization identifies with S; this is the stable
  conormal comparison for two presentations of the same algebra.
- R or S is the zero ring: `CommRing` permits it. There is no nontriviality hypothesis.
- Arbitrary characteristics and independent universes u,v are allowed; no field,
  Noetherian, finite-presentation, or smoothness hypothesis is added.

### Searches

The real remote searches and service responses are recorded in `searches.jsonl`:

- leanfinder: `conormal modules of polynomial presentations of an algebra and its principal localization are stably isomorphic`. 8 hits; Algebra.Generators.cotangentCompLocalizationAwayEquiv, Algebra.Generators.snd_cotangentCompLocalizationAwayEquiv, Algebra.Generators.snd_comp_cotangentCompLocalizationAwayEquiv, Algebra.instFreeCotangentToExtensionUnitLocalizationAway, Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_inr, Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_inl, Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_comp_inl, Algebra.SubmersivePresentation.cotangentEquiv.

- loogle: `Algebra.Extension.Cotangent, LinearEquiv`. 12 hits; Algebra.Extension.cotangentEquivCotangentKer, Algebra.Extension.cotangentEquivCotangentKer_apply, Algebra.Extension.cotangentEquiv, Algebra.Extension.cotangentEquivCotangentKer_symm_apply, Algebra.Extension.contangentEquiv_tmul, Algebra.Extension.cotangentEquiv_tmul, Algebra.Extension.H1Cotangent.equiv_apply, Algebra.Generators.H1Cotangent.equiv_apply.

- leansearch: `conormal modules I/I² of two polynomial presentations of an algebra and its localization are stably isomorphic`. 0 hits; service unavailable: Internal Server Error.

- grep: `stacks 00S6|cotangent.*(prod|stable)|conormal.*local`. 6 hits; Mathlib/RingTheory/Extension/Cotangent/Basis.lean, Mathlib/RingTheory/Extension/Cotangent/Basis.lean, Mathlib/RingTheory/Extension/Cotangent/Basis.lean, Mathlib/RingTheory/Extension/Cotangent/Basis.lean, Mathlib/RingTheory/Extension/Cotangent/Basis.lean, Mathlib/RingTheory/Kaehler/JacobiZariski.lean.

LeanFinder's localization equivalence is for the specific composite presentation formed
by adjoining an inverse, not arbitrary β. Read its full signature/docstring at
`Mathlib/RingTheory/Extension/Cotangent/LocalizationAway.lean:190–204`.
The grep hit `cotangentEquivProd` is likewise for a constructed presentation, with an
additional nontriviality assumption. Read its signature/docstring at
`Mathlib/RingTheory/Extension/Cotangent/Basis.lean:214–221`.
Loogle hits compare a conormal object with its underlying synonym, tensor description,
or compare first homology; none give this stable comparison of arbitrary presentations.
LeanSearch returned Internal Server Error; no mathematical verdict is inferred from it.

Direct rg searches for the item id, `conormal.*local`, and `cotangent.*[Pp]rod` in
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing
statement. Broader conormal/Cotangent searches found only unrelated Hopf-algebra and
local-ring results. No duplicate definition has been introduced.

### Validation

Server compilation via `scompile.py H1 lem-weil-pbc-conormal-module-principal-localization`
completed cleanly (exit code 0, 1.5 seconds), with no warnings. All universes and variables
are explicit. The final delivery dry run is run after writing this report.


## Second reading by H1

I independently read the item node and all three statement-dependency nodes,
their recorded Mathlib declarations, and the delivered Lean file. I obtained the
primary Stacks TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex into
this item's scratchpad, and read the section opening at lines 35115–35206 and
`lemma-conormal-module-localize` at lines 35775–35798. The source's presentation
means a surjective algebra homomorphism. Its finite-type assumption follows from
α being a surjection from a polynomial ring on `Fin n`; there is no independent
Noetherian, nontriviality, or finite-presentation assumption. The same statement
is available at https://stacks.math.columbia.edu/tag/00S6.

My object/hypothesis/conclusion checklist, matched with Lean:

1. Arbitrary commutative ring R: `{R : Type u} [CommRing R]`. Exact.
2. Commutative R-algebra S, with its specified structure map R → S:
   `{S : Type v} [CommRing S] [Algebra R S]`. Exact; independent universes.
3. Element g of S: `(g : S)`. Exact; no invertibility or regularity required.
4. S_g, the ring of fractions at the powers of g:
   `Localization.Away g`. Exact instance of `def-weil-ring-localization-away`:
   the recorded abbreviation is `Localization (Submonoid.powers g)` in
   `Mathlib.GroupTheory.MonoidLocalization.Away`. Read also `IsLocalization.Away`
   in `Mathlib.RingTheory.Localization.Away.Basic`. The R-algebra on this ring
   is the canonical composite R → S → S_g. The node names the localization,
   rather than quantifying over an additional unrelated ring structure, so this
   canonical model loses no case.
5. Nonnegative integers n,m: `(n m : ℕ)`. Exact, including zero.
6. Polynomial rings over R with n and m variables:
   `MvPolynomial (Fin n) R`, `MvPolynomial (Fin m) R`. Exact relabelling of the
   node's finite variable sets. Read the dependency's `MvPolynomial` definition
   in `Mathlib.Algebra.MvPolynomial.Basic` (finitely supported monomial sums),
   `MvPolynomial.algHom_ext` there, and `MvPolynomial.aeval` in the Eval module.
7. Surjective R-algebra maps α and β with the stated targets:
   `(α : MvPolynomial (Fin n) R →ₐ[R] S)` and
   `(β : MvPolynomial (Fin m) R →ₐ[R] Localization.Away g)`, with
   `hα : Function.Surjective α`, `hβ : Function.Surjective β`. Exact, and both
   presentations remain arbitrary, in the node's quantifier order.
8. I=ker α, J=ker β and their quotients I/I², J/J²:
   `(ofSurjective α hα).Cotangent`, `(ofSurjective β hβ).Cotangent`. Exact.
   Read `Algebra.Extension.ofSurjective` at Extension/Basic.lean:102: it sets
   its source ring to the polynomial ring and its algebra₂ to `f.toAlgebra`.
   Thus its kernel is precisely the input map's kernel, not another presentation.
   Read `Extension.Cotangent` at :330 and `Ideal.Cotangent` in
   RingTheory/Ideal/Cotangent.lean:42: this is the quotient of I by the submodule
   I • top, i.e. I², carried through a type synonym.
9. The first quotient is an S-module and the second an S_g-module:
   `Algebra.Extension.Cotangent.module` supplies these exact structures.
   Read its signature and action at Extension/Basic.lean:368 and
   `Cotangent.val_smul`: a scalar acts through a lift in the source ring;
   the kernel annihilates the quotient. These are the natural quotient actions,
   so the node's module-structure clauses are present in the types rather than
   replaced by existential assertions about arbitrary actions.
10. Localization of the S-module I/I² at g:
    `LocalizedModule.Away g (ofSurjective α hα).Cotangent`. Exact use of
    `def-weil-pbc-module-localization-away`. Read its recorded abbreviation at
    LocalizedModule/Basic.lean:1475, `LocalizedModule.mkLinearMap`, and
    `IsLocalizedModule.lift` at :928. Read `moduleOfIsLocalization` at :374:
    its scalar ring is S_g with the fraction action, as required here.
    The dependency's additional canonical maps to localization at fg are
    not a clause of this item's statement and need not appear in the signature.
11. Free summands S_g^{⊕m} and S_g^{⊕n}:
    `(Fin m → Localization.Away g)` and `(Fin n → Localization.Away g)`.
    Exact: for finite sets the function module equals the finite direct sum.
    The binary module product `×` is the binary direct sum, with componentwise
    operations and scalar action.
12. Existence of an S_g-linear isomorphism, left localized I quotient plus
    rank m, right J quotient plus rank n:
    `Nonempty ((LocalizedModule.Away g (ofSurjective α hα).Cotangent ×
    (Fin m → Localization.Away g)) ≃ₗ[Localization.Away g]
    ((ofSurjective β hβ).Cotangent × (Fin n → Localization.Away g)))`.
    Exact; ranks and direction checked independently. No canonical isomorphism,
    compatibility condition, freeness of a quotient, or weaker stable relation
    has been substituted for the node's conclusion.

Edge cases: `Fin 0` allows either or both variable sets to be empty and gives
zero free summands. `CommRing` includes zero rings. g=0 and nilpotent g are
allowed (the localized ring and both modules are zero); g=1 or any unit is
allowed and gives comparison over S itself. All characteristics and unrelated
universe levels u,v are permitted. No scheme occurs in this ring statement, so
the empty-scheme case introduces no additional restriction. No unbound universe
or variable is present.

Independent searches, with different wording from the worker's queries, were
run through msearch.py and recorded in searches.jsonl:

- LeanFinder: `Schanuel stable isomorphism of relation modules for two finite
  polynomial algebra presentations after localization`: eight hits, concerning
  finite-presentation descent, constructed presentations, and freeness of a
  cotangent module. None states this arbitrary-presentation comparison.
- Loogle: `Algebra.Extension.Cotangent, Prod`: six hits, all the constructed
  `Algebra.Generators.cotangentCompLocalizationAwayEquiv` and its component
  formulas. I opened LocalizationAway.lean:190–204: its source is the composite
  presentation obtained by adjoining an inverse, not arbitrary β.
- LeanSearch: `Schanuel lemma for conormal relation modules of two polynomial
  presentations of a ring algebra`: service returned Internal Server Error.
  This is recorded as unavailable, not evidence of absence.
- msearch grep in Mathlib/RingTheory:
  `00S[56]|schanuel|conormal.*stabl|cotangent.*stabl`: no hits.
- Independent rg over Mathlib/RingTheory, WeilConjectures, and lean/Sheaf used
  `00S[56]|schanuel|conormal.{0,80}(local|stabl)|cotangent.{0,60}(prod|stabl)`.
  The relevant results were the constructed `cotangentEquivProd` and its basis
  formulas, plus a Jacobi–Zariski basis product. I opened Basis.lean:214–221:
  this equivalence concerns a constructed presentation and additionally assumes
  `Nontrivial S`; it cannot replace the item. Searches for the proposed name
  and item id in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json
  found no existing declaration. No duplicate notion is defined by this module.

No new definition node or dependency module is delivered, and no statement
correction is present or needed. All dependencies supply the notions used.
No H3–H9 mismatch was found. The module docstring and theorem docstring cite
00S6 and the blueprint id; the theorem docstring follows all six node proof
steps, including the two explicit composition homotopies and the final
crossed direct sum. There is one theorem with proof `sorry` and no definitions
or other proofs. The node's lean.statement was checked byte for byte against
the signature before `:=`; all module lines satisfy the 100-character bound.
The Lean and node were left unchanged; only this independent report was added.

Validation: my fresh server compilation through scompile.py exited 0 in 1.4 s,
with no errors or warnings. Delivery preflight and final server compilation
are run by deliver2.py after this report is written.
