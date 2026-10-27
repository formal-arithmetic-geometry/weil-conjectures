## Worker report

Stage 2, Q103, 2026-10-22. The module
`Sheaf.CategoryTheory.CoefficientCounitMateCocycle` states the two clauses of
`lem-coef-dualizing-quotient-mates` as
`CategoryTheory.Adjunction.coefficientCounitMate_cocycle` and
`CategoryTheory.Adjunction.coefficientCounitMate_identity`. Both proofs are `sorry`.
There are no definitions, helper axioms, new nodes, dependency repairs, or statement
corrections. Only the item's `lean` field changes. The earlier Q88 work was the
stage-1 split, not a Lean statement; this delivery preserves that split verbatim.
There was no retained module or node in this sandbox, only dispatcher brief files.
There is no repair note for this item in the read repository.

Source read: blueprint main-20261015,
`sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md`, paragraph 3,
the sentence “The same adjoint calculation proves the quotient cocycle and
compatibility with the counit.” I read the complete item, including the four
expanded proof steps, and Q88's stage-1 report. No source or statement fault was found.

The mates are written out using `Adjunction.homEquiv`; hence no new notion or
arbitrary map parameter replaces the canonical counit mate. In Lean composition
`f ≫ g` means first f, then g. The inverse comparison is therefore the first
factor in each adjunct.

The hypothesis and clause correspondence for the cocycle theorem is:

| Node | Lean |
| --- | --- |
| The six arbitrary categories | `CA`, `DA`, `CB`, `DB`, `CC`, `DC`, each with its own object universe and morphism universe |
| The three functor pairs and chosen adjunctions, with their actual counits | `FA`, `GA`, `FB`, `GB`, `FC`, `GC`, and `aA : FA ⊣ GA`, `aB : FB ⊣ GB`, `aC : FC ⊣ GC`; their fields `aA.counit`, etc. |
| Coefficient functors AB, BC, AC on both families | `tcAB`, `tdAB`, `tcBC`, `tdBC`, `tcAC`, `tdAC` |
| Associators from iterated to direct coefficients | `assocC : tcAB ⋙ tcBC ≅ tcAC` and `assocD : tdAB ⋙ tdBC ≅ tdAC` |
| Objects N_A, N_B, N_C | `NA`, `NB`, `NC` |
| The coherent specified identifications T_RS N_R ≅ N_S | `nAB`, `nBC`, `nAC`, with `hN : tdBC.map nAB.hom ≫ nBC.hom = assocD.hom.app NA ≫ nAC.hom` |
| Natural transformations T_RS F_R → F_S T_RS | `cAB : FA ⋙ tdAB ⟶ tcAB ⋙ FB`, and likewise `cBC`, `cAC` |
| Comparison cocycle only at G_A N_A | `hc`, evaluated only at `GA.obj NA`; its two paths begin at `tdBC.obj (tdAB.obj (FA.obj (GA.obj NA)))` and end at `FC.obj (tcAC.obj (GA.obj NA))` |
| The four listed invertible components | Precisely the four `IsIso` binders after `hc`: AB and AC at `GA.obj NA`, BC at `GB.obj NB`, and BC at `tcAB.obj (GA.obj NA)` |
| Definition of v_AB | `(aB.homEquiv (tcAB.obj (GA.obj NA)) NB) (inv (cAB.app (GA.obj NA)) ≫ tdAB.map (aA.counit.app NA) ≫ nAB.hom)` |
| Definition of v_BC and v_AC | The same displayed formula with `aC.homEquiv`, the respective component inverse, transported counit, and `nBC.hom` or `nAC.hom` |
| v_AC = v_BC composed with T_BC(v_AB), under associators | The theorem equality has v_AC on its left; its right side is `assocC.inv.app (GA.obj NA) ≫ tcBC.map vAB ≫ vBC` |
| Global equality in the Hom set, without invertibility of v | Ordinary equality of morphisms; no mate has an `IsIso` binder and no further test map is composed with either side |

The identity clause has its own theorem, so it is valid for each of A, B, C
without demanding irrelevant triple data:

| Node | Lean |
| --- | --- |
| An arbitrary one of the original adjunctions | `a : F ⊣ G`, with arbitrary C and D and independent object and morphism universes |
| Identity coefficient functors with their unit identifications | `tc`, `td`, with `uC : tc ≅ 𝟭 C`, `uD : td ≅ 𝟭 D` |
| Coherent identity identification T_RR N_R ≅ N_R | `N`, `n : td.obj N ≅ N`, `hN : n.hom = uD.hom.app N` |
| Identity coefficient comparison natural transformation | `c : F ⋙ td ⟶ tc ⋙ F` |
| Its component at G_R N_R is the unit comparison | `hc : c.app (G.obj N) = uD.hom.app (F.obj (G.obj N)) ≫ F.map (uC.inv.app (G.obj N))` |
| The canonically inverted comparison | Explicit `@inv` uses `hc.symm ▸ inferInstance`; the instance is transported from the stated composite of unit isomorphisms. This introduces no invertibility assumption. |
| The same counit-adjunct definition of v_RR | `a.homEquiv` applied to that inverse, then `td.map (a.counit.app N)`, then `n.hom` |
| v_RR = 1 with unit identifications understood | The equality to `uC.hom.app (G.obj N)`. For literal identity coefficient functors and unit isomorphisms it is equality to `𝟙 (G.obj N)`. |

The two explicit commuting path equations express the node's phrase “under
these associators” and the coherence of the chosen N identifications. Only the
triple and identity coherence involved in the two asserted equations is needed;
there is no assumed natural inverse of c, no global c cocycle hypothesis, and no
identification of different category universes. The node's identity coefficient
condition belongs to the identity theorem; the cocycle theorem does not use it.

Dependencies read and used:

- `def-weil-pbc-composite-adjunction` is Mathlib, with no `lean` record. Its
  `mathlib_match` is `CategoryTheory.Adjunction.comp`, including `comp_homEquiv`,
  `comp_unit_app`, `comp_counit_app`, and `Adjunction.id` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. I read their signatures, docstrings,
  and definitions. This module supplies the actual `Adjunction` structure used
  in the three binders, including the specified counits. There is no private
  definition of adjunction.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is also Mathlib:
  `CategoryTheory.Adjunction.mkOfHomEquiv`, with `homEquiv_unit` and
  `homEquiv_counit`, in the same module. I read `homEquiv` and its explicit
  inverse `F.map g ≫ adj.counit.app Y`, and `mkOfHomEquiv`'s construction and
  `mkOfHomEquiv_homEquiv`. The one public import supplies both dependency nodes;
  no additional private proof import is needed.

The module and both theorem docstrings name the source and blueprint node.
The cocycle docstring spells out proof steps 1--3, including the actual
naturality square at v_AB and the associator/object bookkeeping. The identity
docstring spells out step 4. There is no proof or choice of new data in either
theorem. `autoImplicit` is disabled and every variable and universe is bound.

Edge cases checked before writing: coincident coefficient labels and identity
changes are allowed; the adjunction itself need not be the identity adjunction.
For identity unit isomorphisms the second theorem gives literally v_RR = 1.
Nontrivial unit isomorphisms yield precisely their component on G(N), as required
by “identifications understood.” The terminal category gives its unique map.
An empty D cannot supply N and so satisfies no instance of the hypotheses; an
empty C with nonempty D cannot supply G. Noninvertible mates are permitted:
none of their inverses occurs. The auxiliary fourth invertible component in the
cocycle is needed for naturality at the actual v_AB, whose source is
`tcAB.obj (GA.obj NA)` rather than `GB.obj NB`. Different object and morphism
universes for all six categories are retained.

Searches actually run with `msearch.py Q103 lem-coef-dualizing-quotient-mates`:

- LeanFinder: `Counit adjuncts of coefficient comparison maps invertible only at specified objects satisfy composition cocycle`.
  Eight hits on adjunction counit formulas and unrelated cochain material; none
  states this componentwise coefficient cocycle.
- Loogle: `CategoryTheory.mateEquiv`. Twelve hits, including `mateEquiv_vcomp`
  and `mateEquiv_hcomp`. I read Mates.lean's square types and the vertical
  composition theorem: they need complete natural squares in the reverse
  direction, which four invertible components do not provide.
- Grep: `mateEquiv_vcomp|mateEquiv_hcomp|homEquiv_counit` in
  `CategoryTheory/Adjunction`. Twenty-three hits, locating the same composition
  results and the Hom-bijection formulas in Basic.lean. These provide ingredients,
  not an existing statement of this node.
- LeanSearch: `Adjunction transpose composition for partially invertible natural comparison components`.
  Eight hits on adjunction composition and complete natural comparison
  transformations, with no match for the objectwise-inverse result.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the exact item id,
  `coefficientCounitMate`, `quotient.*mate`, and `mate.*cocycle` found no declaration
  for this node. I opened the generic private `mate_cocycle_at` in
  `Sheaf.Paper.ExceptionalCoefficientComparison`: it takes three full reverse
  `TwoSquare`s, not the forward natural transformations with only four component
  inverses of this node, and does not include the identity clause. The private
  `quotient_mate` in SupportSiteComparison compares different adjunction systems,
  so also is not a match. No existing notion was redefined.

Validation: the initial module compiled through prescribed `scompile.py` in both
its sandbox and library module forms (0.9 s and 1.2 s), with no diagnostics.
The final version additionally disables auto-bound implicits and is checked
again by the mandatory dry run. Maximum Lean line length is at most 100.
No `STATEMENT-DISPUTED` issue remains.

The mandatory `deliver2.py Q103 lem-coef-dualizing-quotient-mates --no-push`
completed successfully: `OK (dry run): commit 4493e73ea32 passes the preflight
and compiles; nothing pushed`. This check includes the final version with
`autoImplicit false`. It stages only this report, the item node and the module.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
