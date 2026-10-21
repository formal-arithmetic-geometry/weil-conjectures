## Worker report

The module `Sheaf.CategoryTheory.AdjunctionSquareShiftMate` states
`CategoryTheory.Adjunction.square_shift_mate`, with `sorry` as its sole proof.
No definitions or additional nodes are introduced. The node changes only in `lean`.

Sources read: Stacks `derived.tex`, Tag 0A8D, `lemma-adjoint-is-exact`, first proof
paragraph constructing the right adjoint shift comparison; `categories.tex`, Tag
0037, `definition-adjoint` and the following adjunct formulas. Also read the current
blueprint `main-20261015`, `lemma-weil-pbc-perfect-projection-formula.proof.md`,
first paragraph, closure under shifts. As the node explicitly records, its
four-category refinement and its two detailed adjunct equations are agent-written;
they are not claimed to be verbatim Stacks statements.

Hypotheses and objects, matched individually:

- The four categories are `C`, `D`, `C'`, `D'`, each with its own explicitly bound
  object universe and morphism universe. The four `HasShift _ ℤ` instances encode
  coherent integer shifts. No equality between any of these universes is imposed.
- `L`, `R`, `L'`, `R'` have exactly the stated domains and codomains;
  `adj : L ⊣ R` and `adj' : L' ⊣ R'` include units, counits, and triangle identities.
- `r : C ⥤ C'` and `t : D ⥤ D'` are arbitrary functors. Each of the six functors
  has its specified `Functor.CommShift ℤ` structure; this supplies natural shift
  isomorphisms and the zero/addition coherence. `H.commShiftIso n` has the node's
  orientation `H(X[n]) ≅ (HX)[n]`.
- `hunit` and `hunit'` require `CommShift.CompatibilityUnit` for every integer
  `n`. Its definition is precisely the respective displayed unit equation,
  written in Lean's forward composition order.
- `β : R ⋙ r ⟶ t ⋙ R'` is the node's natural transformation `rR → R't`.
  `hβ` spells out the node's equation for every `E : D` and `n : ℤ`:
  `β(E[n]) ≫ R'(e_E) ≫ b'_(tE) = r(b_E) ≫ c_(RE) ≫ β(E)[n]`.
- `P : C` and `n : ℤ` remain arbitrary. There is no triangulated or additive
  structure, adjoint of `r` or `t`, or invertibility assumption on `β` or its mate.

Every conclusion is included, as four conjuncts:

1. The first conjunct is `h_(P[n]) ≫ R'(d_P) ≫ b'_B = c_P ≫ h_P[n]`.
   Throughout the statement `h_P` is expanded literally as
   `r.map (adj.unit.app P) ≫ β.app (L.obj P)`. Here `B = t.obj (L.obj P)`;
   `d_P` is expanded as `t.map ((L.commShiftIso n).hom.app P) ≫
   (t.commShiftIso n).hom.app (L.obj P)`, the recorded composite convention.
2. The second conjunct applies `adj'.homEquiv (r.obj (P⟦n⟧)) (B⟦n⟧)` to
   `θ_(P[n]) ≫ d_P` and gives exactly `h_(P[n]) ≫ R'.map d_P`.
   Every occurrence of `θ_P` is expanded literally as
   `L'.map h_P ≫ adj'.counit.app B`, not an independently chosen mate.
3. The third conjunct applies that same hom equivalence to
   `L'.map c_P ≫ a'_(rP) ≫ θ_P[n]`; its value is exactly
   `c_P ≫ h_P[n] ≫ (R'.commShiftIso n).inv.app B`.
   Thus the inverse right comparison, rather than the forward comparison,
   occurs in the second adjunct formula, in the required order.
4. The last conjunct is the full mate shift equation
   `θ_(P[n]) ≫ d_P = L'.map c_P ≫ a'_(rP) ≫ θ_P[n]`.

Dependency declarations read and used:

- `lem-weil-pbc-adjunction-of-natural-bijection`: Mathlib module
  `Mathlib.CategoryTheory.Adjunction.Basic`, `Adjunction.mkOfHomEquiv`,
  `Adjunction.CoreHomEquiv`, `Adjunction.homEquiv`, `Adjunction.homEquiv_unit`,
  and `Adjunction.homEquiv_counit`. Its `mathlib_match` is the dependency record;
  the existing `Adjunction` and its hom equivalence are used directly.
- `lem-weil-pbc-commshift-nattrans-comp-whisker`: Mathlib module
  `Mathlib.CategoryTheory.Shift.CommShift`, `Functor.CommShift`, its composite
  instance and `Functor.commShiftIso_comp_hom_app`, and
  `NatTrans.CommShift.comp`, `.whiskerRight`, `.whiskerLeft`, `.associator`.
  The theorem uses the given coherent structures and writes their composite
  comparisons directly. These declarations describe the proof's composition
  convention; no private version of shift compatibility is defined.
- `lem-weil-pbc-adjunction-shift-compatibility-unique`: Mathlib module
  `Mathlib.CategoryTheory.Shift.Adjunction`,
  `Adjunction.CommShift.CompatibilityUnit`,
  `Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit`,
  `Adjunction.CommShift.compatibilityUnit_right`,
  `Adjunction.CommShift.compatibilityUnit_unique_right`, and
  `Adjunction.rightAdjointCommShift`. The statement uses `CompatibilityUnit`
  directly and the docstring records where unit-to-counit compatibility enters.

The public import of `Shift.Adjunction` includes all three dependency modules,
which are also all the proof dependencies. `Mathlib.Algebra.Group.Int.Defs`
supplies the integer additive group needed by `HasShift _ ℤ`.

Edge cases checked mathematically before writing: identity adjunctions and
identity comparison recover the ordinary shift square; `n = 0` gives the same
identities with the coherent zero comparison, without strictifying it; negative
integers use exactly the supplied shift isomorphisms. Empty categories cause no
nonempty assumption, since the component equations quantify over their objects.
A zero comparison in an additive example gives zero on both sides and is
allowed: no step cancels `β` or `θ`. Non-strict comparisons for `r,t` remain
explicit in every clause. The sources and the typing of the two hom equivalences
confirm their common source `L'(r(P[n]))` and target `B[n]`.

Searches for an existing declaration (2026-10-21):

- `msearch.py ... leanfinder`, query "A mate of a natural transformation in an
  adjunction square commutes with integer shift when the units and comparison
  commute with shift": 8 hits, including `Adjunction.CommShift.mk'`,
  `compatibilityCounit_of_compatibilityUnit`, `shift_unit_app_assoc` and
  `CompatibilityUnit`. None includes the two requested shifted adjunct formulas.
- `msearch.py ... loogle`, query `"mateEquiv", "shift"`: 0 hits.
- `msearch.py ... grep`, query
  `mate.*[Cc]ommShift|[Cc]ommShift.*mate|conjugate.*[Cc]ommShift|[Cc]ommShift.*conjugate`
  in Mathlib `CategoryTheory`: 0 hits.
- The same `rg` concept search in `lean/WeilConjectures` and `lean/Sheaf` found
  `WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction` and applications.
  Read its complete `NatTrans.CommShift.mateEquiv` signature: it transports
  compatibility from a left square to its right mate. It supplies neither the
  two component adjunct equations nor this node's conjunction of four formulas.
  Consequently it is not an exact match for this node.
- `grep -rn` for this node id in `lean/WeilConjectures`: no matches. `rg` for
  `square_shift_mate` across Mathlib, upstream, and `lean/Sheaf`: no matches.

No statement correction, missing dependency interface, or statement dispute was
found. The module contains no auto-bound variables, file-local notation,
instances, helper definitions, or proofs beyond the required `sorry`.

## Second reading by Q26

I reread the complete node and the finished signature against the above mapping.
This is a worker self-check, not an independent-agent review; the dispatcher
brief prohibits starting another agent and assigns independent review to the
maintainer. The first equation and the two hom-equivalence images all use the
same expanded `h_P`, and both occurrences of the shifted mate use exactly the
expanded counit formula. The four conjunctions retain all clauses. The six
coherent structures are independently specified, the two unit hypotheses range
over every integer, and `hβ` keeps both the `r` and `t` comparisons. There are no
extra invertibility, strictness, adjoint, or triangulated hypotheses. No
mathematical mismatch required a change. The initial compile identified the
missing integer additive-group import; adding `Mathlib.Algebra.Group.Int.Defs`
repairs that import without changing any mathematical statement.
