## Worker report

The module `Sheaf.TraceFormula.ValuationFiniteTypeModulePresentation` states
`Algebra.valuation_finite_type_module_presentation`, the statement of Stacks
Project More on Algebra, Tag 053E (2), lines 5966--6001.

The Lean binders render the node clause by clause. `A : Type u` and the
instances `[CommRing A] [IsDomain A] [ValuationRing A]` are the valuation ring.
`B : Type v`, `[CommRing B]`, and `[Algebra A B]` give the A-algebra B, while
`hAB : RingHom.FiniteType (algebraMap A B)` is the finite-type ring map.
`M : Type w`, `[AddCommGroup M]`, `[Module B M]`, and
`[Module.Finite B M]` give a finite B-module.  `[Module A M]` and
`[IsScalarTower A B M]` express the canonical restriction of the B-action to
A, and `[Module.Flat A M]` is flatness over A.  The conclusion
`Module.FinitePresentation B M` is finite presentation over B.

The statement uses the recorded dependency declarations:

* `ValuationRing` from `Mathlib.RingTheory.Valuation.ValuationRing`;
* `RingHom.FiniteType` from `Mathlib.RingTheory.FiniteType`;
* `Module.Finite` from `Mathlib.RingTheory.Finiteness.Defs` (available through
  the imported Mathlib modules);
* `Module.Flat`/`RingHom.Flat` from `Mathlib.RingTheory.RingHom.Flat`;
* `Module.FinitePresentation` from
  `Mathlib.Algebra.Module.FinitePresentation`.

The edge cases are retained: the finite-type witness may use zero generators,
`M` may be the zero module, and no nonzero or positive-rank assumption is made.
The valuation-ring class takes `[IsDomain A]` as a parameter; this explicit
instance records the integral-domain condition of the node's valuation ring.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: “A finite module over a finite type algebra over a valuation ring
  that is flat over the valuation ring is finitely presented”. Eight hits,
  including `Module.FinitePresentation.of_finite_of_finitePresentation` and
  `Module.finitePresentation_of_finite`; none has the valuation-ring hypotheses.
  The former concerns an algebra finite as a module; the latter requires
  Noetherianity, which is not assumed here.
- Loogle: `ValuationRing, Module.FinitePresentation`. Zero hits.
- Mathlib grep in `RingTheory`:
  `valuation.*presentation|presentation.*valuation|053E|053C`. Zero hits.
- LeanSearch: “finite module over finite type valuation ring flat finitely
  presented”. Eight hits, including the Noetherian finite-presentation theorem,
  the flat finitely presented projectivity theorem, and finite-flat freeness over
  a local ring; no exact match.
- `rg` in `WeilConjectures/` and `lean/Sheaf/` for `ValuationRing`,
  `RingHom.FiniteType`, `Module.FinitePresentation`, and valuation/presentation
  name combinations found generic definitions and different valuation-ring
  results (closed-fibre Noetherianity and module injectivity), not this statement.
  Searching the item's id in `WeilConjectures/`, and the chosen declaration name
  in Mathlib and `dag/lean_names_upstream.json`, found no match.

The source Tag 053E(2) was read directly in `more-algebra.tex`; it agrees exactly
with the node. `ValuationRing.TFAE` supplies the equivalence with the node's
fraction-field characterization. All three universes are independent. The
zero ring is excluded only for A, as required by the valuation-domain
hypothesis; B can be the zero ring. A field A and the identity algebra B=A
are included. No theorem or definition was duplicated; no statement correction,
new node, or dependency-interface repair was necessary.

Proof-only imports include `Mathlib.Algebra.MvPolynomial.Basic` (polynomial
ring) and `Mathlib.RingTheory.Flat.TorsionFree` (both torsion-free steps).
`lem-trf-local-graded-flat-module-finite-presentation` and
`lem-trf-finitely-presented-over-subring` have no recorded Lean module in the
read checkout, so their imports cannot yet be added; their roles are retained
explicitly in the seven-step proof docstring. They are proof prerequisites,
not missing notions in the present statement.

The module compiled cleanly through `scompile.py`: both the sandbox check and
library-path check completed with no warnings or errors. The single theorem
proof is `sorry`; there are no definitions with postponed data.

## Second reading by Q27

Independent maintainer reading, 2026-10-18, of immutable delivery
`db8c5cab9734f78773700ff4d3c5f024472313f9`. The reviewer did not author this
delivery. Read the item, all five statement-dependency records, their exact
Mathlib declarations and docstrings, the delivered module, and the source.

Clause-by-clause comparison with Stacks `more-algebra.tex:5966–6001`,
Tag 053E(2), `lemma-flat-finite-type-valuation-ring-finite-presentation`:

- The valuation domain is `(A : Type u) [CommRing A] [IsDomain A]
  [ValuationRing A]`. `ValuationRing` at `ValuationRing.lean:64` takes the
  domain instance as a parameter and extends total divisibility;
  `ValuationRing.TFAE` at line 407 identifies this with the fraction-field
  condition in `def-trf-valuation-ring`. The explicit domain instance adds
  no hypothesis beyond that definition. Fields are included.
- The arbitrary finite-type ring map is represented by `(B : Type v)
  [CommRing B] [Algebra A B]` and
  `hAB : RingHom.FiniteType (algebraMap A B)`.
  `RingHom.FiniteType` at `FiniteType.lean:217` is finite generation for
  the induced algebra; `finiteType_algebraMap` and
  `Algebra.FiniteType.iff_quotient_mvPolynomial''` give precisely the
  dependency's polynomial-surjection definition. Any ring map supplies
  this algebra structure; no injectivity or flatness of B is imposed.
- `(M : Type w) [AddCommGroup M] [Module B M] [Module.Finite B M]`
  means a finitely generated B-module, using `Module.Finite` at
  `Finiteness/Defs.lean:117–119`, not finiteness of its underlying set.
- `[Module A M] [IsScalarTower A B M]` specify restriction of scalars:
  applying scalar associativity to `a`, `1 : B`, and `m` gives
  `a • m = (algebraMap A B a) • m`. Thus `[Module.Flat A M]` is exactly
  the source's flatness hypothesis. `Flat/Basic.lean:113–115` and
  `iff_lTensor_preserves_injective_linearMap` at line 316 identify the
  class with the dependency's tensor-injectivity condition. The recorded
  `RingHom.Flat` module imports this same class; no private notion is used.
- The sole conclusion is `Module.FinitePresentation B M`.
  `Algebra/Module/FinitePresentation.lean:67–69` requires a finite
  generating set and finitely generated kernel, precisely the finite-free
  exact-sequence definition in `def-sc-finitely-presented-module`.

Source definitions also read: `algebra.tex:350–365` (0518), `517–530`
(00F3), `8620–8641` (00HB), `11729–11745` (00I9), and `11800–11830`
(00IB and its converse). No source-wide extra hypotheses occur here.

All seven proof steps occur in the theorem docstring. Step 1 obtains
locality from total divisibility and chooses finite generators. Step 2's
filtered polynomial module is internally graded and generated by the
specified degree-zero generators. Step 3 applies the flat/torsion-free
statements; the actual Mathlib declarations `Module.Flat.torsion_eq_bot`,
`Submodule.isTorsionFree_iff_torsion_eq_bot`, and
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, together with the
valuation-ring Bezout instance, were read. Step 4 uses exactly the local,
positive-weight, finite and flat hypotheses of the Tag 053C dependency
(`more-algebra.tex:5856–5909`). In Step 5 the partial-sum coefficients
belong to the required filtration terms; multiplication by t−1 gives
all the original coefficients, including the last using their zero sum.
Step 6's finite relations survive evaluation at X₀=1. Step 7 uses
surjectivity of Q→B to get finite type and then precisely Tag 0561
(`algebra.tex:584–610`). Its restriction action is the given one.
The two proof prerequisites without Lean declarations are not objects
needed to type this statement, so no missing-helper construction or
statement-dependency repair is needed at stage 2.

Edge cases checked: M=0, B the zero ring (hence M=0), A a field,
B=A, zero algebra generators, zero module generators, and degree D=0
in the kernel computation. A=0 is correctly excluded by valuation-domain
status. There is no characteristic, rank, Noetherian, or flat-B assumption.
Universes u, v, w are independent and explicitly bound; autoImplicit is
false. The additional A-action is determined by the scalar tower.

Independent duplicate searches: Loogle `ValuationRing,
Module.FinitePresentation` returned zero hits; LeanSearch `finite flat
module over a finite type algebra over a valuation ring is finitely
presented` returned eight general finite-presentation results, none exact.
Text searches in Mathlib, upstream WeilConjectures, the group's lean/Sheaf,
and dag/lean_names_upstream.json found no duplicate. The nearby local,
essentially-finite-type theorem is a different statement. The worker's
report records the other search modes. Existing dependency notions are
all reused. No new definition or dependency module is delivered.

Mechanical checks: all three delivered files equal the immutable commit;
only the item's lean field changed relative to its parent. Its
lean.statement equals the theorem signature verbatim. Both source and
blueprint docstrings are present, every Lean line is at most 100
characters, and the only proof is `by sorry`. There is no definition,
arbitrary construction, hidden proof, local notation, or pro-etale
substitute. No direct statement/proof dependency is on the current route
pivot drop list; no item repair note exists there. The proof is ordinary
commutative algebra and introduces none of the dropped machinery.

Compiler reproduction: ran the prescribed scompile.py on the exact immutable
snapshot module. Exit code 0; both `Sheaf/Stage2/Sandbox0.lean` and library
`Sheaf/TraceFormula/ValuationFiniteTypeModulePresentation.lean` passed with
empty Lean diagnostic output (no errors or warnings). Reported wrapper
wall times were 187.7 s and 128.5 s, including slot acquisition; the usual
60-second Lean limit after acquisition was retained. The installed
2026-10-17 wrapper delegates these overlay checks to the server; it was
used unchanged. No direct SSH, live Lean write or global build was run.

Finding and change: H11 (also the real-section requirement of H1): the
original second-reading section explicitly said no independent reading
was performed. Replaced that placeholder with this actual independent
reading. Clarified the worker's description of the IsDomain parameter.
The Lean module and node record require no change. No mathematical,
universe, or dependency-interface defect was found.
