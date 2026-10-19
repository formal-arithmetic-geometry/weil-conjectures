## Worker report

The module `Sheaf.RingTheory.GenericFiniteModulePresentation` states
`Module.Finite.exists_finitePresentation_localizedModule_powers`, with `sorry` as its entire
proof. No definitions or auxiliary theorems are added. The node is unchanged except for
its `lean` record. The module docstring cites Tag 051T; the theorem docstring gives all
seven proof steps of the node, including denominator clearing, the torsion-kernel argument,
and reduction of relation columns through the polynomial-algebra quotient.

Hypothesis and clause correspondence:

- A commutative integral domain R is `(R : Type u) [CommRing R] [IsDomain R]`.
- A commutative R-algebra B is `(B : Type v) [CommRing B] [Algebra R B]`.
- Finite type over R is `[Algebra.FiniteType R B]`, the exact recorded dependency notion.
- A B-module M is `(M : Type w) [AddCommGroup M] [Module B M]`.
- Finitely many generators is `[Module.Finite B M]`, meaning the top submodule is FG.
- Existence of a nonzero base element is `∃ a : R, a ≠ 0 ∧ ...`; a is in R, not in B.
- B_a is `Localization.Away (algebraMap R B a)`, inverting the image of a in B.
- M_a is `LocalizedModule.Away (algebraMap R B a) M`, with Mathlib's canonical module
  structure over that same localization of B. It needs no separately supplied R-action.
- The fractions and equality criterion are supplied by the actual Mathlib construction,
  rather than an abstract unknown module. `LocalizedModule.Away` is localization at powers;
  `LocalizedModule.mk_eq` says equality of m/s and m'/s' is equivalent to existence of
  u in that submonoid with u • s' • m = u • s • m'. For s = a^n and s' = a^k this is
  exactly the stated annihilation criterion, with a acting through `algebraMap R B`.
- Finite presentation over B_a is
  `Module.FinitePresentation (Localization.Away (algebraMap R B a))
    (LocalizedModule.Away (algebraMap R B a) M)`.
  This class is finite generators with finitely generated kernel. Its exact-sequence
  formulation is `Module.FinitePresentation.exists_fin'` in the same Mathlib module:
  natural n,m, maps B_a^n → M_a and B_a^m → B_a^n, surjectivity of the former and
  `Function.Exact` of the pair. Conversely finite generators of that kernel from the
  columns of such a sequence give the defining class. Thus this is exactly the node's
  finite integers u,v and right exact sequence, including zero ranks.
- There is no Noetherian hypothesis and no finite-presentation assumption on B or M.
  Independent universes u,v,w allow arbitrary base ring, algebra and module sizes.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType` in
  `Mathlib.RingTheory.FiniteType`, class with `out : (⊤ : Subalgebra R B).FG`.
  Its docstring is finite generation as an algebra. This is the recorded declaration.
- `def-weil-ring-localization-away`: `Localization.Away` in
  `Mathlib.GroupTheory.MonoidLocalization.Away`, abbreviation for
  `Localization (Submonoid.powers x)`. Its docstring specifies the quotient localization.
  Imported publicly as recorded; ring instances come from the localized-module imports.
- Other standard notions already carried by DAG nodes are used directly from Mathlib:
  `Module.Finite` (`Mathlib.RingTheory.Finiteness.Defs`,
  `def-weil-finitely-generated-module`), `LocalizedModule.Away`
  (`Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `def-weil-pbc-module-localization-away`), and `Module.FinitePresentation`
  (`Mathlib.Algebra.Module.FinitePresentation`, `def-sc-finitely-presented-module`).
  Their full defining signatures and docstrings were read, as were `mk_eq` and
  `Module.FinitePresentation.exists_fin'`.
- Stated proof dependencies use `Algebra.FiniteType.isNoetherianRing` from
  `Mathlib.RingTheory.FiniteType` and `Submodule.FG.of_le` from
  `Mathlib.RingTheory.Noetherian.Basic`. The latter module has a proof-only import.
- `lem-pur-fp-algebra-module-generic-freeness` has no Lean or Mathlib record in the
  supplied DAG snapshot; no import is possible yet. Its place in the proof is explicitly
  retained in the theorem docstring. It is not needed to elaborate the statement.

Source check: read the local `literature/stacks-project/algebra.tex`,
`lemma-generic-flatness`, lines 28564–28626, and
https://stacks.math.columbia.edu/tag/051T . The node is precisely the module part of
conclusion (b), with the same three hypotheses. No correction or dispute is needed.

Edge cases checked: B may be the zero ring (no `Nontrivial B` or `IsDomain B`);
then M is zero and the conclusion holds. M may itself be zero; the empty presentation
is allowed. The image of the nonzero a in B may be zero or nilpotent, producing zero
localizations, which are permitted. A zero generic fibre is allowed. R may be a field
or a non-Noetherian domain. No rank is required positive and no generic fibre is
required nonzero. These cases agree with the node and with its proof.

Searches performed using msearch.py with this group and item:

- LeanFinder: "A finite module over a finite type algebra over an integral domain becomes
  finitely presented after inverting a nonzero base element". Eight hits, including
  `Module.FinitePresentation.of_finite_of_finitePresentation`,
  `Module.FinitePresentation.iff_finitePresentation_of_finite`,
  `Algebra.FinitePresentation.of_span_eq_top_target`,
  `Algebra.FinitePresentation.of_finitePresentation`,
  `IsLocalization.Away.finitePresentation`,
  `Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway`,
  `Module.FinitePresentation.exists_fin`, and the auxiliary version of the span result.
  These convert algebra/module finite presentation or assume local presentations; none
  produces generic finite presentation for this finite module over an arbitrary domain.
- Loogle: `Module.FinitePresentation`. Twelve hits: the defining class, standard instances,
  the Noetherian and projective sufficient conditions, and transport/product/pi results.
  None states this generic localization theorem. Read the defining class and the finite
  free exact-sequence formulation in the pinned source.
- LeanSearch: "generic finite presentation of finite modules over finite type algebras
  over a domain". Service unavailable: Internal Server Error; no verdict from this search.
- msearch grep: `generic.*finitePresentation|exists.*finitePresentation.*powers`,
  Mathlib RingTheory subtree: zero hits.
- Local rg in the upstream `WeilConjectures` tree and `lean/Sheaf` for
  `generic.*(resentation|finite)|exists.*finitePresentation.*powers` and the item id:
  generic flatness, scheme-level generic finite presentation and unrelated generic
  finiteness results, no exact statement. In particular read
  `Sheaf.RingTheory.GenericFlatness`: it concludes flatness of an algebra over the base,
  not finite presentation of this arbitrary module. Read upstream
  `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`: finite-module generic
  freeness over a domain localizes at a target-ring element; generic flatness for a finite
  type algebra assumes the base is Noetherian and concludes flatness, not this statement.
- Local rg for `generic_finitePresentation|exists_finitePresentation_localizedModule_powers`
  in `dag/lean_names_upstream.json`, Mathlib, upstream and `lean/Sheaf`: no hits.
  Hence the new declaration name is available.

Validation: scompile.py compiled the delivered module cleanly on the server in 0.9 s,
nice 19, two threads, 60 s limit. Every universe and variable is explicitly bound.
The independent second reading is reserved for the next worker.

## Second reading by ND

I independently read the sandbox node, all seven proof steps, its two statement
 dependency nodes and their recorded declarations, the delivered Lean file, and
`algebra.tex`, lemma-generic-flatness (Tag 051T), including the preceding Tag 051S
lemma and the polynomial and general cases of the proof. The source assumes only
that R is a domain, B is a finite type R-algebra, and M is finite over B. The node
isolates the module clause of (b), not the source's additional freeness and algebra
finite-presentation conclusions. No source-wide Noetherian assumption applies.

Object, hypothesis and conclusion checklist (each verdict: exact):

1. A commutative integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`.
   The nontriviality inherent in IsDomain agrees with integral domain.
2. A commutative R-algebra B: `(B : Type v) [CommRing B] [Algebra R B]`.
   This packages precisely the ring map in the source; it does not assert that
   this map is injective or that B is nontrivial.
3. B is finite type over R: `[Algebra.FiniteType R B]`. I opened the recorded
   declaration in Mathlib.RingTheory.FiniteType: its field is finite generation
   of the top R-subalgebra. The same file's `iff_quotient_mvPolynomial''` gives
   the finite-polynomial-surjection formulation of the dependency node.
4. M is a B-module: `(M : Type w) [AddCommGroup M] [Module B M]`.
   No separate R-module instance or scalar tower is imposed: base elements act
   through the given algebra map, exactly as the fractions in the node require.
5. M has finitely many B-generators: `[Module.Finite B M]`. I read its field
   `fg_top : (⊤ : Submodule B M).FG`, which is the node's finite spanning family,
   not finiteness of the underlying set.
6. There exists a nonzero base element: `∃ a : R, a ≠ 0 ∧ ...`.
   It depends on all the given objects and structures; it lies in R, not B.
7. The coefficient ring after localization is
   `Localization.Away (algebraMap R B a)`. I opened Localization.Away in the
   recorded module: it is Localization at Submonoid.powers. Thus this is B[1/a],
   with no injectivity of R → B assumed.
8. The module is `LocalizedModule.Away (algebraMap R B a) M`. I read its
   abbreviation, the underlying OreLocalization quotient, and `mk_eq` in
   Mathlib.Algebra.Module.LocalizedModule.Basic. For denominators a^n and a^k,
   the latter gives existence of a power a^j with
   a^j • (a^k • m - a^n • m') = 0. Its canonical localization-module scalar
   structure is over the very B_a used in clause 7. This is the node's actual
   module of fractions and equality criterion, including torsion.
9. The conclusion `Module.FinitePresentation B_a M_a` is exact. I read the
   class (finite generators and finitely generated kernel), `exists_fin`, and
   `exists_fin'` in Mathlib.Algebra.Module.FinitePresentation. The last gives
   natural numbers n,m, linear maps B_a^m → B_a^n → M_a, surjectivity of the
   second and Function.Exact of the pair. Conversely such a right exact pair
   gives a finitely generated kernel via the images of the finite basis. Thus
   the class expresses exactly the displayed sequence in the node; it imposes
   no positivity on either rank.
10. The explicit absence of Noetherian or finite-presentation hypotheses on B
    or M is respected. All binders have been accounted for above. The only
    finiteness assumptions are Algebra.FiniteType R B and Module.Finite B M.

Edge cases: M = 0, empty generator or relation families, n = 0 polynomial
presentations, B = 0, zero generic fibre, and a zero or nilpotent image of a in B
are all allowed. Zero localization rings and modules are permitted. The base
itself is nonzero by the node's domain hypothesis. Fields and domains of arbitrary
characteristic, including non-Noetherian domains, are included. The independent
universes u,v,w impose no relative size restriction. There is no scheme or scheme
nonemptiness hypothesis in this algebraic item.

Dependency and construction review: the two actual stmt_deps use the correct
recorded declarations, not similarly named alternatives. I also read the DAG
records for module localization, finite generation and finite presentation; the
standard Mathlib constructions above implement them without a private copy.
There are no new nodes, definition bodies, or dependency modules to review.
The proof-only import Mathlib.RingTheory.Noetherian.Basic supplies the recorded
`Submodule.FG.of_le`; I read its signature and that of
`Algebra.FiniteType.isNoetherianRing`. The generic-freeness proof dependency has
no Lean declaration yet, so its omission from imports is justified and its use
is retained explicitly in proof step 5. The theorem docstring matches all seven
node steps: polynomial presentation, generic localization and exactness,
Noetherian relation generation, the torsion-kernel finite-presentation cover,
generic freeness and injectivity, localization of the finite presentation, and
reduction of relation columns to B_a. The only proof is `by sorry`; no statement
is proved, no data are postponed. Source and blueprint docstrings, namespace,
line widths, imports, and explicit universe/variable bindings satisfy H5–H9.

Independent searches with different queries:

- LeanFinder via msearch.py: “A finitely generated module over a finitely
  generated algebra over a domain has finite relations after localizing the
  base at one nonzero element”. Eight results, principally
  Module.Finite.of_localizationSpan variants, algebra finite-presentation
  locality, IsLocalization.Away.finitePresentation, and
  IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation.
  None states this generic existence theorem. I opened the last declaration:
  it assumes finite presentation of the localized target over the original
  ring, which is absent here.
- Loogle via msearch.py: `LocalizedModule, Module.FinitePresentation`.
  Twelve results: preservation of an existing finite presentation by
  localization, localization of Hom, lifting equivalences, and projectivity
  locality. They assume existing finite presentation and do not produce
  the finite presentation claimed by this item.
- Independent rg over pinned Mathlib, upstream WeilConjectures, project
  lean/Sheaf and dag/lean_names_upstream.json used
  `generic.{0,45}(present|relation)`,
  `exists.{0,25}finitePresentation.{0,35}(local|away|powers)` and
  `finitePresentation.{0,35}generic` (case insensitive). No exact duplicate.
  I opened GenericFlatFinitePresentation and GenericLocallyOfFinitePresentation:
  these concern schemes or finite presentation of the algebra, not an arbitrary
  finite module. I also inspected upstream Spectrum/Prime/FreeLocus and
  Mathlib.RingTheory.Localization.Free: finite-module freeness over a domain
  chooses an element of that domain, whereas B is not assumed a domain here;
  the finite-type-algebra generic-flatness theorem assumes a Noetherian base;
  Mathlib's freeness spreading theorem assumes the original module already
  finitely presented. None is an exact existing declaration for this node.

No mismatch was found. I changed only this report by adding the independent
second reading; the correct Lean signature and node fields remain unchanged.
The node lean.statement is verbatim equal to the file's signature, excluding
`:= by`. No statement_change exists or is needed, so citer correction review
does not apply. Validation uses the required scompile.py server compilation
with nice 19, two threads and a 60-second per-file limit, followed by the delivery
script's dry run and actual delivery.
