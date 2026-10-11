## Worker report

The module `Sheaf.RingTheory.CompleteLocalGRing` states
`isGRing_of_isNoetherianRing_of_isAdicComplete`, with only `sorry` as its proof.
It reproduces Stacks Proposition [07PS](https://stacks.math.columbia.edu/tag/07PS),
checked on the website because the local literature source is not present.
The declaration docstring carries the seven-step natural-language proof and its DAG inputs.

Hypothesis and clause correspondence:
- The commutative ring S is `(S : Type u) [CommRing S]`, with explicitly bound universe u.
- Noetherian is `[IsNoetherianRing S]`: every ideal is finitely generated.
- Local with maximal ideal n is `[IsLocalRing S]`, with n canonically represented by
  `IsLocalRing.maximalIdeal S`. No chosen extra maximal ideal is needed.
- Completeness is `[IsAdicComplete (IsLocalRing.maximalIdeal S) S]`.
  `AdicCompletion.of_bijective_iff` identifies this exactly with the stated bijectivity
  of S → lim S/n^n, including injectivity, not merely precompleteness.
- The conclusion `IsGRing S` is the dependency definition: Noetherianity and regularity
  of the canonical completion ring map at every prime ideal. Expanding it gives
  exactly the node's final clause, including all primes, not just the maximal ideal.

Dependency declarations read and used:
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing` (docstring and full signature).
- `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion`, `IsAdicComplete`, and
  `AdicCompletion.of_bijective_iff` (definitions and signatures read).
  This serves both adic-completion dependency nodes; the latter's Mathlib match is usable.
- `Sheaf.RingTheory.GRing`, `IsGRing`; its complete definition and the underlying
  `RingHom.IsRegular` and `Algebra.IsGeometricallyRegular` were read. This module is imported;
  Mathlib completeness and Noetherian definitions are available transitively.

Edge cases: fields (maximal ideal zero) are included; characteristic zero and positive
characteristic are both included; no domain or reducedness hypothesis is imposed, so
Artinian rings and complete local rings with nilpotents are included. Mathlib's local
ring convention excludes the zero ring, as does the unique-maximal-ideal convention
in Stacks. Every ring universe is permitted. There are no new definitions, disputed
statements, corrected statements, or unusable dependencies.

Searches (msearch.py, group J1, this item):
- LeanSearch: `A complete Noetherian local ring is a G-ring`; unavailable (Internal Server Error).
- LeanFinder: `A Noetherian complete local ring is a G-ring`; eight unrelated results,
  including `isLocalRing_of_isAdicComplete_maximal`, Hausdorffness and Noetherian
  localization criteria; no G-ring theorem.
- Loogle: `IsAdicComplete, IsNoetherianRing, IsLocalRing`; one result,
  `AdicCompletion.instIsAdicCompleteMaximalIdeal`, which concerns the completeness
  of the completion rather than geometric regularity of formal fibres.
- Mathlib grep: `IsGRing|G-ring|geometrically.?regular`, RingTheory; no hits.
- rg with `IsGRing|G-ring|isGRing_of_isNoetherianRing_of_isAdicComplete` in upstream
  WeilConjectures and project lean/Sheaf: only the existing G-ring definition module;
  no theorem for complete local rings.
- grep of the item id in upstream WeilConjectures: no hits.
- rg of the proposed name and item id in dag/lean_names_upstream.json: no hits.

Server compilation succeeded without errors or warnings before packaging; the final
module is compiled again by the dry run. No second-reading section is supplied: the
independent second reader writes it.

## Second reading by J1

Independent second reader: I opened the sandbox node and CompleteLocalGRing.lean,
all four statement-dependency nodes, and their recorded declarations. The local
Stacks .tex files are absent. I read the actual source places from the upstream
[more-algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex)
(label proposition-Noetherian-complete-G-ring, lines 12355–12389) and
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex)
(label definition-complete-local-ring, lines 44785–44803), and checked the tag
pages 07PS, 0324 and 07GH. The proposition has no further standing hypothesis:
its proof introduces exactly a Noetherian complete local ring. The domain and
power-series assumptions occur only after reductions in the proof.

Object, hypothesis and conclusion checklist (written from the node first):

- A commutative ring S: `(S : Type u) [CommRing S]`. Exact; u is explicitly
  declared and arbitrary. There is no field, domain, reducedness or algebra
  structure assumed on S.
- S is Noetherian: `[IsNoetherianRing S]`. Exact. I read Noetherian/Defs.lean,
  including `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`: this means
  that every ideal is finitely generated, as def-weil-pbc-noetherian-ring says.
- S is local with maximal ideal n: `[IsLocalRing S]`, with n represented by
  `IsLocalRing.maximalIdeal S`. Exact; the maximal ideal is unique, so choosing
  its canonical representative loses no case and adds no hypothesis. I read
  LocalRing/Defs.lean: local rings are nontrivial, matching the source's convention.
- The canonical map S to the inverse limit of S/n^n is bijective:
  `[IsAdicComplete (IsLocalRing.maximalIdeal S) S]`. Exact. I read both
  def-weil-pbc-adic-completion and def-weil-pbc-adically-complete-ring, then
  AdicCompletion/Basic.lean (`AdicCompletion`, `of`, `IsAdicComplete`,
  `of_bijective_iff`) and Algebra.lean (`evalₐ`, `evalₐ_of`). Completion is
  compatible quotient sequences. For M = S the submodule n^j • top equals
  the ideal n^j; the canonical map has precisely the quotient coordinates.
  `of_bijective_iff` includes both separatedness and precompleteness, so the
  typeclass assumption is neither stronger nor weaker than the node.
- Conclusion S is a G-ring: `IsGRing S`. Exact. I opened the dependency
  def-weil-pbc-g-ring and Sheaf/RingTheory/GRing.lean, including all three
  definitions, rather than inferring this from the theorem's name. `IsGRing`
  requires Noetherianity and, for every `(p : Ideal S) [p.IsPrime]`, regularity
  of the canonical `algebraMap` from `Localization.AtPrime p` to its completion
  at that local ring's maximal ideal. This is the node's every-prime clause,
  not merely the maximal-prime instance. `RingHom.IsRegular` is flatness plus
  geometrically regular fibres; `Algebra.IsGeometricallyRegular` includes
  Noetherianity and regularity after every finite purely inseparable field
  extension. The residue-field-first tensor order is canonically isomorphic
  to the source's completion-first order. All quantifiers are those of the node.

Edge cases: fields (n = 0), complete Artinian rings, and rings with nilpotents
are covered. Neither characteristic zero nor positive or mixed characteristic
is excluded. The zero ring is excluded by locality in both conventions, not by
an added assumption. Empty schemes and empty index sets are not objects of
this theorem. The inverse limit includes j = 0, whose quotient is the zero
ring and imposes no additional restriction. S has any universe u. The G-ring
dependency tests finite extensions in Type (max u v); every finite extension
has a representative in that universe since it is finite-dimensional over its
base field, so this does not narrow geometric regularity.

Independent searches, using different conceptual wording from the worker:

- LeanSearch via msearch.py: `formal fibres of Noetherian complete local rings
  are geometrically regular`; service unavailable (Internal Server Error).
- LeanFinder via msearch.py: `geometrically regular formal fibers of a complete
  local ring`; eight hits concerning localness from adic completeness, smooth
  and etale loci, unramified algebras, Henselian rings and de Rham rings. None
  states the G-ring conclusion or regularity of all completion maps.
- Loogle via msearch.py: `"IsGRing"`; zero hits.
- Independent rg over Mathlib/RingTheory, upstream WeilConjectures and project
  lean/Sheaf for `grothendieck ring|formal.?fib[er]+|isGRing|geometric.*regular|
  complete.*local.*g-ring`: only the project's GRing definition, unrelated
  scheme geometric-fibre regularity, and PolynomialFormalFiber.lean. I opened
  `Polynomial.formalFiber_isGeometricallyRegular`: it is a positive-characteristic
  statement for particular polynomial formal fibres, with domain and prime
  hypotheses, not this complete-local G-ring theorem. No existing declaration
  renders the item. The search service results are also recorded in searches.jsonl.

No semantic mismatch found; no Lean or node change needed. There are no new
nodes or dependency modules to review, and no statement correction or citer
verdicts to audit. The single import uses the dependency's actual definitions
and supplies the Mathlib predicates transitively. The module and theorem
source tags are present; the theorem docstring follows all seven node proof
steps, including the quotient reduction, regular subring, quasi-finite ascent,
regular completion and both characteristic cases. No definitions are introduced,
no fact is proved, and the only proof body is `by sorry`. Every binder and
universe is explicit. The recorded lean.statement equals the Lean signature
verbatim, excluding `:= by`. Second reading changed only this review report.
