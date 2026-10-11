## Worker report

The module states `tate_n2_complete_principal`. It binds a commutative domain `R`, a
field `K` with `Algebra R K` and `IsFractionRing R K`, and the element `x : R`.
`[IsNoetherianRing R]` renders Noetherianity; `hnormal : IsIntegrallyClosed R`
renders that the normal domain is integrally closed in its fraction field. The
instance `[IsAdicComplete (Ideal.span ({x} : Set R)) R]` renders xR-adic
completeness. The instance `[IsDomain (R ⧸ Ideal.span ({x} : Set R))]` renders
that R/xR is an integral domain. The hypothesis `hquot` is
`IsN2 (R ⧸ Ideal.span ({x} : Set R)) (FractionRing (R ⧸ Ideal.span ({x} : Set R)))`,
rendering that the quotient is N-2 using its fraction field. The conclusion
`IsN2 R K` says every finite field extension of K has integral closure finite as
an R-module.

Dependencies used are `IsN2` (module
`Sheaf.RingTheory.JapaneseDomain`), Mathlib `IsNoetherianRing`,
`IsIntegrallyClosed`, `IsAdicComplete`, `IsDomain`, `Algebra`, `IsFractionRing`,
and `FractionRing`.

Edge cases checked: x = 0 is included (the principal ideal is zero and the
quotient is R); x need not be nonzero or a nonunit; arbitrary universe levels
u and v are retained for R and its fraction field; the quotient and its
fraction field use the quotient's own domain instance.

Searches actually run:
- LeanFinder: "normal Noetherian domain complete along principal ideal quotient
  Japanese implies Japanese" returned eight hits on DVRs, Dedekind rings,
  Noetherian localization and adic Hausdorffness, none the criterion.
- Loogle: "IsAdicComplete, IsIntegrallyClosed, integralClosure" returned zero hits.
- msearch grep: "japanese|Tate|IsN2" in RingTheory returned unrelated occurrences
  (including "statement"); no matching theorem.
- rg on project lean/Sheaf and upstream WeilConjectures for IsN2, integralClosure
  and IsAdicComplete found the existing notions and other finiteness theorems,
  but no Tate criterion. Exact item-id/name searches upstream and in
  dag/lean_names_upstream.json returned no hits.

Source checked at https://stacks.math.columbia.edu/tag/032P because the local
algebra.tex is absent. Its three assumptions and conclusion agree with the node.
The module docstring records the node's twelve proof steps for stage 3.
No statement correction or disputed statement was needed.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker specified by the dispatcher. This worker
has checked the clause mapping above, but does not claim an independent reading.

## Second reading by V1

I independently read the node, its seven statement-dependency nodes and their
recorded declarations, and the delivered Lean module. The repository has no
local Stacks checkout. I fetched the upstream Stacks algebra.tex into the item's
scratchpad and read lemma-tate-japanese (Tag 032P), including its proof, as well
as https://stacks.math.columbia.edu/tag/032P. The source has precisely the three
assumptions below; no local-ring, characteristic, or extra finiteness hypothesis
is implicit in this lemma.

Clause-by-clause checklist (all verdicts: exact):

- Object R, a commutative ring: `(R : Type u) [CommRing R]`.
- Object x, an arbitrary element of R: `(x : R)`; its principal ideal xR is
  `Ideal.span ({x} : Set R)`, and the quotient is the corresponding `R ⧸ ...`.
- R is a domain: `[IsDomain R]`, including nontriviality.
- R is Noetherian: `[IsNoetherianRing R]`. I read the Mathlib abbreviation
  `IsNoetherian R R`, expressing finite generation of every ideal.
- R is normal as a domain: `hnormal : IsIntegrallyClosed R`. I read the
  normal-ring dependency's domain clause and Mathlib's abbreviation for integral
  closedness in `FractionRing R`; this is the domain specialization the node
  asks for, not a substitute notion of normality.
- R/xR is an integral domain: `[IsDomain (R ⧸ Ideal.span ({x} : Set R))]`.
- R/xR is N-2: `hquot : IsN2 (R ⧸ Ideal.span ({x} : Set R))
  (FractionRing (R ⧸ Ideal.span ({x} : Set R))))`. Its fraction field is the
  canonical fraction field of this quotient, with no extra hypothesis on it.
- R is xR-adically complete, including injectivity of the completion map:
  `[IsAdicComplete (Ideal.span ({x} : Set R)) R]`. I read both parent classes
  `IsHausdorff` and `IsPrecomplete`, and `AdicCompletion.of_bijective_iff`,
  which identifies this assumption with the node's bijective canonical map.
- Object K, the fraction field of R: `(K : Type v) [Field K] [Algebra R K]
  [IsFractionRing R K]`. Naming an arbitrary fraction field introduces no
  restriction: every domain has one, and choices are algebra-isomorphic.
- Conclusion, for every finite field extension L/K its integral closure is a
  finitely generated R-module: `IsN2 R K`. I opened JapaneseDomain.lean:
  its body quantifies over `[Field L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L]` and concludes
  `Module.Finite R (integralClosure R L)`. The tower enforces exactly the
  composite R-algebra structure required by the node. I also read Mathlib's
  `Algebra`, `integralClosure` (carrier `IsIntegral R`), `IsIntegral`, and
  `Module.Finite` (finite generation of the top submodule). No conclusion is
  omitted or strengthened, and no field extension is required to be separable.

Edge cases: x = 0 is allowed, with quotient R and automatic zero-adic
completeness. A unit x is ruled out by the quotient-domain hypothesis, exactly
as in the source. The zero ring is ruled out by the domain assumptions, not by
an added assumption. Characteristic zero and all positive characteristics are
included. There is no index-set, scheme, or numerical n parameter; completeness
uses all natural powers, including n = 0. R and K have independent universes u
and v. The shared IsN2 definition quantifies over extensions in K's universe;
finite extensions admit a model there (finite-dimensional vector spaces over K),
so this excludes no finite field extension up to algebra isomorphism. The same
observation applies to the quotient's canonical fraction field.

Independent H4 searches, using different words from the first worker:

- LeanFinder via msearch: "finiteness of normalization from completeness and
  Japanese principal quotient". Eight results: Dedekind characterizations,
  DVR TFAE, Noetherian localization, normal closure, and complete integral
  closure; none is Tate's criterion.
- Loogle via msearch: `IsAdicComplete, Module.Finite`: zero results.
- rg over upstream WeilConjectures, the project's lean/Sheaf/RingTheory, and
  Mathlib's AdicCompletion and IntegralClosure directories for Tate, Japanese,
  IsN2, and normalization/completeness. The existing JapaneseDomain definitions
  and related ascent, descent, polynomial and power-series statements do not
  state this criterion. Exact declaration-name and IsN2 searches in upstream
  WeilConjectures and dag/lean_names_upstream.json found no declaration.

No new definition nodes, dependency modules, or statement correction occur in
this delivery. Every required notion is already furnished by a dependency.
The theorem docstring gives all twelve proof steps in node order; the module
and declaration identify Tag 032P and the blueprint node. There is one theorem,
with `sorry` as its whole proof, and no definitions, local notation, local
instances, or unbound variables/universes. I found no mismatch and left the
Lean module and node unchanged. The second reading adds only this report.

Validation: single-file scompile succeeded with no errors or warnings except
the permitted declaration-uses-sorry warning. The node's lean.statement was
checked against the file signature verbatim (apart from trailing whitespace).
