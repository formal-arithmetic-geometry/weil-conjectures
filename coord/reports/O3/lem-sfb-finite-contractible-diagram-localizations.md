## Worker report

The module `Sheaf.RingTheory.FiniteContractibleDiagramLocalizations` states
`CommRingCat.finiteContractibleDiagramLocalizations`, with its sole proof `sorry`.
It supplies the complete three-clause statement, including the canonical localization
colimit and the exact inverse-image equality expressing locality. There are no new
definitions, new nodes, dependency repairs, statement corrections or disputed statements.
Only the item's `lean` field changes. The prior Q126 PASS is the stage-1 split review,
not a Lean statement or an instruction to split the node again. No split is changed.
There is no repair note for this item.

Hypotheses and clauses, matched against the node:

- A commutative w-contractible base is `(A : Type v) [CommRing A]
  [IsWContractibleRing A]`. The recorded upstream class inherits precisely
  `IsWStrictlyLocalRing` and extremal disconnectedness of the component space.
- A nonempty small directed poset is `(D : Type u) [PartialOrder D] [Nonempty D]
  [IsDirected D (· ≤ ·)]`. Its category is Mathlib's category of a preorder;
  a morphism attached to i ≤ j is `homOfLE hij`. No linear order is assumed.
- The direct system of commutative A-algebras with unital A-algebra maps is
  `(F : D ⥤ CommAlgCat.{u} A)`. Its functor laws are exactly the transition laws,
  and its morphisms are AlgHoms, so they commute with the A-algebra structures.
- Finite A-module generating lists are `hfinite : ∀ d, Module.Finite A (F.obj d)`.
  Finite presentation as A-algebras is `hfp : ∀ d,
  Algebra.FinitePresentation A (F.obj d)`. These are separate hypotheses.
- The ring colimit B, coprojections and universal property are a cocone `c : Cocone F`
  with `hc : IsColimit ((forget₂ (CommAlgCat A) CommRingCat).mapCocone c)`.
  Thus B is `c.pt`, and iota_d is `(c.ι.app d).hom.toRingHom`. The colimit is
  required in commutative rings, not merely asserted to be an algebra colimit.
  Its compatible A-algebra structure is canonical: any ring colimit of the given
  nonempty algebra diagram has this structure. This is also the parent's interface.
- Clause (1) is `∀ d, IsWContractibleRing (F.obj d)`. Its explicitly mentioned
  consequences are inherited fields: `IsWStrictlyLocalRing.toIsWLocalRing` and
  `IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization`. Thus the
  w-locality and strict henselianity at every maximal ideal are included, without
  substituting another definition of w-contractibility.
- Structural-map clause (2) is the second conjunct. For each d it asserts
  `(algebraMap A (F.obj d)).Finite`, `.IsIntegral`, and maximality of the comap
  of every maximal ideal. `RingHom.Finite` uses exactly the source scalar action;
  `RingHom.IsIntegral` says each target element satisfies a monic polynomial
  evaluated under that map.
- Transition-map clause (2) is the third conjunct, for every `i j hij` and the ring
  map `(F.map (homOfLE hij)).hom.toRingHom`. It asserts all the same three properties.
  No injectivity, surjectivity or finite-presentation condition on transitions occurs.
- Clause (3) quantifies over `p : PrimeSpectrum c.pt`; `p.asIdeal` is exactly an
  arbitrary prime ideal with its primality proof. Its hypothesis is
  `∀ d, (p.asIdeal.comap (c.ι.app d).hom.toRingHom).IsMaximal`, precisely the stated
  maximal-coordinate condition. This condition is not claimed for all colimit primes.
- Strict henselianity of B_p and maximality of the contraction under A → B are the
  first two conjuncts under that hypothesis: `IsStrictlyHenselianLocalRing
  (Localization.AtPrime p.asIdeal)` and
  `(p.asIdeal.comap (algebraMap A c.pt)).IsMaximal`.
- The existential `L : D ⥤ CommRingCat.{u}` and object equalities `hL` identify its
  stages with `(B_d)_(iota_d^{-1}(p))`, using the recorded `Localization.AtPrime`.
  The first equation on L says that each transition commutes with the maps from
  the original rings. Localization's uniqueness property then forces the fraction
  formula b/s ↦ phi(b)/phi(s): the denominator's inverse must map to the inverse
  of its image. These equations specify the canonical maps, not arbitrary maps.
- The next conjunct is the exact equality of inverse images of maximal ideals
  under `eqToHom (hL i).symm ≫ L.map (homOfLE hij) ≫ eqToHom (hL j)`.
  Both endpoints are the specified prime localizations, so this is exactly the
  locality of those fraction maps, expressed without choosing extra local structures.
- A cocone `l : Cocone L` and `hl : l.pt = CommRingCat.of
  (Localization.AtPrime p.asIdeal)` have the canonical compatibility equation
  with each original coprojection. The same localization uniqueness fixes each
  leg to b/s ↦ iota_d(b)/iota_d(s). `Nonempty (IsColimit l)` is the full ring
  colimit universal property. Consequently B_p is canonically the indicated
  colimit, including the coprojections specified by the node.

The object equalities hL and hl only transport along equal bundled commutative rings.
They introduce no arbitrary underlying objects into the mathematical assertion: the
rings, their maps, and their universal property are all fixed by the displayed equations.
The base-ring universe v and diagram/stage universe u are explicitly bound and independent.
Every variable is explicitly bound, and autoImplicit is disabled. The statement contains
no local notation, private definitions, local instances, hidden let binders or chosen maps.

Dependency declarations read and used:

- `sk-def-pe-wlocal`: `IsWContractibleRing` in
  `WeilConjectures.RingTheory.ProEtale.WContractible`, with `IsWLocalRing` and
  `IsWStrictlyLocalRing` in `WeilConjectures.RingTheory.ProEtale.WLocal`, and
  `WLocalSpace` in `WeilConjectures.Topology.SpectralSpace.WLocal.Basic`.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation` in
  `Mathlib.RingTheory.FinitePresentation`.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`, `IsColimit`
  and `colimit`, from `Mathlib.CategoryTheory.Limits.HasLimits` and its imports;
  `CategoryTheory.IsFiltered` was also checked in Filtered.Basic.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`.
- `def-weil-pbc-henselian-terminology`: `IsStrictlyHenselianLocalRing` in
  `WeilConjectures.Mathlib.RingTheory.Henselian`, publicly imported through WLocal.

The modules for all recorded proof dependencies are imported: `Sheaf.RingTheory.FiniteWContractible`
(theorem `isWContractibleRing_of_finite_finitePresentation`), the upstream w-local module,
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`Algebra.IsIntegral.of_finite`),
`Mathlib.RingTheory.Ideal.GoingUp` (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'`),
the colimit/localization modules already listed,
`WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
(`AlgebraicGeometry.filteredColimitLocalizationAtPrime`), and
`Sheaf.RingTheory.FilteredColimitStrictlyHenselianLocal`
(`CommRingCat.isStrictlyHenselianLocalRing_colimit_of_local_maps`).
Their signatures and proof docstrings were inspected. The existing prime-localization
comparison uses the same object-equality/compatibility formulation. It is a proof
input, not a new definition needed in the statement. Its statement-local lets are not
copied. The node's full six-step argument is in the new theorem's docstring.

Edge cases checked: a one-object directed poset reduces to finite permanence and its
localizations; zero base or zero stages are admitted (with no prime in a zero colimit,
clause (3) is vacuous); a finite product of separably closed fields is allowed;
noninjective algebra transitions such as k[epsilon]/epsilon² → k are allowed;
no transition surjectivity is required. Empty D is excluded exactly as the node says.
There is no reducedness, flatness or nontriviality assumption. Finite presentation
and module finiteness are retained separately. The conditional maximality is used
exactly where strict henselian stage localizations are needed.

Searches actually run:

- `msearch.py` LeanFinder: “Finite finitely presented algebras over a w-contractible
  ring have integral transition maps and strictly henselian localizations of a directed
  colimit at primes with maximal contractions”. Eight results include QuasiFiniteAt,
  IsEtaleAt and finite-presentation locality; none states this combined theorem.
- `msearch.py` Loogle: `"IsWContractibleRing", "FinitePresentation"`; no hits.
- `msearch.py` grep: `WContractible|StrictlyHenselian.*[Cc]olimit|[Cc]olimit.*StrictlyHenselian`;
  no Mathlib hits.
- `msearch.py` LeanSearch: “Finite finitely presented algebras over a weakly
  contractible ring and strictly henselian localizations of their directed colimits”.
  Eight hits concern finite presentation and presentations, not the whole statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for localization diagrams,
  localization cocones, colimits and finite-contractible names identified the
  recorded localization comparison, finite-permanence result and parent theorem.
  No exact existing combined statement exists. The upstream
  `IsWContractibleRing.of_finite` also covers finite permanence alone.
- The required `grep -rn` of the item id in `lean/WeilConjectures` had no hits.

The actual wrapper search results are retained in the sandbox's `searches.jsonl`.
Source text checked: Stacks proetale.tex Tag 0986 and algebra.tex Tag 04GI;
the finite-integral and prime-localization declarations and all cited proof modules
were also read. No external result or alternative proof route is introduced.

Validation: `scompile.py O3 lem-sfb-finite-contractible-diagram-localizations` compiled
the module cleanly on the project server as sandbox and final library module, 2.2 s each.
There were no errors or warnings. All Lean lines are at most 100 characters, and the
node signature is extracted verbatim from the theorem header. All other node fields
are identical to the current base. Dry-run and push receipts follow in the delivery output.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
