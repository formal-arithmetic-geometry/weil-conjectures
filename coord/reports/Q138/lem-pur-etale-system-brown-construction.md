## Repair status

The ownership blocker was fixed upstream by maintenance commit
`cdd2ab41a778f24bd5bd3c8a439fd5825747cd4a`. Read the current maintenance handoff in
`coord/preferred-upstream/lem-pur-etale-system-brown-construction.md`. The sandbox
copies of both relocated dependency modules and nodes are byte-identical to main
and are omitted from the delivery diff. The mathematical repair below supplies the
remaining explicit recorded-q identification, retaining the universal-S conclusion.

## Worker report

The module `Sheaf.Paper.EtaleSystemBrownConstruction` states
`AlgebraicGeometry.etaleSystemBrownConstruction`, with its sole postponed proof `sorry`.
It defines two conclusion records, `StrictEtaleBrownComponents` and
`StrictEtaleBrownConstruction`, using the already published strict-system categories,
compact-support presentation, evaluation, scalar-extension models and scalar actions.
No data are chosen from existence of an unspecified object. One new definition node
supplies the normalized comparison interface between the existing constant-ring-sheaf
and fixed-scalar encodings. There is no statement correction.

Source read: Zheng, Construction 4.1 and Lemma 4.10 (printed pp. 21, 23),
Constructions 5.14--5.15, Lemmas 5.13 and 5.16, and the Brown paragraph (printed
pp. 34--35). The latter explicitly uses unbounded categories, small direct sums,
and the derived insertion comparison. Also read the current blueprint's
`sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`:
this item concerns ordinary etale strict systems, not the erroneous ambient pro-etale
adjoint discussed at the end of that blueprint definition. The node's ten-step proof
is reproduced in the theorem docstring, with each step's dependency ids.

Hypothesis and clause matching:

- `D : WeilConjectures.FiniteFieldDatum` fixes the algebraic closure of a finite field,
  its characteristic `D.p` and the finite-field data. `l`, `Fact l.Prime`, `_hl : l ≠ D.p`
  give precisely the prime and characteristic restriction.
- `E`, `Field E`, `Algebra (Padic l) E`, `FiniteDimensional (Padic l) E` give the finite
  local-field extension; `Padic.coefficientExtensionIntegers l E` is the existing O.
  The parameter `t` has hypotheses `_ht : t ≠ 0` and `_hunit : ¬ IsUnit t`.
  A uniformizer is not required. Schemes live in universe u; coefficients in u+1,
  as in the published ordinary etale system interface. Smaller coefficient types
  are included by the usual universe lift. No site object/hom universes are equated.
- `X.Over`, `Y.Over`, the two structure-morphism `LocallyOfFiniteType` and
  `QuasiCompact` pairs give finite-type k-schemes. `f.IsOver` gives a k-morphism;
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` give separated finite type.
  There is no separatedness condition on Y. `c : Compactification f` includes the
  open immersion c.i, proper c.g, and the factorization equation.
- The first conjunct states finiteness of O/(t)^(n+1); the second gives its
  l-power annihilation. Principal ideal powers equal (t^(n+1)). The third gives
  surjectivity of the actual `Ideal.Quotient.factor` for all m ≤ n, including identity.
  `IsAdicComplete (Ideal.span {t}) O` is completeness and separatedness for the
  canonical inverse-limit map, not existence of an unrelated ring isomorphism.
- The universal `∀ S : StrictEtaleCompactSupport O t c` uses the given actual
  open extension and total proper derived functor. `S.functor` is definitionally
  `S.derivedOpen ⋙ S.properDerived.system.direct`; its finite-level counterpart is
  `S.levelFunctor n`. The proper derived presentation includes the universal
  right-derived pair, its computation on K-injectives, and its normalized Hom
  transpose. The open presentation includes termwise localization and its normalized
  transpose, so the objects and morphisms are independent of resolution choices
  through the canonical universal comparisons.
- `componentsX`, `componentsZ`, `componentsY` record Grothendieck abelianity,
  coproduct existence and evaluation preservation, cohomology comparisons, and both
  cohomological bounds. They apply to the existing abelian system category, not an
  abstract replacement. `S.PX`, `S.PZ`, `S.PY` give actual exact evaluations and
  derived left extensions, their adjunctions, `derivedBelow` tensor formulas and
  `derivedAbove` vanishing. No new version of L_n is defined here.
- `additive`, `shift`, `exact`, `coproducts` give the exact coherent-shift functor
  preserving every family indexed by `Type (u+1)`, including the empty family.
  `scalarX` and `scalarY` reuse the section-normalized `StrictEtaleScalarAction`;
  `linear` states commutation with that actual O-action. Additivity plus this
  scalar equation is O-linearity on all Homs, including derived morphisms.
- `S.evaluation n` is already the pasted open/proper canonical isomorphism
  e_n F_A = F_n e_n. `S.properDerived` carries the evaluated proper units,
  counits, coefficient transitions and inverse-image scalar comparison.
  `S.val.property` is the existing open coherence, including the ordinary open
  mate and derived transpose equations. Its exact localization specifies evaluated
  open unit/counit compatibility, rather than adding arbitrary evaluation isomorphisms.
- `properInsertion_conjugate` characterizes beta by conjugating the actual proper
  evaluation comparison under the two composite left-extension/proper adjunctions.
  `properInsertionMate_def` defines lambda by the explicit geometric mate.
  `openInsertion_conjugate` likewise fixes the open insertion from the actual open
  inverse evaluation. `leftExtension_def` pastes these maps using lambda inverse.
  Thus `leftExtension n` is an actual natural isomorphism F_A L_n = L_n F_n in the
  derived category of strict systems, constructed before evaluation. Equality of
  derived system maps is never inferred merely from equality of evaluations.
- `openMate`, `properMate`, `projection_def` retain the finite-level proper/open
  mate construction. `projection_recorded_q` now explicitly identifies its inverse
  with **the exact `Etale.compactScalarMap` appearing in the recorded dependency**,
  after conjugation by the scalar and compact-support realization comparisons.
  The third conclusion of `Etale.SystemProjection.etaleSystemCoefficientProjection`
  identifies the finite-level component of its `Theory.q` with precisely that same
  `compactScalarMap`; the seventh conclusion states it for a single ring map.
  Thus this is an explicit identification with the dependency's q, rather than an
  assertion that two unspecified maps have the same endpoints. The literal quotient
  `strictEtaleBrownRingMap O t h` is used on both sides, including h : n ≤ n.
  Combining this identification with `leftExtension_below` states that the evaluated
  left-extension comparison is q inverse, as the node requires. Above n, both
  sides vanish by the recorded derivedAbove comparisons.
- `realizationX`, `realizationZ`, `realizationY` use the already defined
  `Etale.SystemProjection.constantModule` to restrict to constant scalars. No new
  ordinary realization functor or map is invented. Their `factors` and
  `StrictEtaleBrownRealizationCoherence` fix the derived localization and restriction
  comparisons on all cochain representatives, with ordinary identity-on-sections
  normalization and `scalar_mate` for derived extension. These equations exclude
  arbitrary scalar rescaling of the comparison.
- `properRealization` and `openRealization` identify the given ordinary direct
  images with the fixed-scalar etale direct images by their exact underlying section
  maps. The universal right-derived-unit square fixes each derived right comparison;
  its mate fixes inverse image. `openComparison_mate` fixes the further left-adjoint
  comparison, and `levelComparison_def` is the actual paste of the open and proper
  comparisons. Accordingly the realization used by `projection_recorded_q` is
  canonically normalized, rather than an unrelated natural isomorphism.
- `right` and `adjunction : S.functor ⊣ right` give the whole unbounded Brown
  right adjoint, including its map action. `rightAdditive`, `rightShift`,
  `shiftAdjunction`, `rightExact` and `rightLinear` give the induced additive,
  coherent integer-shift, unit/counit-compatible shift, exactness and O-linearity
  structures. `unitLinear` and `counitLinear` spell out scalar compatibility.
  Compatibility of both shift structures with the adjunction is Mathlib's
  `Adjunction.CommShift`, which determines the right shift from the left shift.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (publicly
  reexported by the support interface).
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement`
  and its category; `Compactification` itself is reexported from Defs.
- The morphism-properties node is a convention node: Mathlib `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` are its specified declarations.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports
  `Padic.coefficientExtensionIntegers` and the coefficient definitions; its
  recorded `finite_coefficientExtensionRing` concerns uniformizer stages. The
  conclusion here specializes the general quotient construction to arbitrary t.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison`, `CoefficientSystemOrdinaryImage`,
  `CoefficientSystemDerivedImage`; the full interfaces and proof docstrings were read.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`:
  `SheafOfModules.systemLevelLeftExtensionTheory`, whose `SystemLevelLeftExtensionTheory`
  includes Grothendieck abelianity, coproducts, cohomology, bounds and insertions.
  Its concrete coefficient-system specialization is the already recorded
  `CoefficientEvaluationDerivedPackage` used by S.PX/PY/PZ, including the actual
  derived extension/scalar adjunctions and representative normalization.
- `Sheaf.Paper.EtaleSystemCoefficientProjection`:
  `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`, whose
  `q` is the scalar-adjunction transpose of the normalized restriction word.
  The explicit new equation `projection_recorded_q` identifies our proper/open mate
  word with that theorem’s published finite-level `compactScalarMap`.
- `Sheaf.Paper.StrictEtaleSystemInterfaces`, owned by
  `def-per-strict-etale-system-interfaces`: `StrictEtaleCompactSupport`, `.functor`,
  `.levelFunctor`, `.evaluation`, `StrictEtaleEvaluation`, `StrictEtaleScalarAction`.
  The interface relocation and parent import adaptation have now landed on main.
  This delivery cites that definition node directly and imports no parent theorem.
  The parent may later import the Brown theorem for its stage-3 proof without a cycle.
- `Sheaf.Paper.EtaleBrownProjectionRealization`: the new definition node described
  below. Its public dependencies are the independent strict interfaces and recorded
  system-projection definition module; it never imports the downstream parent.
- Every recorded proof module is imported plainly. Mathlib proof dependencies are
  already exposed by their appropriate imports (mates, shifts, triangulated
  adjunctions, exact functors, derived linearity, finite-type Noetherianity).

Elaboration detail: the two existing standard derived-category witnesses
`strictEtaleSystemDerived` and `strictEtaleLevelDerived` are given explicit priority
5000 in this module, so every use selects the same witness as the imported support
presentation instead of the different general `systemRingHasDerived` witness.
No mathematical hypothesis or universe equality is added.

Edge cases checked: empty X or Y and the zero complex; nonseparated Y;
all n≥1 encoded by n+1 (so no level-zero quotient); m=n identity quotient;
m<n possibly nonflat quotient; components above the insertion index; empty
coproduct; arbitrary nonzero nonunit t, including a unit times a higher power
of a uniformizer. No constructibility, normalization, boundedness, quotient
flatness or extra properness of f is imposed.

Searches made through msearch.py (Q138, this item):

- leanfinder, "The strict etale coefficient system compact support functor preserves
  coproducts and has a linear exact Brown right adjoint": 8 hits about condensed
  profinite free/solid and locally constant module adjunctions; no match.
- loogle, "Functor.IsLeftAdjoint, Functor.IsTriangulated, PreservesColimitsOfShape":
  zero hits (unknown unqualified identifier Functor.IsLeftAdjoint).
- grep, "Brown|brown", CategoryTheory/Triangulated: zero hits.
- leansearch, "A coproduct preserving triangulated functor from a Grothendieck
  derived category has a right adjoint": 8 hits including
  `CategoryTheory.Adjunction.isTriangulated_rightAdjoint`; this gives the general
  adjoint exactness step only, not the geometric construction or comparisons.
- rg over the project Sheaf and WeilConjectures trees: Brown representability,
  strict etale support and adjunction records, coefficient projection and insertion
  formulas. Reused the support and scalar notions listed above. No declaration
  states all clauses of this arbitrary-t theorem. The exact item-id search in
  WeilConjectures returned no declaration; the upstream name index was also checked.

Validation: every theorem remains sorry; every definition has actual data. Compiler
checks and delivery validation are recorded below after the final run.


## Returned review repair

1. H4/H3 (the recorded projection): added `projection_recorded_q`. Read the full
   signature and docstring of `etaleSystemCoefficientProjection`, including its
   evaluated-q equality and its single-ring specialization. The new equation is
   exactly the conjugation word from that evaluated-q equality, using the actual
   quotient map A_n → A_m. Its right side is the same fully qualified declaration
   `AlgebraicGeometry.Etale.compactScalarMap`. `leftExtension_below` uses the inverse
   of the projection so identified. The comparison functors and all scalar/geometric
   normalization equations are described above. Nothing is inferred from derived
   evaluation being faithful.
2. C6/H2 (parent cycle): main now owns the StrictEtale* declarations in
   `Sheaf.Paper.StrictEtaleSystemInterfaces`, recorded by the existing definition
   node `def-per-strict-etale-system-interfaces`. The Brown module publicly reaches
   that independent module. It does not import `EtaleCoefficientSystemAdjoint`.
   Parent source and its node were compared with main; their adaptation has landed,
   so this delivery needs no downstream node/module modification. The stale packet
   copies have been refreshed byte-identically to main. No prerequisite cycle is introduced.
3. H3 (given support functor): the theorem concludes `∀ S : StrictEtaleCompactSupport
   ... , Nonempty (StrictEtaleBrownConstruction ... S)`. This applies to every given
   support presentation, including the parent's SF. It asserts no extra premise
   on S and does not replace the fixed functor by an existentially chosen one.

## New nodes

`def-pur-etale-brown-projection-realization` defines only the normalized comparison
interfaces needed to identify the two encodings, in
`Sheaf.Paper.EtaleBrownProjectionRealization`. It uses the existing ordinary
`Etale.SystemProjection.constantModule`, the existing evaluation/scalar packages,
and the given ordinary/derived geometric images. Its data and coherence types
specify the section, cochain localization, universal derived-unit and adjunction
mate equations. It asserts no existence or invertibility theorem about q. The
Brown theorem supplies these data as part of its conclusion. The source is Zheng
Construction 4.1 and Constructions 5.14–5.15, Lemma 5.16, with the constant-scalar
and derived normalizations of Stacks 03CV, 06YY and 07A4.

Searches: msearch LeanSearch, query "Exact realization of modules over constant
quotient sheaves and its normalized derived scalar and geometric comparison",
returned eight sheafification/condensed-module hits, no such interface. LeanFinder,
query "Constant scalar realization of derived strict etale coefficients identifies
compact support projection with compactScalarMap", returned eight distribution/
standard-etale hits, no such interface. Mathlib grep `constantModule|compactScalarMap`
in CategoryTheory returned no hits. DAG/project rg found general constant-ring
module equivalence and geometric comparison packages, which were read; none
specializes these diagrams to arbitrary t and the given strict evaluation package.
`ExceptionalFiniteRealization` uses the chosen lifted uniformizer and was read as
an example; importing it here would also reintroduce the parent dependency.
`SystemProjection.constantModule` itself is reused, not copied. Blueprint search
"coefficient projection" returned four different units (four-arrows, four-corners,
finite-direct-image, Kunneth-map-agrees), none defines this comparison interface.
The ancestor command gives `def-weil-exceptional-inverse-image`; the new node cites
that ancestor and the existing item via path. These actual search results are in
the new node's mathlib_searches and searches.jsonl.

## Second reading by Q138

Self-check by the dispatched worker, with node, module and recorded projection
signature open; no other agent was started, as the brief requires. Independent
review belongs to the maintainer. Checked all three returned defects explicitly:
the parent import is absent; the final binder is universal in S; the actual
`compactScalarMap` occurs on the right of `projection_recorded_q`. Traced its left
side from fixed-scalar T(F_n P), through inverse compact-support and scalar
comparisons, through realization of projection inverse, and back to F_m(TP).
This is the exact orientation of recorded q. `leftExtension_below` consequently
uses q inverse. Checked every new interface has actual functors or proof-valued
normalization equations and no existence choice. Empty schemes, zero complexes,
identity m=n, nonflat quotients, levels above n, arbitrary nonzero nonunit t and
unbounded inputs remain covered. The coherence/data separation changes only the
representation of the interface and avoids expensive kernel projection checking.
No source, target statement or dependency theorem was weakened.

## Validation

The required initial saved-packet dry run passed against current main (temporary
commit 255e299878d). The subsequent self-check found and repaired the remaining
recorded-q issue rather than pushing that incomplete saved packet.

The comparison interface initially exceeded the per-file limit. Separated data
from coherence predicates so the kernel does not repeatedly expand dependent
structure projections. No timeout limit or tool was changed. `scompile.py` then
compiled both files cleanly: realization 35.0 seconds in library mode, Brown
construction 23.0 seconds in library mode, with only the expected theorem sorry.
The later dry run repeated compilation against refreshed server sources and found
only the missing new-node `import_flags` field; added `[]` as required by the
current schema. No warning, extra axiom, hollow definition or proof was introduced.

The final corrected packet passed `deliver2.py --no-push`: temporary commit
`d3c1e82a8d5`, preflight and all per-file compiles OK. The staged diff contains only
the Brown module, the new realization module and definition node, the item node,
and this report; the already landed relocation files are unchanged.
