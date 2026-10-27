## Worker report

Stage 2, Q38, 2026-10-23. This resumes the retained Lean draft. The sandbox
initially contained the module and three search records, but no node copy or
report. There was consequently no retained delivery packet to push again.
The live node has no Lean binding; its Q63 ledger entry records the accepted
stage-1 split. The current queue assigns stage 2. No repair note or stage-2
return for this item was present. The inherited unchanged-item rejection was
from the earlier stage, not a reason to re-split this accepted node.

The delivered module is
`Sheaf.AlgebraicGeometry.LogConditionFineChartLocality`. It introduces two
fully constructed helper definitions and three theorems, each with a `sorry`
proof. All five are recorded in `lean.declaration`/`lean.declarations`.
Nothing is proved in this delivery. The item's statement, proof, sources and
all existing dependencies are unchanged. Its statement dependencies gain the
already-landed `def-trf-fine-log-etale-descent-datum`, which owns the fine
predicate and isomorphism interface used here. No new definition node or
dependency repair is needed.

Sources actually read: ILO, Exposé VI 1.1, printed p. 69 (PDF page 75), and
Exposé VIII Remark 3.3.4(i)--(ii), 3.3.8, printed p. 107 (PDF page 113).
VI stipulates étale log structures and locally Noetherian underlying schemes,
and defines fine/fs by local charts. VIII describes strict étale charts and
the descent context. The elementary log-unit equalizer argument is the
accepted node's proof, rather than a claimed verbatim theorem in ILO.
The recorded restriction and log/chart definitions were read in full.
The latest blueprint ancestor proof now discusses contracting
correspondences; as the accepted Q63 split report explains, the inherited
logarithmic ancestry describes older genealogy. I checked the latest source
but did not alter that maintainer-reviewed metadata.

### Hypotheses and clauses

- The underlying locally Noetherian scheme is `{T : Scheme.{u}}`
  with `[IsLocallyNoetherian T]` in each theorem. No separatedness,
  quasi-compactness, global Noetherianity or characteristic is assumed.
- The small étale site is exactly `T.Etale` with
  `T.smallEtaleTopology`. The family `U : ι → T.Etale` encodes all
  covering arrows as étale scheme morphisms. Its hypothesis
  `hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x`
  is joint surjectivity, for an unrestricted `ι : Type v`.
- The monoid sheaf and structural homomorphism are exactly the fields
  `monoidSheaf` and `alpha` of `M : EtalePrelogStructure T`. The former is
  a `Sheaf T.smallEtaleTopology CommMonCat.{u}`; its restriction maps
  preserve identity and multiplication. The latter has target the
  multiplicative-monoid functor of the actual étale structure presheaf.
- Slice restriction is `M.etaleRestrict U`, constructed from the existing
  `M.monoidSheaf.over U` and `Scheme.Etale.overEquiv U`. Its structural
  map is `Functor.whiskerLeft` along the canonical composition functor
  from the local étale site. The source test scheme and its ring of
  functions are unchanged. This is a specialization of the existing
  localization, with real data and no new choice of a local sheaf.
- The local log hypothesis is `hlocal` in `logCondition_etale_local`:
  for each `a` there exists `N : EtaleLogStructure (U a).left` with
  `N.toEtalePrelogStructure = M.etaleRestrict (U a)`. The equality
  preserves the whole sheaf and its structural map, rather than merely
  the sections on the covering object. A log axiom is a property, so
  this existential over its proof-bearing extension is precisely the
  local log condition on the given prelog structure.
- The canonical map from inverse images of units to units on an arbitrary
  object `W` is `M.unitSectionMap W`. Its domain is
  `{m : M.monoidSheaf.obj.obj (op W) // IsUnit (M.alpha.app (op W) m)}`;
  its codomain is `{r : Γ(W.left, ⊤) // IsUnit r}`. It sends `m` to
  `alpha m`, with the supplied proof of being a unit.
- The first conclusion of `logCondition_etale_local` is
  `∀ W : T.Etale, Function.Bijective (M.unitSectionMap W)`.
  This is the full monoid-sheaf isomorphism condition: the canonical
  map already preserves multiplication, identity and restriction, and
  its objectwise inverse does too by uniqueness. A sectionwise bijective
  natural monoid homomorphism has a natural monoid inverse. In particular
  this does not merely assert a bijection on global sections of `T`.
  The second conclusion supplies `N : EtaleLogStructure T` with
  `N.toEtalePrelogStructure = M`, explicitly recovering the recorded
  geometric-stalk encoding of the log axiom without changing `M`.
- The remainder is stated in `fineChart_etale_local` for the now-global
  `M : EtaleLogStructure T`. Stating this after the first theorem avoids
  choosing an arbitrary global extension inside the signature: apply
  the first theorem and eliminate its existential to obtain this `M`.
  No extra global log assumption is imposed on the original prelog data.
- `N : ∀ a, EtaleLogStructure (U a).left` and `e` specify arbitrary
  local log structures identified over the structure sheaf with the
  restriction of `M`. `EtalePrelogStructure.Iso` contains both the
  natural monoid isomorphism and its structural-map compatibility.
  Taking the identity isomorphisms gives the node's direct-restriction
  case; allowing these `e` gives its isomorphic-local-structure clause.
- Each local cover is `V : ∀ a, J a → (U a).left.Etale` with
  unrestricted `J : ι → Type w`. `hcoverV` is its explicit joint
  surjectivity. Each chart monoid is `P a j : Type u` with the explicit
  dependent `CommMonoid` instance, and its chart map is `β a j`.
- Finite generation is `hfg : ∀ a j, Monoid.FG (P a j)`.
  Integrality is `hintegral`, injectivity of the actual canonical map
  `Algebra.GrothendieckGroup.of (M := P a j)`. This uses the node's
  definition of integrality and imposes no torsion-free group condition.
  `hchart` is the existing `(N a).IsChart (V a j) (β a j)`.
- The first conclusion asserts that every `x : T` has a preimage in
  one of the schemes `(V a j).left` under
  `(V a j).hom ≫ (U a).hom`. `Scheme.Etale.mk` in the next clause
  bundles precisely these same composite étale arrows, so their
  étaleness as well as joint surjectivity is retained.
- The second conclusion asserts that the map
  `((e a).iso.hom.app (op (V a j))).hom.comp (β a j)` is an
  `M.IsChart` on that composite object. Evaluation of `etaleRestrict`
  on `V a j` is definitionally evaluation of `M` on the composite;
  there is no replacement chart, altered monoid or unspecified map.
- The third conclusion is `M.IsFine`, using exactly the landed
  étale-local finitely generated integral chart predicate.
- The fourth conclusion is conditional on
  `∀ a j, IsFineSaturatedMonoid (P a j)` and concludes
  `M.IsFineSaturated`. The predicate contains finite generation and
  integrality already present in `hfg`/`hintegral`, together with
  saturation. Its multiplicative condition `g ^ n` for `0 < n`
  is exactly the additive condition `n g` in the node. Repeating those
  two already-assumed properties in the saturation premise changes
  neither its strength nor the monoids being tested.
- Finally, `EtaleLogStructure.isChart_comp_prelogIso` states the node's
  chart-isomorphism clause independently for every `W`, every chart
  monoid `P`, and every structure-preserving isomorphism `e : N ≅ M`.
  It imposes no finite-generation, integrality or saturation condition
  on this clause, and its resulting chart map is literally `e ∘ β`.

### Recorded dependency declarations

I read each statement dependency node, its full Lean signature and its
source docstring, including the following interfaces:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.Etale`, `Scheme.smallEtaleTopology` and
  the jointly-surjective characterization of covering families.
- `def-weil-pbc-etale-sheaf-of-sets`:
  `Mathlib.CategoryTheory.Sites.Sheaf`, `CategoryTheory.Sheaf`.
  Applying its existing category-valued form to `CommMonCat` gives
  the monoid sheaf in the recorded prelog definition.
- `def-pur-localized-ringed-site`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `overMap`, `overFunctorMap`, and
  `CategoryTheory.Sheaf.over`/`GrothendieckTopology.over` from
  `Mathlib.CategoryTheory.Sites.Over`. This item uses `Sheaf.over`
  for its monoid sheaf; no module-sheaf specialization is substituted.
- `def-trf-fs-log-blowup`:
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`,
  `AlgebraicGeometry.EtalePrelogStructure`, `EtaleLogStructure`,
  `EtaleLogStructure.IsChart` and `IsFineSaturated`. I read their
  actual geometric-stalk definitions, including `stalkAlpha`,
  `unitsIn`, `IsStalkChart`, and the quotient pushout condition.
- Added landed dependency `def-trf-fine-log-etale-descent-datum`:
  `Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum`,
  `EtaleLogStructure.IsFine` and `EtalePrelogStructure.Iso`.
  Its public upstream import
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver` supplies
  `Scheme.Etale.overEquiv`, `etaleToOver` and their sheaf equivalence.
  I read those constructions and their evaluation formula.

The proof-only imports expose every available proof dependency. Both
cover-base-change and cover-composition nodes have exact Mathlib matches
in `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`: the respective
`Scheme.instIsStableUnderBaseChangePrecoverageOfIsJointlySurjectivePreservingOfIsStableUnderBaseChange`
and `Scheme.instIsStableUnderCompositionPrecoverageOfIsStableUnderComposition`
instances specialize to étale morphisms. The affine-adjunction match is
`AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` in
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`; fibre products use
`CategoryTheory.Limits.pullback` and its projections in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
The representable-sheaf node is the upstream theorem
`AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf` in
`WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`.
These are private proof imports, while statement dependencies are public.
The theorem docstrings carry all four accepted proof steps: pull back the
cover, uniquely glue local unit lifts using sheaf separatedness, compose
the chart covers, and compose the stalk chart isomorphism with the given
isomorphism over the structure sheaf.

### Edge cases

Checked the empty scheme and empty covering family. `hcover` correctly
excludes an empty family on a nonempty scheme and permits it on an empty
scheme; the sheaf condition on the empty object makes the unit-section
map a bijection there. No nonempty-index hypothesis is introduced.
The same check applies to empty local covering index sets. Empty charts
on empty components cause no problem. The identity cover and its
identity local identifications give precisely the original chart maps.
Repeated indices and infinite covering families require no finite
subcover. The trivial log structure and the trivial chart monoid are
allowed. For an integral finitely generated nonsaturated monoid such
as the additive submonoid generated by 2 and 3, the fine conclusion
applies, while the fs conclusion still requires the additional
saturation hypothesis. Isomorphism transport itself works for arbitrary
commutative chart monoids. All schemes, functions and monoid sheaves
use the existing dependency universe `u`; independent cover-index
universes `v` and `w` are explicit. The restriction functor makes no
additional size equality. No false statement or statement correction
was found.

### Searches

The retained `searches.jsonl` records the actual earlier searches on
2026-10-23, which I read before repeating any tool:

- LeanFinder: "A prelog monoid sheaf is a log structure if its log unit
  condition holds on an etale covering; fine saturated charts are
  etale local" returned eight ordinary étale topology/locality hits,
  including `Scheme.smallEtaleTopology` and
  `RingHom.Etale.propertyIsLocal`, with no logarithmic theorem.
- Loogle: `EtalePrelogStructure, EtaleLogStructure, IsChart` returned
  no hits; the service reported unknown `EtalePrelogStructure`.
- Mathlib grep: `LogStructure|PrelogStructure|fine.*chart` in
  `AlgebraicGeometry` returned zero hits.

A fresh LeanSearch query, "The log unit condition and fine saturated
monoid charts descend along jointly surjective etale covering families",
returned eight ordinary jointly-surjective topology, cover and flat
descent declarations, including `Scheme.smallEtalePretopology`, but
no log-unit or chart-locality theorem. The service answered normally;
this search is also recorded in `searches.jsonl`.

Direct `rg` searches in the prescribed `lean/WeilConjectures`,
`lean/Sheaf`, and `dag/lean_names_upstream.json` used
`EtalePrelogStructure`, `EtaleLogStructure`, `IsFineSaturatedMonoid`,
the exact item id and all five proposed declaration names. The upstream
project has no matching logarithmic structure or theorem. The Sheaf
searches locate the two recorded owning modules just listed and the
monoid predicate in `LogRegularPair`; there is no existing restriction
helper or theorem with any of the proposed names. Unrelated
`etaleRestrictionTensorIso` and `counitSectionMap` hits were discarded.
The existing datum node was read and reused rather than copied.
The withdrawn example `Sheaf.CategoryTheory.CompactObject` was read;
its current node points to the upstream `WeilConjectures` definition.
This delivery follows the current module/public-import convention.

### Validation

The retained draft was first checked with the prescribed `scompile.py`:
its sandbox and actual module checks both completed successfully in
1.9 seconds with no errors or warnings. The final module additionally
makes the recorded statement and fibre-product proof imports explicit.
Final validation and delivery use `deliver2.py`, which recompiles the
complete packet and runs the server preflight.

## Second reading by Q38

This is the dispatcher's single worker's final rereading, not a claim
that another agent was started. The maintainer supplies the independent
review. With the node, the dependency definitions and the module open,
I checked the local hypothesis is the entire restricted log structure,
not a single section set, and the global equality preserves both the
sheaf and its structural map. Sectionwise bijectivity is quantified over
every étale object, so it states the canonical sheaf isomorphism.
I checked the chart theorem's target type: its transported map evaluates
`e` on the original local test object, and its codomain is definitionally
`M` evaluated on the composite étale object. This is why no arbitrary
comparison map or extra compatibility hypothesis was necessary.
The separate isomorphism theorem retains arbitrary chart monoids.
The fine and fs clauses use the existing predicates, and the redundant
finite-generation/integrality parts of the fs premise add no condition.
The first theorem followed by the second proves the original conditional
statement without strengthening its global hypotheses.

The draft needed no mathematical correction. I added its missing node
record and report, declared the already-landed fine/Iso dependency,
listed both helpers and all three theorems, and made the owning module
imports explicit. The item's accepted natural-language statement and
proof are unchanged; there are no new nodes and no dependency modules.

Final dry run: `deliver2.py Q38 lem-trf-log-condition-fine-chart-locality
--no-push` exited successfully and printed `OK (dry run): commit
6a16eb21c60 passes the preflight and compiles; nothing pushed`. Both the
sandbox and actual module compile passed with no warnings. The packet
contains exactly this module, the item's node and its report. The final
push uses the same prescribed wrapper and repeats those checks.
