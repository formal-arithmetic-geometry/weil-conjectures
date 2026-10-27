## Worker report

The module `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` states
`WeilConjectures.RelativeProductBaseChange.factor_squares`, with proof `sorry`.
It constructs the seven actual objects, the six specified factor arrows and all
seven beta isomorphisms independently, using the existing operation datum. The
result is six equalities of derived morphisms, indexed by `Fin 6`, rather than
only naturality of their composite. The mathematical statement is unchanged. This repair extracts an existing selector
interface into its own definition node and repairs its former owning module.

Source checked: `literature/blueprint/latest/blueprint/sec-six-functors/` and
`sk-thm-sf-kunneth-relative/_section.md`, the six-factor construction and
coherence (iii). The original node statement and its proof were read in full.
The source describes the same individual-factor assertion, with normalized
exchange, projection, composition and signed tensor comparisons.

Hypotheses and coefficient conventions:

* `D : FiniteFieldDatum.{u}` is the recorded finite field and its algebraic
  closure, including the positive exponent and characteristic prime.
  `C : D.CoefficientDatum` supplies the distinct coefficient prime and Qbar.
  `E : Type u`, its field, Padic-algebra and finite-dimensional instances give
  the finite extension. The valuation ring and chosen uniformizer are those
  of the recorded coefficient construction, with no additional choice here.
* `m : ℕ` and exponent `m + 1`, with `Nat.succ_pos m`, cover exactly all positive
  coefficient exponents, including n = 1. `S : SixFunctorDatum D C E (m+1) ...`
  is precisely the required supplied datum, with its A1--A6 properties.
* `s : PodCoefficientStage` ranges over finite, integral, rational and common.
  `Ctf S s X` is the full subcategory of the dependency's actual domain: finite
  Tor at finite/integral coefficients, and all constructible objects at field
  coefficients. `operations` merely selects the recorded stage.
* `Product D` contains B, X, Y, T as `SixFunctorSpace D`; these are already
  finite-type schemes over k. Its separated structure maps express B separated
  and the separated sources. Together with f and g over k this is equivalent
  to B separated and f,g separated as in the node. `mapSeparated` supplies the
  resulting separatedness of all maps in the displayed diagrams, not an extra
  geometric hypothesis. The product of such schemes is separated as well.
* `Product.square : IsPullback u v f g` supplies T with its two projections.
  Any such model is canonically the recorded scheme pullback. The fields cf,
  cg, cv, ch retain the compactifications used to write the supplied support
  functors; the datum already supplies comparisons between compactifications.
  h is written as `v ≫ g`; the product equation identifies it with `u ≫ f`.
* The binders `K : Ctf S s G.X`, `L : Ctf S s G.Y` are exactly the two finite-Tor
  inputs. `first`, `image` and `external` are respectively P, Q and H.
* `Change G G'` contains b,x,y,t over k, the Cartesian faces fSquare, gSquare,
  vSquare and the u-face equality. G' itself is a product. These data give
  exactly the base-changed cube and its canonical map between products;
  `uComm` and vSquare force t to be the induced map by the universal property.
  No flatness, properness or smoothness condition is placed on b.
* K' and L' are the actual objects `(pull S s A.x).obj K` and
  `(pull S s A.y).obj L`, both in the actual primed domains.
* `_wK`, `_wL` retain the finite-origin data in the finite case: a bounded-below
  fixed-module complex, its isomorphism to the coefficient realization of K
  or L, and the recorded `FixedEtaleOriginWitness` with its actual etale
  antecedent and comparison isomorphism. They are not mere `Nonempty` choices.
  Other stages need no separate witness and this case distinction gives PUnit.
  The morphism definitions are canonical and independent of a choice of witness.

Clause-by-clause rendering:

| Node clause | Lean construction |
| --- | --- |
| D0 = h!H | `object ... 0`, support of `G.v ≫ G.g` |
| D1 = g!v!H | `object ... 1`, two support functors |
| D2 = g!(v!P tensor L) | `object ... 2` |
| D3 = g!(g*Q tensor L) | `object ... 3` |
| D4 = g!(L tensor g*Q) | `object ... 4` |
| D5 = g!L tensor Q | `object ... 5` |
| D6 = Q tensor g!L | `object ... 6` |
| d0 = inverse alpha | `factor ... 0`, `composition.hom`, directed h! to g!v! |
| d1 = g!(inverse PF_v) | `factor ... 1`, `projectionIso.inv` under g! |
| d2 = g!(inverse Ex tensor identity) | `factor ... 2`, tensor map of `exchangeIso.inv` and identity |
| d3 = g!(sigma) | `factor ... 3`, `symmetry.hom` under g! |
| d4 = inverse PF_g | `factor ... 4`, with arguments L,Q in that order |
| d5 = sigma | `factor ... 5`, with arguments g!L,Q |
| beta0 | h-exchange, then h'! of `externalComparison` |
| beta1 | g-exchange, then g'! of v-exchange and v'! of externalComparison |
| beta2 | g-exchange, distribution of y*, v-exchange on P and canonical u-composition |
| beta3 | g-exchange, distribution, `imagePullComparison` on the first tensor factor |
| beta4 | same route with `imagePullComparison` on the second factor |
| beta5 | b* distribution, g-exchange then f-exchange as the ordered tensor entries |
| beta6 | b* distribution, f-exchange then g-exchange as the ordered tensor entries |
| Lt*H = H' | `externalComparison`: distribution first, then the two `pullSquare` comparisons |
| y*g*Q = g'*b*Q, then f-exchange | `imagePullComparison` |
| Every factor square | `factor_squares`, with i ranging over `Fin 6` |

Lean's composition `≫` is left to right. Thus the theorem's left side is
Lb*(d_i) followed by beta_(i+1), and its right side is beta_i followed by d'_i,
exactly the displayed equation in the node. `Fin.castSucc` and `Fin.succ` select
the adjacent seven objects without losing either endpoint.

Canonical operations, not free parameters:

`pull` and `support` restrict the recorded functors by `sixFunctorDomainChange`.
`tensorValue` is the existing partial tensor restricted on its other argument;
`tensor` lifts it to the full finite-Tor inclusion. `composition` lifts the
supplied support compositor. `pullSquare` composes the supplied canonical
pullback compositors with the equality of the underlying geometric composites.
`tensorPull` uses the actual fixed-module derived tensor comparison at finite
coefficients, cancelling only the prescribed coefficient-equivalence units.
The other cases transport `canonicalIntegralPullbackTensor`,
`canonicalRationalPullbackTensor` and `canonicalCommonStagePullbackTensor`
through S's normalization equalities. Integral operations therefore remain
completed; rational and common-stage operations remain the recorded ones.
`symmetry` uses Koszul symmetry at finite coefficients and the unique normalized
integral/rational/common braidings at the other stages.

`compactifiedSquare` constructs the proper/open base-change diagrams from the
actual pullback of a compactification. `exchange` is the canonical published
finite base-change map conjugated by the prescribed realization maps, or the
supplied higher-stage `compactExchange` with its equality fields. It then uses
the supplied comparison if the primed compactification is different.
`projection` is exactly `CompactSupportFiniteProjection.component` at finite
level and `compactSupportProjectionComponent` at other levels. No inverse is
chosen from a bare existence theorem: `exchangeIso` and `projectionIso` use
`asIso` of their already defined arrows, whose inverses are uniquely determined.

Six named theorems have postponed proofs: `coherence`, `tensor_domain`,
`exchange_isIso`, `projection_isIso`, `mapSeparated`, `factor_squares`. Their
source/blueprint docstrings state their mathematical content and proof. They
are the preservation and invertibility clauses needed to express the very
seven objects and six arrows of this node. All definitions contain actual data.
The main proof docstring gives each factor's argument separately and uses strict
coherent quotient towers for the integral equality before derived limit; it
never deduces equality of completed maps from separate levelwise equalities.

Dependency declarations read and used:

* `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`,
  `SixFunctorCoherentStage`, `sixFunctorDomainChange`, the stage coherence,
  exchange, projection and compositor fields. The recorded def-sf-datum module
  is reexported by `Sheaf.Paper.SixFunctorDualNotation`, the def-sf-pf module.
* `Sheaf.Paper.SixFunctorDualNotation`: projection notation explicitly reuses
  the existing compactification projection. Its coefficient-dual declarations
  are not mistaken for new projection maps.
* Mathlib `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` and
  `IsPullback`, including the scheme pullback instance and pasting. This uses
  the recorded Mathlib declaration of def-pc-fibre-product.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, with both fields retained.
* `Sheaf.Paper.CtfCoefficientStageSelectors`: `WeilConjectures.PodCoefficientStage`,
  `.domain`, `.operations`, `.tensor`; these select existing categories and
  operations, not a fresh coefficient model. This new module owns all eight
  selectors; PodCtfAdjunctions now publicly imports it.
* `Sheaf.Paper.ConstructibleProjectionMates` (publicly reexported by the above):
  `compactSupportProjectionSquare`, `compactSupportProjectionComponent`,
  `CompactSupportFiniteProjection.realization`, `partialTensor`, `component`,
  `fixedTensor`, `fixedDerivedPull`, `fixedPullComparison`, `pullRealization`,
  `fixedPullRealization`, `supportRealization`, `fixedSupportRealization`.
* `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `canonicalIntegralPullbackTensor`, `canonicalRationalPullbackTensor`,
  `canonicalCommonStagePullbackTensor`, owned by
  def-pur-completed-pullback-tensor-comparison, cited directly.
* `Sheaf.Paper.DerivedPullbackTensorIso`:
  `pullbackTensorIntegralBraiding`, owned by the directly cited definition
  def-pod-integral-tensor-constraints; `pullbackTensorRationalBraiding` and
  `pullbackTensorCommonBraiding`, with their unique-map pinning theorems, owned
  existing:true by the directly cited def-sf-rational-common-tensor-symmetries.
* `Sheaf.CategoryTheory.DerivedTensorKoszulSymmetry`:
  `CategoryTheory.derivedTensorKoszulSymmetry`, owned by the directly cited
  def-pur-localized-derived-tensor-braiding. Its body is identical to the old
  `projectionCoherenceSymmetry`: `DerivedMonoidal.braiding'` at Qh and quasiIso.
  The finite coefficient's Noetherian fact is supplied inline by
  `isNoetherian_of_finite` after `Padic.finite_coefficientExtensionRing`; the
  old theorem-owned plain instance is not used as a dependency.
* `Sheaf.Paper.DirectImagesConstructible`:
  `WeilConjectures.finiteFieldDatumPrimeUnit`. This exact theorem constructs
  residue-field invertibility via the structure map; no invertibility
  hypothesis is added. The owning node is cited for this helper, not for an
  unrelated direct-image conclusion.

Statement dependencies now cite the selector definition, the three specified
comparison/braiding definition owners, ConstructibleProjectionMates, the genuine
rational/common braiding theorem, and the prime-unit theorem. The unused theorem
nodes det-thm-sf-ctf-stability-adjunctions and
lem-pur-projection-formula-coefficient-coherence have been removed from stmt_deps.
The original statement, proof and source fields remain unchanged. Proof imports include
`Sheaf.Paper.ExchangeFunctoriality` (fix-lem-exchanges),
`Sheaf.Paper.IntegralCoherenceTower` and
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`. The operation definition
for def-weil-derived-pullback-tensor-hom is already publicly available through
the statement imports. `prop-sf-pf-coherence` is a forward proof dependency
with no recorded module in this checkout; it remains in the DAG and the proof
plan without an invented import. No statement construction waits on it.

Edge cases checked mathematically: n = 1; either input zero; empty schemes;
identity b and arbitrary Cartesian representatives; b nonflat, nonproper and
nonsmooth; different compactifications of primed maps; odd-degree shifts where
Koszul signs matter; all four coefficient stages. No nonempty-scheme condition
or positivity of cohomological degrees occurs. The pro-etale site's object
universe u+1 and morphism universe u are inherited unchanged. Fixed-module
coefficients have the required u+1 lift. No equality of these universes is imposed.

Searches for an existing exact statement (msearch.py, group Q18 and this item):

* leanfinder: "Base change commutes with each of the six factors of the relative
  compact support Kunneth morphism" returned eight ordinary tensor/base-change
  and pullback results, none the six specified factor squares.
* loogle: `"baseChange", "comp"` returned twelve ordinary linear/tensor
  base-change results, none this assertion.
* grep: `relativeProduct|kunneth.*baseChange|factorSquare` in CategoryTheory
  returned no results.
* leansearch: "derived compact support Kunneth base change individual factor
  squares" returned eight unrelated support/function results.
* rg in `lean/WeilConjectures` and `lean/Sheaf` for relative-product/factor-square
  names, and grep for this exact node id in WeilConjectures, found no existing
  declaration. Existing relative Kunneth-map naturality is about the entire
  composite and does not state these six separately defined squares.

Validation of the returned head: the original 644-line module compiled cleanly
and delivery 191b54044d2 was returned solely for the H2 ownership issue. This
repair compiles all three delivered modules, including the extracted selector
and the repaired importing theorem module, in dependency order. The current
compile and dry-run results are recorded below when returned. Both automatic
implicit options remain false, with no diagnostic commands in the delivery.

## Second reading by Q18

The dispatched instructions prohibit starting another agent. This section is a
separate self-reading with the node, current blueprint and complete module open;
it is not represented as an independent worker review. The maintainer performs
the independent review on delivery.

The six branches of `factor` and seven branches of `beta` were reread against
all displays. Their ordering and directions agree, including inverse PF_v,
inverse inner exchange, the L,Q ordering in PF_g, and the opposite exchange
orders in beta5/beta6. The comparison defining beta0 uses the pasted h square;
beta1 exchanges g before v. No beta uses the assertion being stated. The finite
witnesses are retained data, not replaced by existence. Completed and field
operations use the recorded normalization interfaces. Compilation defects found
during drafting (a grouped structure-field syntax, projection indentation and
a missing import for the existing prime-unit theorem) were repaired before the
clean complete-module compile. No mathematical mismatch or disputed statement
remains. The maintainer return independently confirmed the mathematical rendering.
No existing node statement was altered.


## Repair of returned delivery 191b54044d2f

The sole numbered issue is H2, addressed in all of its requested parts:

1. Move the eight `PodCoefficientStage` declarations, with unchanged names,
   signatures and bodies, from PodCtfAdjunctions to CtfCoefficientStageSelectors.
   The definition node def-sf-ctf-coefficient-stage-selectors owns the new module.
   PodCtfAdjunctions imports it and reexports every old public name. Its theorem
   node changes only in `lean`, removing the extracted definitions from its
   ownership list. The item imports and cites the definition rather than the
   unused adjunction theorem.
2. Replace the single finite `projectionCoherenceSymmetry` use by the identical
   `CategoryTheory.derivedTensorKoszulSymmetry`, import its module and cite
   def-pur-localized-derived-tensor-braiding. Remove the unused coefficient-
   coherence theorem dependency and its import.
3. Cite def-pur-completed-pullback-tensor-comparison directly for all three
   `canonical*PullbackTensor` maps and def-pod-integral-tensor-constraints for
   the integral braiding. The rational/common braidings remain genuine uses of
   the recorded theorem's uniquely determined objects. Keep the prime-unit
   theorem, whose Prop conclusion constructs the residue Invertible instance.

Comparison against current main found only the authorized `lean` and added
`stmt_deps` delta for the item. The selector source was read both locally and
with `scompile.py --source Sheaf.Paper.PodCtfAdjunctions`; they agree. The
extraction preserves all theorem bodies and names in the repaired old module.
All seven objects, all six arrows, all seven beta routes and the final theorem
signature remain unchanged from the returned version. Finite Noetherian proofs
are supplied from Mathlib inline to avoid using the former theorem-owned plain
instance. The selectors contain no sorry and select all four coefficient stages,
including arbitrary positive n and schemes without separated structure maps.

This repair's second self-reading checked the new node's statement clause by
clause: the four index constructors, four recorded categories with their category
structures, actual finite-Tor domains versus top at fields, recorded push/pull
and support/exceptional operations, permitted Hom pairs, restricted Hom and
partial tensor are exactly the eight moved declarations. Their data are unchanged.
The new module imports only its two definition dependencies, not PodCtfAdjunctions.
The old theorem module imports the new one, so the move introduces no import cycle.

## New nodes

def-sf-ctf-coefficient-stage-selectors owns the existing four-stage selectors,
now in `Sheaf.Paper.CtfCoefficientStageSelectors`. Its statement fixes the recorded
operation datum (def-fix-six-functor-datum) and the finite partial tensor
(def-sf-constructible-projection-mates), and describes each of the eight selectors.
It asserts no restricted adjunction or new preservation theorem. Source: the
current relative-product unit's coefficient conventions and finite-Tor domains.
Mathlib searches through msearch.py (LeanFinder, Loogle, grep, LeanSearch) found
no selector for these project coefficient stages. Exact outputs, query strings,
hit names and digests are recorded in its mathlib_searches. Project grep found
the existing eight definitions solely in PodCtfAdjunctions; DAG matches were their
theorem owner and consumers, with no definition owner. Blueprint searches found
zero PodCoefficientStage nodes and 81 general coefficient-stage consumers.
The implementation is moved, not copied alongside the old declarations.

## Dependency modules

det-thm-sf-ctf-stability-adjunctions receives a section 1(B) lean-only repair.
The old interface placed the needed selector definitions in its theorem module,
although that theorem's conclusion is not used by this item. Its sandbox module
now publicly imports the new selector module and removes exactly the extracted
block. All remaining declaration bodies and theorem statements are unchanged.
Its lean.declarations no longer claims the selector definitions, and its main
lean.statement is the verbatim multiline signature from the unchanged theorem.
Every non-lean JSON field is byte-for-byte equivalent as JSON to current main.

Repair compilation: scompile.py checked all three files together, in dependency
order. Its first pass reached the final library-path check but that check hit
60 seconds. The wrapper's automatic confirmation against current server sources
then compiled CtfCoefficientStageSelectors in 26.1 s, PodCtfAdjunctions in 35.0 s,
and RelativeProductBaseChangeFactorSquares in 38.5 s, each with nice 19, two
threads and the unchanged 60-second limit. Final exit status 0, no diagnostics.

Repair dry-run blocker: deliver2.py --no-push compiled the files and staged all
seven intended paths, but preflight rejected the authorized section 1(B) module
repair. It treats det-thm-sf-ctf-stability-adjunctions as outside the item's
statement/proof prerequisite closure after the requested removal of that unused
theorem dependency. Consequently it excludes the accompanying lean-only node
repair and gives the hard error:

> (c) lean/Sheaf/Paper/PodCtfAdjunctions.lean: no node of the delivery has it as
> lean.file (every module is the module of the item, of a new definition node
> or of a dependency node)

The accompanying node does name exactly that file, but the gate has excluded it
from its recognized dependency nodes. The maintainer return explicitly requests
this very extraction and importing-module repair under section 1(B). Readding
the unused adjunction theorem as a statement prerequisite would undo H2; adding
a fictitious dependency would work around the gate. No launcher or repository
file was patched. All requested repair files remain in the sandbox and all
three current-server compiles have passed. No repair delivery was pushed.

Resumed repair retry: compared the retained packet with current main; the item
still differs only in lean/stmt_deps and the existing adjunction node only in
lean. deliver2.py --no-push rechecked all three Lean files successfully and again
rejected the identical ownership classification, with the same hard (c) error
for PodCtfAdjunctions.lean. No delivery mutation was pending or repeated, and
nothing was pushed. The complete requested mathematical and ownership repair
is retained; the prerequisite-closure gate still excludes the explicitly
requested lean-only repair of the former selector owner.


## Maintenance handoff (2026-10-25)

The repeated preflight ownership refusal is resolved on the server. Maintenance
landed the selector extraction and former-owner public import as interface set
20261024T175027-L-3988132 (Lean source included by build commit 403da4e5954), then
committed definition ownership and the former owner dependency in 5ec85b6315a.
The eight selectors and all twelve remaining declarations preserve their exact
signatures and masked bodies. tools/lean_file.sh passed separately: selectors
9.1 seconds, PodCtfAdjunctions 14.8 seconds, each with the 60-second limit.

The already-landed companion node/module copies were archived as .bak files
in this sandbox; the pending delivery now contains only the repaired item node,
item module and report. Keep its direct definition citations and signed symmetry
replacement. Rebase against current sheaf-dag and run normal dry-run/delivery.
See coord/changes/Q18-factor-squares-selector-extraction.md. The earlier blocker
entries above describe the pre-maintenance attempts, not an outstanding gate
failure. No launcher or protected delivery tool was edited.

## Repair of immutable head 2e392df64ebd

The returned H2 point is repaired by replacing the statement dependency
lem-pur-derived-pullback-tensor-iso with the landed definition owner
def-sf-rational-common-tensor-symmetries (Q58, 5897ae80e17). I read that node's
statement and existing:true Lean record, and the full signatures and docstrings
of pullbackTensorRationalBraiding and pullbackTensorCommonBraiding and their
unique-map pinning theorems in Sheaf.Paper.DerivedPullbackTensorIso. The definition
node owns exactly the rational/common signed symmetries used at symmetry's
rational and common branches (lines 267 and 275). The old theorem node is not
needed as a direct statement dependency. The unchanged Lean module retains the
same specified maps, hypotheses, all seven objects and comparisons, six arrows,
and Fin 6 conclusion. The direct dependency
lem-weil-structure-direct-images-constructible remains because
finiteFieldDatumPrimeUnit supplies the residueInvertible proof term.

The previous selector extraction and maintenance handoff above are historical;
those companion modules and nodes are already landed. This repair delivers only
the item node, its unchanged Lean module and this report. No mathematical
statement, proof, proof dependency or Lean declaration is changed.
