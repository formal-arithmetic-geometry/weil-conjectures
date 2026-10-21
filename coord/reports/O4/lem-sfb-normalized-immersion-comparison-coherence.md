## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence` states
`AlgebraicGeometry.Scheme.normalizedImmersionComparisonCoherence`. Its single theorem
has proof `sorry`. All helper definitions have real data: parameter bundles,
transparent parameter types, and composites of the dependency's actual isomorphisms.
There is no new existence assumption on scalar extension or pullback comparisons.
There are no new nodes, dependency repairs, or statement corrections.

Hypotheses, in the order of the node:

- Quasi-compact locally Noetherian schemes are `ImmersionComparisonBase`, the subtype
  of `Scheme` with `IsLocallyNoetherian X ∧ CompactSpace X`. It is a parameter bundle,
  not a new scheme or Noetherian predicate. All source, intermediate and target
  schemes range over this subtype.
- The coefficient labels are arbitrary `I : Type v`, independent of scheme universe
  `u`. `ImmersionComparisonRings.ring` supplies `R_X^r` on `ProEt.topology X.val`.
  `coefficient` supplies the ring inverse-image isomorphism for every immersion.
  `Cartesian.identity` and `Cartesian.composition` identify the resulting coefficient
  arrows with the dependency's actual identity and composite arrows. Consequently no
  coefficient equality, nor an extra ring homomorphism, is silently chosen.
- `G.category r X` is literally `DerivedCategory (proEtaleRingModules X.val (G.ring r X))`.
  These are ordinary unbounded derived module-sheaf categories, with the dependency's
  module and localization universes; the small site keeps its object/morphism sizes.
- `E : LocallyClosedExtensionData`, `hE : E.Coherent`, `D : E.DerivedCoherence` are the
  witnesses supplied by `locallyClosedExtensionCoherence`. `G.extend`, `G.pull` and
  `G.gamma` specialize their exact termwise extension, inverse image and compositor.
  The latter transports along `hG.composition` only. `D.restriction` is used verbatim.
- `F.functor` is the supplied family `F_X^{rs}`. `F.q` has type
  `F_X^{rs} ⋙ L_a^s ≅ L_a^r ⋙ F_S^{rs}`, which is the node's q in Lean's sequencing
  convention. `F.property.1` and `F.property.2` are its coherent identity/composition
  equations, with `G.pullId` and `G.pullComp` inserting the actual identifications.
  `pullId` reads the normalized identity restriction from the dependency's identity
  and restriction isomorphisms; it is not an arbitrary trivialization.
- `B : F.Elementary` supplies separate `openComparison` and `closedComparison`
  isomorphisms with type `E_a^r ⋙ F_X^{rs} ≅ F_S^{rs} ⋙ E_a^s`.
  `openNormalized` and `closedNormalized` impose exactly the typed equation (N) of
  node proof step 1: `L_a^s(d) ≫ rho_a^s = q_a(E_a^r M) ≫ F_S^{rs}(rho_a^r)`.
  Normalization uses both rho maps, rather than equating an ill-typed restricted map
  directly to q. No support-preservation, flatness, adjunction for F or faithfulness
  of restriction on the entire target category is assumed.

Each conclusion clause:

- The existential family `d` gives the assembled comparisons for every immersion.
  `Functors.Coherent.normalized` records their normalization.
- `Functors.composite` is the prescribed factorization formula: inverse gamma for
  coefficient r, the comparison for the outer arrow, the comparison for the inner
  arrow, and gamma for coefficient s. Only functor associators intervene.
- `Coherent.closedOpen` states that `d` equals this composite for a closed arrow
  followed by an open arrow. Thus all such factorizations of the same immersion give
  the same iso after equality transport. `Coherent.openClosed` states the same for
  the opposite factorization order, and hence also compares those factorizations.
- `Coherent.openComparison` and `closedComparison` retain agreement with both given
  elementary comparisons, including identity, empty and clopen immersions.
- `Coherent.composition` is the node's first displayed equation at every M: Lean writes
  first `F_X(gamma_r)`, then `d_ab`, while its right side is `d_a`, then `E_a^s(d_b)`,
  then `gamma_s`. The functor arguments match the stated domains and codomains.
- `Functors.Tower r s t` supplies exactly the additional natural isomorphisms t for one
  triple of labels, with no unmentioned associativity hypothesis. Its `compatible` field
  is the node's q/t equation at every object, in Lean's left-to-right composition
  convention. (Maintainer review fix: the delivered version demanded t for every triple.)
- `Coherent.tower` is conditional on every such tower H for the triple; it is exactly the last
  displayed equation: `F_X^{st}(d_a^{rs})`, `d_a^{st}`, `E_a^t(t_S)` equals
  `t_X(E_a^r M)`, `d_a^{rt}`. This conditional clause does not require t to exist.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  the locally ringed space and local-affineness structure and its actual morphisms.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no separation condition).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for `SheafOfModules`; the dependency's `proEtaleRingModules`
  is that same module-sheaf construction for commutative ring sheaves, not a new model.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, ordinary localization at cochain quasi-isomorphisms.
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` and its publicly reexported
  `LocallyClosedModuleExtensionCoherence`: `LocallyClosedCoefficients`,
  `LocallyClosedCoefficientImmersion` with `identity`, `comp`, `pull`, `pullComp`;
  `LocallyClosedExtensionData` with `derived`, `Coherent`, `DerivedCoherence`, and
  `locallyClosedExtensionCoherence`. The complete field signatures were read, including
  restriction and gamma termwise normalization, full faithfulness, the Hom bijection,
  and the unit and associativity laws. The sole public import provides these notions
  and all the underlying Mathlib definitions; no existing definition is copied.

The theorem docstring gives the node's seven-step natural-language proof: normalization,
restriction detects equality on objects isomorphic to extension images, binary
normalization, both factorizations, arbitrary immersion composition, and the two
restricted tower paths. The module makes no proof claim beyond its one `sorry`.

Edge cases checked before writing: the empty scheme and empty immersions satisfy the
same parameter bundle; no nonemptiness is imposed on schemes, labels or module objects.
The zero ring sheaf and zero object are allowed. For a clopen arrow the input has both
comparisons, with their equality concluded. Identity arrows use canonical coefficient
and restriction identity maps. Repeated labels r=s=t impose no extra identity on F or
t; only the explicitly supplied q and t equations apply. Open-then-closed factorizations
are included only when given. No field, finite type, separatedness, boundedness or
flatness condition has been introduced. Scheme, site and label universes remain distinct.

Searches actually run with `msearch.py O4 lem-sfb-normalized-immersion-comparison-coherence`:

- LeanFinder: “Restriction normalized comparison isomorphisms for fully faithful locally
  closed extensions are independent of factorization and compatible with composition and
  coefficient towers”. Eight hits, headed by `AlgHom.restrictNormal_comp` and
  `AlgEquiv.restrictNormal_trans`, with scheme Zariski restriction composition among the
  remaining hits. None gives the arbitrary-ring pro-etale conditional statement.
- Loogle: `CategoryTheory.Functor.Faithful, CategoryTheory.NatTrans`: zero hits.
- Mathlib grep: `normalized.*immersion|immersion.*comparison.*coher|extensionByZero`
  both in `CategoryTheory` and in the whole Mathlib tree: zero hits.
- LeanSearch: “Equality of normalized comparison maps detected by restriction on
  extension by zero images”: eight hits, beginning `ContinuousMapZero.ext`,
  `ZeroAtInftyContinuousMap.ext_iff`, `ContinuousMapZero.ext_iff`; no match.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf`, plus
  `dag/lean_names_upstream.json`, for the item id and the proposed names:
  no existing statement or collision. The related `ScalarSixPullback` was read; it
  specializes to condensed scalar extension on finite-type schemes over a field and
  does not state this conditional arbitrary coefficient-system assertion.

No node fault or `STATEMENT-DISPUTED` finding was identified in the source comparison.


Current-source repair and validation (2026-10-21): retained the saved packet and
first ran the prescribed dry run. The previously missing dependency artifacts are
now available; the first new diagnostic was a 60-second timeout in the item itself.
An import-only check passed in 2.6 seconds. Diagnostic prefixes and synchronous
profiling isolated the functor parameter structure. Disabling automatic size and
constructor-injectivity auxiliaries alone did not repair the timeout.

`Functors` now stores exactly the same data as a dependent pair (the supplied family
and q) with a subtype imposing the conjunction of its identity and composition laws.
`Functors.functor` and `Functors.q` are explicit projections of that supplied data.
This replaces the generated structure interface without changing a hypothesis or
clause; both laws are still mandatory, at `F.property.1` and `F.property.2`.
The extension helper also explicitly supplies the existing coefficient bundles to
`E.derived`, avoiding expensive backwards inference. No new data are chosen and no
definition contains a proof placeholder. The primary theorem signature is unchanged.

The full repaired module passed the prescribed `scompile.py` check: both sandbox and
library-name passes completed in 3.7 seconds, with no warnings or errors. The exact
same source is the delivered module. All diagnostic tracing, markers, and prefix
files remain confined to `scratchpad/` and are outside the delivery packet.
The saved node was refreshed from the current shared node, retaining only the `lean`
record and updating its declaration list. Its signature was compared verbatim with
the file, all lines meet the 100-character limit, and its only postponed theorem is
`normalizedImmersionComparisonCoherence`. No repair note exists for this item.
The maintainer performs the independent second reading under the dispatcher's rule.

The required `deliver2.py O4 lem-sfb-normalized-immersion-comparison-coherence
--no-push` passed: `OK (dry run): commit 8afc0e9194b passes the preflight and
compiles; nothing pushed`. The final push uses the same module and node record.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-21)

`Functors.Tower` was parameterized by the triple of labels `(r s t : I)`, and
`Coherent.tower` now quantifies `∀ (r s t : I) (H : F.Tower r s t)`. The delivered
structure required t and its q/t square for every triple in `I`. For non-invertible
coefficient changes (the citer det-prop-scalar-six-pullback (3), with
`Λ → Λ' → Λ''`) that hypothesis cannot be satisfied: triples such as `(B, A, B)` would
need `F^{AB} F^{BA} ≅ F^{BB}`. The node gives t for one triple only. The theorem
signature, the node `lean` record and the declaration list are unchanged. The fixed
module compiles clean with `nt_compile.py`.
