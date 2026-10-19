## Worker report

This is stage 2 of `def-per-fs-log-smooth-etale`, not a repetition of Q02's
stage-1 split. The Q02 ledger entry at line 41209 records the accepted split,
not a Lean statement: the base node has no `lean` or `reviewed_lean` record.
The previous NG worker left only dispatch markers in this sandbox.

The module `Sheaf.AlgebraicGeometry.FSLogSmoothEtale` defines compatible chart
data, its canonical scheme comparison, and both `EtaleLogHom.IsLogSmooth` and
`EtaleLogHom.IsLogEtale`. There are no theorem declarations, postponed proofs,
`sorry`s, new nodes, dependency replacements, or changes to the node statement.
All data are genuine constructions. Every universe and variable is explicitly
bound and `autoImplicit` is disabled.

Clause-by-clause correspondence:

- The morphism `f : EtaleLogHom X Y`, with `X Y : FineSaturatedLogScheme.{u}`,
  is exactly a morphism of locally Noetherian fs log schemes. The recorded
  structure already contains the local Noetherian condition, the log monoid
  sheaf, its structural map and fs charts. No additional geometric hypothesis
  is imposed. `EtaleLogHom` supplies its natural map on sections in every
  relative etale diagram and compatibility with regular functions.
- The inherited log API uses multiplicative monoids. Thus `1`, multiplication,
  powers and `GrothendieckGroup` represent the node's zero, addition, integer
  multiples and group completion. This is a change of notation only, with no
  restriction on the commutative monoids.
- The monoid ring is Mathlib `MonoidAlgebra ℤ P`, the finite-support functions
  `P →₀ ℤ` with convolution multiplication. Its monomial `single p 1` represents
  `z^p`; multiplication of monomials and the multiplicative identity give
  `z^p z^q = z^(pq)` and `1 = z^1` in this notation.
- `FSLogChart.W` and `.V` are respectively etale objects over `Y.scheme` and
  `X.scheme`; their structure maps are etale by the actual small-etale-site
  object definition. `map : V.left ⟶ W.left` and `map_over` are precisely the
  local commutative square over `f.base`.
- `P`, `Q`, their `CommMonoid` structures and `fineP`, `fineQ` are the two fine
  saturated chart monoids. `chartY`, `chartX`, `chartY_isChart`,
  `chartX_isChart` use the dependency's own chart predicate for restrictions
  of the two log structures to these etale objects. No unrelated local log
  structure is supplied. The monoid map is `g`, and `chart_compatibility`
  identifies the image of each base chart section under the actual
  `f.sectionMap` with the corresponding source chart section.
- `EtaleLogStructure.chartToSpec` applies the ring homomorphism
  `(MonoidAlgebra.lift ℤ Γ(W.left, ⊤) P ((M.alpha.app (op W)).hom.comp β)).toRingHom`
  to the `ΓSpec.adjunction.homEquiv`. This is exactly the canonical map to
  `Spec ℤ[P]` specified in the node, on arbitrary (including nonaffine)
  etale neighbourhoods. It is not an arbitrary map or an existence choice.
  MonoidAlgebra's lift maps `z^p` to the structural image of `β p`.
- `Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g))` is the
  contravariant map on spectra induced by `ℤ[g]`. The field `square` records
  the node's displayed equality of the canonical maps. This is not a further
  geometric hypothesis: `chart_compatibility`, `f.compatibility`, the monoid
  ring universal property and the global-sections/spectrum bijection imply
  it. It is kept as the commutativity witness needed by the fibre-product
  constructor; no theorem or extra axiom is used to construct such a witness.
- `FSLogChart.comparison` is `pullback.lift c.map (chartToSpec ...) c.square`.
  Its target is exactly the scheme fibre product in the node. It is the
  specified `(f_i,a_i)`, not an independently chosen comparison map.
- `FSLogChart.groupMap` is the canonical group-completion lift of `g`.
  Its `.ker` is `K_i`; `FSLogChart.cokernel` is the actual quotient of the
  source-chart group completion by that group map's range, namely `C_i`.
  `CommGroup.torsion c.cokernel` is the subgroup of elements killed by a
  positive power, i.e. by a positive multiple in additive notation.
- `IsSmoothChart` requires `Finite c.groupMap.ker` and
  `Finite (CommGroup.torsion c.cokernel)`. Their orders are `Nat.card` of the
  actual subgroup types. For every `x : c.V.left`, both natural-number casts
  must be `IsUnit` in `c.V.left.presheaf.stalk x`, the ordinary scheme local
  ring. The last conjunct is Mathlib `Smooth c.comparison`. It makes no
  injectivity or torsion-free-cokernel assumption.
- `IsEtaleChart` instead requires `Finite c.cokernel` for the whole cokernel,
  and the unit condition uses its whole order. It retains the finite-kernel
  condition and uses Mathlib `Etale c.comparison` for the last conjunct.
- `EtaleLogHom.IsLogSmooth` says that every `x : X.scheme` belongs to
  `Set.range c.V.hom` for some compatible chart `c` with `c.IsSmoothChart`.
  This is exactly existence of a covering family of the required charts:
  a covering family gives the pointwise witnesses; conversely the collection
  of all such charts (or charts chosen for each point) is a covering family.
  `IsLogEtale` uses the identical covering condition and `IsEtaleChart`.
  There is no nonempty, quasi-compact, fixed-chart or single-neighbourhood
  restriction on the cover.

Dependency declarations read and used:

- `def-trf-fs-log-blowup`: module
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, declarations
  `FineSaturatedLogScheme`, `EtaleLogStructure`, `EtaleLogStructure.IsChart`,
  `EtaleLogHom`, and its section-map compatibility. The fs monoid predicate
  `IsFineSaturatedMonoid` is reexported from
  `Sheaf.AlgebraicGeometry.LogRegularPair`; its full definition was read.
- `def-sbc-smooth-morphisms`: module
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-etale-morphism`: module
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-pc-fibre-product`: module
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.lift`; the scheme pullback
  instances are available through the imported geometric modules.
- `def-weil-affine-spectrum`: module
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`.
- `lem-weil-pbc-morphism-into-affine-scheme` is a Mathlib leaf:
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, `ΓSpec.adjunction`.
  Its full adjunction definition and orientation of `homEquiv` were read.
  The canonical map uses it directly. That leaf's additional basic-open
  preimage assertion is not required by the present node.

Additional Mathlib ingredients are the existing monoid algebra, Grothendieck
completion, kernel and quotient group, `CommGroup.torsion`, `Finite`, `Nat.card`,
and `IsUnit`. These are not new notions or private copies.

Sources read: ILO Expose X Proposition 1.2 and its proof, printed pp.136--138
(PDF pages 142--144), and Expose XVI 3.6.1--3.6.5, pp.252--253 (PDF pages
258--259). These give the compatible chart and scheme-comparison framework,
the invertible torsion condition, and the explicit reference to Kato 3.5.
Kato's general theorem remains WANTED locally as the base node already says.
This module defines the node's chart condition; it asserts no equivalence
with an infinitesimal-lifting definition.

Edge cases checked before and after writing:

- Empty `X`: both pointwise cover conditions hold vacuously, corresponding
  to the empty covering family; no global chart needs to be chosen.
- Trivial charts/log structures: kernel and cokernel are trivial groups of
  order one; the canonical comparison is the ordinary scheme morphism.
  These recover ordinary smoothness and etaleness locally.
- Identity chart: group kernel and cokernel have order one and impose no
  characteristic restriction; the comparison is the usual identity base
  change map.
- The Kummer map `N → N`, `1 ↦ n`, `n > 0`, has zero kernel and cokernel
  `Z/n`. The definition requires exactly that `n` be invertible on the chart
  source; it does not silently assume the cokernel is torsion-free. This
  excludes wild characteristic dividing `n`.
- The chart `0 → N` has zero kernel and torsion subgroup, but whole cokernel
  `Z`. The smooth criterion allows it, while this chart fails the finite
  whole-cokernel etale criterion.
- Noninjective group maps with finite invertible kernel are retained. No
  hypothesis from the older injective-chart specialization was imported.
- Nonaffine `W.left` is allowed: the actual global-sections adjunction is
  used, not an assumption that etale neighbourhoods are spectra.
- Orders are taken only after an explicit `Finite` clause, so `Nat.card = 0`
  for infinite types cannot make an infinite kernel/cokernel pass.

Searches for existing definitions (all run for NG and this item):

- `msearch.py ... leanfinder` query:
  `Log smooth and log etale morphisms of fine saturated logarithmic schemes with finite kernel invertible torsion cokernel and smooth chart comparison`.
  Result: 8 hits, ordinary scheme smoothness/etaleness and related algebra;
  no logarithmic structure or compatible monoid chart criterion.
- `msearch.py ... loogle` query `LogSmooth, LogEtale`:
  0 hits; unknown identifier `LogSmooth`.
- `msearch.py ... grep` query `LogSmooth|LogEtale|log.smooth|log.etale`:
  0 Mathlib hits.
- `msearch.py ... leansearch` query
  `log smooth morphism fine saturated logarithmic scheme chart criterion`:
  8 hits about ordinary smooth morphisms/ring maps, no matching definition.
- `rg` of `WeilConjectures/` and `lean/Sheaf` for
  `LogSmooth|LogEtale|log.smooth|log.etale`, and for the proposed names
  `FSLogChart|chartToSpec`: no upstream definition. The landed
  `InjectiveFSLogChart` in `LogSmoothLogRegular` is a strictly specialized
  chart notion: it assumes an injective group map and torsion-free cokernel,
  and contains no definition of either general log-smooth or log-etale
  morphisms. It is therefore not usable as the present node's definition.
  The other hits concern `FineLogEtaleDescentDatum`, which is descent data,
  not a logarithmic smoothness or etaleness predicate.
- `rg` in `dag/lean_names_upstream.json`: no proposed declaration name.
- Search of upstream source for the blueprint id: no declaration.

Validation: `scompile.py NG def-per-fs-log-smooth-etale` compiled both the
sandbox file and its actual library module cleanly, with no warnings. The
first compilation diagnosed unregistered class-valued structure projections;
registering `FSLogChart.instP` and `instQ` globally repaired this. The chart
predicates and both log-morphism predicates then elaborated without any
additional assumptions. Delivery preflight is run through `deliver2.py`.

Preflight repair: the gate records signatures starting at `def`, omitting the
`noncomputable` modifier. The JSON signature was aligned with that convention;
the Lean statement and its mathematical meaning did not change.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
