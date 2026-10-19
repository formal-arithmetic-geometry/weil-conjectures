## Worker report

This delivery states `AlgebraicGeometry.gabber_partial_algebraization` in
`Sheaf.AlgebraicGeometry.GabberPartialAlgebraization`. It has one theorem, with `sorry`,
and no new definitions. The mathematical statement keeps the same source content, with its
dimension-function clause rendered by the already landed canonical predicate
`Scheme.IsGeometricDimensionFunction`. Its statement dependencies use
`def-per-geometric-dimension-function`; this replaces the previously recorded
specialization-category interface, whose inline immediate-arrow formulation was not the landed
notion.

Source read: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose V, geometric reformulation
3.1.3 and Remark 3.1.4 (printed pp. 66--67), and Expose XVII, the final paragraph of 6.5
(printed p. 300). The former supplies the regular complete base of dimension d-1 and the
equal-characteristic identity case; the latter gives precisely the completion of a strict
localization and a finite surjective cover used here. The node does not ask for prime-to-ell
generic degree, closed subsets, or a chosen closed point of the special fibre; none was added.

Hypothesis and conclusion correspondence:

- The local scheme X is written `Spec (.of A)`. `CommRing A`, `IsDomain A`, and
  `IsIntegrallyClosed A` express a normal local scheme's normal coordinate domain; for a
  Noetherian local scheme this is equivalent to all its local rings being integrally closed
  domains. Every local scheme in the node is affine; no geometric case is removed by this
  presentation. `IsNoetherianRing A` and `hExcellent : IsExcellent A` give its Noetherianity
  and excellence.
- `IsStrictlyHenselianLocalRing A` is the published upstream class extending henselian
  locality with separably closed residue field. This also supplies the local-ring instance.
- `IsAdicComplete (IsLocalRing.maximalIdeal A) A` is maximal-ideal completeness, using the
  recorded completion node, rather than completeness for an arbitrary topology.
- `ell : ℕ`, `hPrime : ell.Prime`, and `hInvertible : IsUnit (ell : A)` express exactly the
  prime and invertibility hypotheses. `d : ℕ`, `hd : 2 ≤ d`, and `hDimension` assert finite
  topological Krull dimension d, using the recorded `topologicalKrullDim`.
- The existential `X'` and `p : X' ⟶ Spec (.of A)` are the finite cover. `IsFinite p` and
  `Surjective p` assert its finiteness and surjectivity. Normality is written literally at
  each stalk: `∀ x : X', IsDomain (X'.presheaf.stalk x) ∧
  IsIntegrallyClosed (X'.presheaf.stalk x)`.
- The base S is `Spec D`, with `D : CommRingCat`. The existential instances
  `IsLocalRing D`, `IsNoetherianRing D`, and
  `IsAdicComplete (IsLocalRing.maximalIdeal D) D` assert complete Noetherian locality.
  `IsExcellent D` asserts excellence. The recorded `IsRegularScheme (Spec D)` includes
  local Noetherianity and regularity at every stalk. Its topological dimension is exactly
  `((d - 1 : ℕ) : WithBot ℕ∞)`, and `IsUnit (ell : D)` asserts invertibility on S.
- `Z : Scheme`, `f : Z ⟶ Spec D`, `LocallyOfFiniteType f`, and `QuasiCompact f` are the
  finite-type morphism, with both of the recorded defining conditions.
- `Ω : Type u`, the existential `Field Ω` and `IsAlgClosed Ω`, and `z : Spec (.of Ω) ⟶ Z`
  are the geometric point. No bound on its transcendence degree is imposed.
- `Scheme.strictHenselizationRing z` and `Scheme.strictHenselizationScheme z` are precisely
  the dependency's published strict-local construction. The existential local-ring instance
  allows its maximal ideal to be named; it is conclusion data, not a hypothesis on z.
- `e : X' ≅ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal
  (Scheme.strictHenselizationRing z)) (Scheme.strictHenselizationRing z)))` asserts the actual
  isomorphism with the completion. The scheme completion arrow determined by e is e.hom
  followed by Spec of the canonical algebraMap. `RingHom.IsRegular` is applied to that
  canonical algebraMap itself, so it asserts flatness with geometrically regular fibres
  for the completion map, with no arbitrary replacement arrow.
- `IsNoetherianRing (Scheme.strictHenselizationRing z)` and `IsExcellent` of that same ring
  express Noetherian excellence of its affine spectrum, the strict localization.
- The existential integer-valued function δ on `Scheme.strictHenselizationScheme z`
  satisfies `Scheme.IsGeometricDimensionFunction (Scheme.strictHenselizationScheme z) δ`.
  This canonical predicate quantifies over algebraically closed residue fields and geometric
  points in strict localizations, and imposes the dimension-one closure equation with the
  structural map, exactly as in ILO XIV/XVII and the proof plan.
- `ringChar A = ringChar (IsLocalRing.ResidueField A) → IsIso p` retains the equal-
  characteristic case in the same existential witness. Transport the entire conclusion
  along this cover isomorphism to obtain literally X'=X and p=id. Thus the identity cover
  is available; the conclusion does not merely give an abstract unrelated scheme isomorphism.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` (Noetherian, G-ring, J-2, universally
  catenary); its imported `Sheaf.RingTheory.GRing`: `RingHom.IsRegular`, the canonical
  flatness plus geometrically regular-fibre predicate.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `IsAdicComplete`,
  `AdicCompletion`, and its canonical `algebraMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`,
  `Scheme.strictHenselizationScheme`; these abbreviate the same upstream constructions.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.GeometricDimensionFunction`: `Scheme.IsGeometricDimensionFunction`
  on `Scheme.strictHenselizationScheme z`. Its node `def-per-geometric-dimension-function`
  is the statement dependency replacing the unusable specialization-category interface.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.

Every currently recorded proof-dependency module is imported without `public`: finite-type
excellence, Cohen--Gabber finite presentations, complete local excellence, the finite
henselian local model, the Weierstrass henselian cylinder, completion of finite extensions,
finite algebras over complete local rings, regular completion of G-rings, etale
composition/cancellation, integral lying over and maximal ideals. The remaining perverse-specific
proof nodes have no recorded
Lean interface and are named step by step in the theorem's proof docstring rather than
silently replaced by different hypotheses. No proof-only missing interface is needed merely
to state this theorem.

Edge cases: d=2 gives a dimension-one base, including the mixed-characteristic case with one
power-series variable. Both positive equal characteristic and equal characteristic zero use
the same `ringChar` comparison. Mixed characteristic imposes no identity requirement. The
zero ring and empty input scheme are excluded by the input being a strictly henselian local
normal domain of dimension at least two, as in the node. The conclusion's normality is
stalkwise and adds no integrality hypothesis on an arbitrary cover. The geometric point has
an arbitrary algebraically closed field in the scheme universe, the published strict-local
API's convention. There is no independent smaller test universe, no characteristic
restriction beyond ell invertibility, and no finite-type requirement on the completion map.
Identity specializations impose no extra δ equation, since the dimension condition is one.

Searches: all semantic and Mathlib grep searches below were executed using `msearch.py Q65`
for this item. LeanFinder query "Gabber partial algebraization complete normal strictly
henselian local scheme finite cover" returned normalization, etale objects, and smooth-algebra
descent, with no partial algebraization theorem. Loogle query "AdicCompletion,
IsStrictlyHenselianLocalRing, RingHom.IsRegular" reported the unknown project identifier
`IsStrictlyHenselianLocalRing` and no hits; it is not used as negative mathematical evidence.
Mathlib grep "partialAlgebraization|partial_algebraization|Gabber" returned only BBD citations
in triangulated-category files. LeanSearch query "A complete normal local ring admits a
partial algebraization over a complete regular local ring of dimension one less." returned
formal-smoothness lifting and localization results, not the theorem. Direct rg searches of
WeilConjectures and lean/Sheaf for partial algebraization and the proposed declaration name
found no duplicate; the upstream blueprint-id grep also found none. Searches for dimension
functions found the landed `Scheme.IsGeometricDimensionFunction` declaration, which is reused. The
exact
searches were recorded by the prescribed wrapper. No new notion or node is created.

No statement correction or mathematical dispute is proposed; this repair updates the dependency
interface required by the returned H4 review. The repaired packet passes `scompile.py` (sandbox
2.7 s; library 2.2 s) and the required
`deliver2.py --no-push` preflight and compile (dry-run commit 368d9c1b07).

## Self-check by Q65

This is the dispatched worker's own self-check; independent maintainer review follows delivery.
I reopened the saved node and theorem, compared the current base node, read every statement
dependency's current record, and checked their actual definitions and signatures. The node deltas
are the Lean record and the replacement statement dependency
`def-per-geometric-dimension-function` requested by the H4 repair.
The stored signature equals the theorem signature verbatim, and its UTC date is 2026-10-18
as returned by `date -u +%F` on this machine. There is no maintenance repair note for this item.

The input binders retain normality, strict henselian locality, maximal-ideal completeness,
Noetherianity, excellence, prime invertibility, and dimension at least two. The conclusion
retains finite surjectivity and stalkwise normality, the complete regular excellent local
base of dimension d-1 with ell invertible, finite type of Z over that base, a geometric
point, and the actual strict-local completion isomorphism. The remaining conjuncts assert
Noetherian excellence of that strict localization, its integer-valued dimension function,
regularity of the canonical completion algebra map, and an isomorphism for the cover in
equal characteristic. Taking the cover isomorphism as the identification transports all
the witnesses to the identity cover. The dimension-function clause now uses the canonical
`Scheme.IsGeometricDimensionFunction`
without an inline copy; its definition has the same +1 direction for an immediate geometric
specialization and the required strict-local structural map. No copied notion or additional
mathematical hypothesis was found.

The current proof-dependency records now include three modules absent from the saved import
list: `Sheaf.RingTheory.CohenGabberFinitePresentations`,
`Sheaf.RingTheory.FiniteHenselianAlgebraLocalModel`, and
`Sheaf.RingTheory.WeierstrassHenselianCylinder`. I added their required proof-only imports;
the theorem and recorded signature now match the repaired canonical predicate. The remaining
unrecorded proof nodes
are Elkik descent, the regular strict-local model, and dimension-function calculus. Their
proof steps are already in the docstring. No new definition or dependency module is needed.


## Returned H4 repair

The immutable-head return identified that the prior packet at bf42a17bde6d retained the
inline `StrictGeometricPoint.IsImmediate` clause and was byte-identical to the earlier
returned packet. This packet changes the actual theorem: the conclusion is now exactly
`∃ δ : Scheme.strictHenselizationScheme z → ℤ,
Scheme.IsGeometricDimensionFunction (Scheme.strictHenselizationScheme z) δ`. Its public
import is `Sheaf.AlgebraicGeometry.GeometricDimensionFunction`, and its `stmt_deps` replaces
the old packet's `def-per-geometric-specialization-category` with the landed
`def-per-geometric-dimension-function`. The stored `lean.statement` was extracted verbatim
from the repaired theorem.

I read the complete landed definition and its docstring at GeometricDimensionFunction.lean:35,
and checked the corresponding uses in RegularDimensionFunctionPullback and
DimensionFunctionsStrictLocalization. They all use the same predicate, so the dimension
function delivered here is directly usable by the local-duality citer's Step 9. The
shared-base comparison confirms that only `lean` and `stmt_deps` differ; the latter only
gains the landed dimension-function definition relative to the base. There is no new node,
no dependency-node edit, and no mathematical statement correction. The input hypotheses,
remaining conclusion clauses, universe binder and proof docstring are retained. The saved
packet was dry-run checked before repairs; the returned fault was then repaired rather than
re-pushing that mechanically passing saved packet.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
