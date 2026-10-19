## Worker report

The module `Sheaf.Paper.PullbackTorAmplitude` states the unchanged finite-stage
pullback assertion and its stated consequence. Both theorems have `sorry` proofs.
`sfFiniteDerivedPullback` is a public specialization of the existing canonical
ringed-site operation, not a new pullback construction. Its data are the existing
`proEtaleRingDerivedPullback` with the canonical constant-section coefficient
isomorphism. The three declarations are listed in the item's Lean record.

Hypothesis and clause correspondence:

- The global finite-field datum is `D : FiniteFieldDatum.{u}`. The base field is
  its fixed algebraic closure `D.k`, exactly the global k of the six-functor setting.
- The prime ell is `l : ℕ` with `[Fact l.Prime]`; ell different from p is
  `_hl : l ≠ D.p`. The coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
- Positive coefficient level is `(n : ℕ) (hn : 1 ≤ n)`. The coefficient ring in
  every category and predicate is the existing `Padic.coefficientExtensionRing l E n`,
  namely O_E/(varpi_E^n), with the recorded uniformizer. No other coefficient ring
  is substituted. The ULift in the constant ring sheaf is the recorded size convention.
- The finite-type k-schemes are `X Y : Over (Spec (CommRingCat.of D.k))` with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` and the same two instances on Y.
  `f : X ⟶ Y` includes its compatibility with the two structure maps.
- Separatedness is `[IsSeparated f.left]`; finite type of f is
  `[LocallyOfFiniteType f.left] [QuasiCompact f.left]`. No separatedness of X or Y
  over k, smoothness, properness, dimension bound or flatness assumption is added.
- K is an object of the actual recorded constant-ring small pro-etale category
  `proEtaleDerivedCategory Y.left (Padic.coefficientExtensionRing l E n)`.
- Membership in Dᵇ_c(Y,A) is `hK : intrinsicFiniteTorsionConstructible l E n hn Y.left K`.
  This recorded predicate means finite support of cohomology and intrinsic
  constructibility of each cohomology sheaf; it does not assume etale origin.
- The integers a and b are explicit. The assumption `hTor : HasProEtaleTorAmplitude ... K a b`
  includes a ≤ b and tests every module sheaf placed in degree zero using the recorded
  derived tensor. Thus neither the ordered-interval condition nor the universal test
  sheaf quantifier is lost.
- Lf* K is `(sfFiniteDerivedPullback l E n hn f.left).obj K` throughout.
  The first conjunct of `sf_pullback_torAmplitude` asserts intrinsic bounded
  constructibility on X. The second asserts `HasProEtaleTorAmplitude` with exactly
  a and b, with no shift or enlarged interval.
- The consequence is `sf_pullback_finiteTorConstructible`, with hypothesis
  `finiteTorConstructible l E n hn Y.left K` and the identical predicate on the
  pullback on X. The recorded predicate is bounded constructibility intersected
  with existence of one finite Tor interval. Preservation of this object property
  expresses carrying the full Dᵇ_ctf subcategory into the full Dᵇ_ctf subcategory.

Dependency declarations used:

- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` (reexported by
  `Sheaf.Paper.FiniteTorAmplitude`). Its original finite-field-dependent version is
  not copied or reintroduced.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude` and
  `AlgebraicGeometry.Scheme.HasFiniteProEtaleTorAmplitude`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `AlgebraicGeometry.Scheme.proEtaleRingDerivedPullback`,
  `proEtaleRingModulePullback` and its exact termwise descent. This interface is
  publicly reexported by the currently recorded operations dependency.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRing`,
  `proEtaleCoefficientInverseImageMap` and `proEtaleSheafInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientCommRingMap_isIso` gives invertibility
  of that precise canonical map. It is applied explicitly to the canonical ULift
  of A with its discrete topology. The topology is internal to the proof of
  invertibility; the constant CommRingCat sheaf and its canonical map contain no
  topology data and are unchanged. Finiteness is supplied by the existing
  `Padic.finite_coefficientExtensionRing l E n hn`.
- The convention node `def-weil-scheme-morphism-properties` explicitly declares no
  notion of its own. The finite-type notions are Mathlib `LocallyOfFiniteType` and
  `QuasiCompact`, and separatedness is Mathlib `IsSeparated`.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.

The umbrella dependency `def-weil-derived-pullback-tensor-hom` has no Lean record.
Its finite pullback clause is already the recorded ringed-site operation above,
with the canonical constant coefficient map from its existing prerequisites.
There is therefore no absent operation needed by this finite-only statement.
The public helper merely supplies those recorded arguments; no new notion or
arbitrary coefficient identification is assumed. The landed operations,
inverse-image and constant-exactness nodes were added to `stmt_deps` to make this
use explicit. No unused integral, rational or common-stage operation is asserted
or replaced by a placeholder in this delivery.

Proof dependencies imported for stage 3: `Sheaf.Paper.FiniteCoefficientFlatModel`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`, `Sheaf.Paper.KFlatRingedToposPullback`,
and `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`; the derived-tensor and
coefficient-extension definitions are reexported by the statement imports.
`lem-weil-pbc-standard-quotients-perfect` has no recorded module to import.
The recorded module for `lem-weil-pbc-pullback-preserves-bounded-constructible`,
`Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`, was tried as a proof-only
import. Both local compilation and server confirmation reject its existing import
closure: legacy `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` and the
new `FiniteCoefficient.UpperLowerStar.Defs` both declare the pro-etale lower-star
notation. The unnecessary proof-only import is omitted from this statement file,
retaining the finite-coefficient interface needed by its actual signature. Its
mathematical use remains fully described in the theorem proof docstring.

Sources and edge cases: read the full node, all five original statement-dependency
nodes and their available declarations/docstrings, plus the unit
`dag/units/sk-prop-sf-rf-shriek-preservation.json`. The literature/blueprint source
path is absent from this checkout, so I read the exact blueprint Markdown source
through a read-only server command. Its statement agrees verbatim with the node;
its proof gives the bounded-flat-model and inverse-image tensor calculation.
Checked n=1, a=b, zero K, empty source/target schemes, the identity morphism,
and non-smooth/non-flat morphisms. No nonemptiness or positive dimension binder
excludes an empty scheme. Positive n excludes n=0 exactly as in the node. The
characteristic restriction is retained. HasProEtaleTorAmplitude already includes
a≤b, so reversed intervals are not silently admitted. Both sites keep object
universe u+1 and morphism universe u; no equality of those universes is imposed.
All variables and universe u are explicitly bound, with autoImplicit disabled.

Searches made (2026-10-16):

- `msearch.py leanfinder`, query “Derived pullback of bounded constructible pro-etale
  complexes preserves finite Tor amplitude in the same interval”: eight hits,
  including etale base-change instances, DerivedCategory.isGE_Q_obj_iff and Tor
  vanishing for projectives; none is this theorem.
- `msearch.py loogle`, query `HasProEtaleTorAmplitude, proEtalePullback`: zero hits;
  the service reports unknown identifier HasProEtaleTorAmplitude.
- `msearch.py grep`, query
  `torAmplitudeIn_leftDerivedUpperStar|constructibleFiniteTor_leftDerivedUpperStar`:
  zero Mathlib hits.
- `msearch.py leansearch`, query “Derived pullback preserves finite Tor amplitude”:
  service unavailable, Internal Server Error; no results or negative verdict inferred.
- `rg` of Mathlib, upstream WeilConjectures, and lean/Sheaf for the theorem and
  pullback/Tor names: upstream ProEtale/Derived/Stability.lean has
  `AlgebraicGeometry.ProEtale.torAmplitudeIn_leftDerivedUpperStar`, but requires
  an explicit PreservesFlat instance and uses fixed-coefficient sheaves rather
  than this node's intrinsic constant-ring category. The etale versions in
  Etale/Derived/Stability/Basic.lean use the etale site, and its finite-Tor version
  also requires UpperStarPreservesFlat. None states the unchanged node exactly.
- `rg`/node-record searches located the existing canonical ringed-site operation,
  constant coefficient comparison, intrinsic constructibility and finite-Tor
  predicate, all reused. Searches for the three proposed full names in Mathlib,
  upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no duplicate.
- Server-source check for `Sheaf.Paper.DerivedPullbackTensorHom`: source unavailable.
  Read-only enumeration of delivery branches found no derived-pullback-tensor-hom
  or pullback-tor-amplitude delivery to reuse.

No statement correction, new node or statement dispute. The only recorded library
fault is the proof-only legacy import collision described above. Validation uses
only scompile.py and the required deliver2.py dry run; no global build or live
source edit is performed.

## Second reading by NE

I read the node statement, its source place (blueprint order 2064), the unit
statement, and the declarations recorded by every statement dependency. The
correspondence is as follows.

- The global datum is `D : FiniteFieldDatum.{u}`, with base field `D.k` and
  characteristic `D.p`; the Lean binder `_hl : l ≠ D.p` is exactly the source's
  condition ℓ ≠ p.
- The coefficient data are `l : ℕ` with `[Fact l.Prime]`, `E : Type u` with
  `[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, and
  `n : ℕ` with `hn : 1 ≤ n`. Every coefficient occurrence uses the recorded
  `Padic.coefficientExtensionRing l E n`; no alternate quotient or coefficient
  level is introduced.
- `X Y : Over (Spec (CommRingCat.of D.k))` and the four structure-morphism
  instances express finite-type k-schemes (`LocallyOfFiniteType` and
  `QuasiCompact` on `X.hom` and `Y.hom`). The morphism `f : X ⟶ Y` has exactly
  separatedness and finite type (`IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` on `f.left`). No properness, smoothness, flatness, dimension,
  or extra scheme hypotheses occur.
- `K` is an object of the recorded small pro-etale derived category on `Y`.
  `hK : intrinsicFiniteTorsionConstructible ... Y.left K` renders the source's
  bounded constructibility condition, and `hTor : HasProEtaleTorAmplitude ... K a b`
  renders Tor amplitude in the explicit ordered interval `[a,b]`, including the
  universal degree-zero module-sheaf tests. The conclusion is the conjunction of
  the same intrinsic constructibility predicate on `X` and the same interval
  `a,b` for `(sfFiniteDerivedPullback ... f.left).obj K`.
- The consequence theorem takes exactly `hK : finiteTorConstructible ... Y.left K`
  and returns the identical predicate for the pullback, which is the stated
  preservation of `D^b_ctf`.

The helper `sfFiniteDerivedPullback` uses the canonical
`proEtaleRingDerivedPullback` and the canonical inverse-image coefficient map,
with the recorded finite-coefficient isomorphism. It therefore supplies the
`Lf*` construction named in the node and does not choose an arbitrary
coefficient identification. Its three declarations and both theorem statements
carry the source and `(blueprint: lem-sf-pullback-tor-amplitude)` docstrings.

I checked the empty index situation (there is no index binder), zero objects,
empty schemes, the identity morphism, `a = b`, the zero complex, non-smooth and
non-flat morphisms, `n = 1`, and the excluded `n = 0`. The source and target
scheme and coefficient universes remain respectively `u` and the recorded
`u+1/u` site sizes; no universe equality or nonemptiness assumption was added.
The `HasProEtaleTorAmplitude` dependency itself supplies `a ≤ b`, so the Lean
statement does not admit reversed intervals.

Searches were repeated with `msearch.py` LeanFinder, Loogle, LeanSearch, and
grep over Mathlib, upstream `WeilConjectures`, and `lean/Sheaf`. The only related
upstream result is the generic pro-etale `torAmplitudeIn_leftDerivedUpperStar`,
which requires a `PreservesFlat` instance and uses a fixed-coefficient sheaf
category; it is not this intrinsic finite-coefficient statement. No exact
pullback/Tor-amplitude theorem or duplicate helper exists.

The first reading's Lean file compiled cleanly with
`scompile.py NE lem-sf-pullback-tor-amplitude` (including the sandbox wrapper).
I found no mismatch between the corrected sandbox node and the Lean signatures;
the node copy already contains the necessary explicit statement dependencies
`def-weil-pbc-proetale-operations`, `def-weil-proetale-inverse-image`, and
`prop-weil-pbc-proetale-constant-exact`. No statement correction, new node,
dependency repair, or `STATEMENT-DISPUTED` flag is needed.
