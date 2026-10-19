## Worker report

The delivery states `lem-per-regular-pair-alteration-pullback` in
`Sheaf.AlgebraicGeometry.RegularPairAlterationPullback`. There are three postponed
statements, all with `sorry`: `regular_pair_alteration_pullback`,
`excellent_local_completion_isRegular`, and `excellent_stalk_completion_regular`.
The first two declarations construct the identity object in the published alteration
category and its structural arrows. Their data are actual categorical constructions;
no new category, topology, boundary definition, or regularity predicate is introduced.
The existing node is changed only in `lean`.

The preceding worker's supersession diagnosis concerned the reviewed stage-1 split.
This dispatch is stage 2: the reviewed node has no Lean record. Its statement and
reviewed split are retained verbatim.

Clause-by-clause reading:

- The schemes `S`, `S'` are arbitrary `Scheme.{u}`; `[IsNoetherian S]` and
  `[IsNoetherian S']` express Noetherianity, and both `[IsReduced ...]` hypotheses
  express reducedness. `g : S' ⟶ S` is the given morphism, with `[Flat g]`.
- `hreg` quantifies over every point `s`, every field `L : Type u`, every
  `Algebra (S.residueField s) L`, and finite such extension. The tested object is
  the ordinary fibre `g.fiberToSpecResidueField s` pulled back by the spectrum
  of this algebra map. `IsRegularScheme` includes local Noetherianity and all
  regular local stalks. The identity field extension is included; no finite-type
  assumption on `g` or equality of separate universes is introduced. This is
  the explicit finite-extension convention already used by
  `RegularEtaleDirectImageBaseChange` and `RegularStrictLocalModel`.
- `ell : ℕ`, `[Fact ell.Prime]`, and `hinv : ∀ s, IsUnit (ell : S.presheaf.stalk s)`
  express the invertible prime. There is no extra invertibility assumption on `S'`.
- `I : Type w` and `[Finite I]` express an arbitrary finite index set, independently
  of the scheme universe. `R : I → Alt S` uses the recorded category: its object
  property includes finite type, reducedness, maximal dominance and finite generic
  residue-field extensions. The morphism `q_i` is `(R i).obj.hom`.
- `baseObject S` has underlying object `Over.mk (𝟙 S)` and `toBaseObject (R i)`
  has underlying morphism `q_i`. `hcover` is exactly the recorded
  `IsCoveringFamily ell` for these arrows, not joint topological surjectivity.
- `hR` gives Noetherianity and `IsRegularScheme` for every source. `hnoeth`
  gives Noetherianity for the ordinary chosen products `pullback q_i g`, precisely
  the stated hypothesis. The parenthetical finite-type sufficient condition is
  already available from the finite-type object property and the Noetherian
  base-change instances; no additional hypothesis is imposed.
- The first conclusion gives regularity of every ordinary product. The second
  gives `R' : I → Alt S'`, equality of each underlying over-object with
  `Over.mk (pullback.snd q_i g)`, and covering by its structural arrows. The
  equality fixes both the scheme and the base map; arbitrary replacement objects
  cannot satisfy this conclusion. Finiteness is the original `Finite I`.
- The boundary clause quantifies over all closed subsets
  `Z : TopologicalSpace.Closeds S` with `IsNowhereDense (Z : Set S)`. Its antecedent
  gives an ideal sheaf `H` on each `R_i` satisfying the published
  `IsStrictNormalCrossingsBoundary H` and exact set support `q_i ⁻¹' Z`.
  Its conclusion gives such an `H'` on each ordinary product, with support exactly
  `(pullback.snd q_i g) ⁻¹' (g ⁻¹' Z)`. Thus it is the inverse-image support of
  the specified `g⁻¹Z`, without choosing a smaller boundary or discarding components.
- The final completion sentence is recorded by two additional theorems under the
  same DAG id. For any local commutative ring `A`, `IsExcellent A` includes its
  Noetherianity. `excellent_local_completion_isRegular` says that the canonical
  `algebraMap A (AdicCompletion (maximalIdeal A) A)` is `RingHom.IsRegular`.
  For a Noetherian scheme `S` with excellent affine coordinate rings, every `s`
  gives its actual stalk and maximal-ideal completion. The second completion
  theorem gives flatness and all finite-extension regular-fibre tests for
  `Spec.map (algebraMap O_s (completion O_s)) ≫ S.fromSpecStalk s`. This includes
  localization before completion, over the original scheme, and does not treat
  completion as a finite-type alteration object.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms.
- `def-pc-reduced-scheme` and `def-pc-integral-scheme`:
  `Mathlib.AlgebraicGeometry.Properties`, `IsReduced` and `IsIntegral`.
  Integrality of boundary components is supplied by the recorded boundary predicate.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; scheme Noetherianity is `Mathlib.AlgebraicGeometry.Noetherian`,
  `IsNoetherian` (finite affine cover equivalence read).
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`;
  `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing`, `RingHom.IsRegular`,
  `Algebra.IsGeometricallyRegular`, `IsGRing`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme` (locally Noetherian and regular stalks),
  reusing upstream `WeilConjectures.AlgebraicGeometry.Regular.IsRegular`
  (declaration namespace `AlgebraicGeometry.IsRegular`).
- `def-trf-strict-normal-crossings-boundary`:
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`,
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `def-per-prime-to-ell-alteration-topology`:
  `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`,
  `PrimeToEllAlteration.Alt`, `topology`, and `IsCoveringFamily`.
- The proper, finite type, and finite/integral morphism dependency signatures were
  read in Mathlib `Morphisms.Proper`, `Morphisms.FiniteType`, `Morphisms.QuasiCompact`,
  `Morphisms.Finite`, and `Morphisms.Integral`: `IsProper`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsFinite`, `IsIntegralHom`. They are used by the published alteration
  category/topology, not replaced by copies or extra assumptions.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`; scheme fibre construction is Mathlib
  `AlgebraicGeometry.Fiber`, `Scheme.Hom.fiberToSpecResidueField`.
- `def-weil-pbc-adic-completion`: Mathlib `RingTheory.AdicCompletion.Basic` and
  `Algebra`, `AdicCompletion` and its canonical `algebraMap`.
- `def-weil-pbc-localization-at-prime`: Mathlib `Localization.AtPrime.Basic`,
  `Localization.AtPrime`, plus `Ideal.ResidueField` and `Ideal.Fiber` in
  `LocalRing.ResidueField.Ideal` and `Fiber`; the canonical scheme localization is
  `Scheme.fromSpecStalk` from `Mathlib.AlgebraicGeometry.Stalk`.

All available proof-dependency modules are imported. The two new stage-1 proof
prerequisites `lem-per-alteration-generators-reduced-base-change` and
`lem-per-snc-boundary-parameter-criterion` currently have no Lean record and are not
imported. They are needed for proofs, not for the present signatures. No dependency
module or new definition node is needed to state this item.

Sources and edge cases:

ILO IX 1.3, printed p.132 (arXiv:1207.3648 PDF page 138), was opened and read:
its excellent completion map is regular and its base change preserves regularity,
normal crossings divisors and alteration coverings. The module follows the expanded
six-step proof already in this node, including the generated-sieve argument and local
parameter proof. The local definitions and comparison declarations above were read in
full, including their docstrings. No mathematical correction was needed.

The index type can be empty; then the source covering hypothesis still has its actual
generated-sieve meaning. The empty base and empty product schemes are allowed. The
boundary predicate allows zero components, so `H = ⊤` represents the empty boundary;
`Z = ∅` is admitted, and the conclusion retains empty inverse images. No connectedness
or integrality of all `R_i` is imposed. Splitting boundary components after base change
is allowed because the conclusion asks for the published boundary predicate, whose
components are not fixed in advance. Dimension zero and zero parameters are included.
Residue characteristic equal to `ell` is excluded exactly by `hinv`; other
characteristics, the identity map, field identity extension, non-surjective regular maps,
and completion maps which are not finite type are included.

Searches (all on this item, outputs retained in sandbox `searches.jsonl`):

- LeanFinder: "Regular base change of Noetherian schemes preserves regular alteration
  covering pairs and strict normal crossings boundaries": eight hits, including smooth
  base-change stability and valuative criteria; none states the alteration/boundary claim.
- Loogle: "IsRegularRing, AlgebraicGeometry.Flat, AlgebraicGeometry.IsRegular": no hits;
  the upstream-only last identifier was unknown to Loogle. Local source inspection
  resolved it as the stalkwise regular-scheme class, not a scheme-morphism theorem.
- LeanSearch: "Regular morphisms preserve regular schemes and strict normal crossings
  divisors under base change": eight hits, about category regular epis, regular
  sequences, smoothness and universal closedness; none is this statement.
- msearch grep: "regular.*alteration|normal.?crossing|geometrically.?regular" in
  Mathlib AlgebraicGeometry: zero hits.
- `rg` for the item id in upstream `WeilConjectures`: no hits. Source and side-library
  searches for regular morphisms/normal crossings/geometric regularity located the
  boundary, ring regularity and neighboring finite-extension fibre-test interfaces
  described above. No whole-item match was found. Exact searches for all five proposed
  fully qualified declaration names found no existing declarations in Mathlib, upstream,
  or the side library (other namespaces' `baseObject` are unrelated).

Validation: the prescribed `scompile.py` compiled both the sandbox and real module
names cleanly. Initial elaboration errors in the identity object and nowhere-dense name
were repaired; there is no changed mathematical statement and no disputed assertion.

## Second reading by Q44

Author's separate second pass, not a claim of independent review (the dispatched brief
forbids sub-agents; the maintainer supplies independent review). I reread the node with
all declarations open. I checked the two reduced Noetherian bases, arbitrary regular
map tested after all finite extensions including the identity, invertible prime, finite
covering family in the specified topology, ordinary fibre products, and exact support
of `g⁻¹Z`. The over-object equality fixes the chosen ordinary product and its map, so
there is no arbitrary replacement in the covering clause. I also checked that both
parts of the completion sentence appear, through the canonical stalk localization map,
and that no finite-type condition is placed on `g` or completion. I repaired only
elaboration details in the concrete identity alteration object. No clause mismatch,
new hypothesis, new node, dependency-interface repair, or statement correction remains.
