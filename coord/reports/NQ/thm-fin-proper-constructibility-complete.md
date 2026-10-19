## Worker report

The module `Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages` states
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_proper`. Its only theorem
has proof `sorry`; there are no new definitions or additional nodes. The item JSON changes
only in `lean`. No statement correction or disputed statement was needed.

Hypothesis and conclusion correspondence:

- The field `k` is `(k : Type u) [Field k]`, with explicit universe `u`.
- Schemes of finite type over `k` are `{X S : Scheme.{u}}`, their instances
  `[X.Over (Spec (.of k))]` and `[S.Over (Spec (.of k))]`, and
  `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]`
  and the corresponding two instances for `S`. This is precisely the finite-type
  convention in `def-weil-pbc-scheme-conventions`, not finite presentation or properness
  over the field. No Noetherian, reduced, affine or separated-over-the-field hypothesis
  is imposed.
- Every proper morphism is `(f : X ⟶ S) [IsProper f]`. Mathlib's `IsProper` extends
  separatedness, universal closedness and local finite type; universal closedness implies
  quasi-compactness, giving the finite-type properness convention. The statement does
  not impose an additional compatibility condition on the selected field structures:
  the node says every proper morphism between these schemes. The argument also covers
  that formulation: the modification is finite type over `k` via its projective map to
  `S`, and the reduced closed subschemes are finite type via `X`.
- The coefficients implicit in `C(f)` are bound as `(N : ℕ)` and
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, with
  `hX : IsSmoothBaseChangeCoefficients N Λ X` and the corresponding `hS`.
  These are the exact required binders of the recorded property-C dependency, using
  the same positive annihilator and invertibility convention on both schemes. Its
  definition says `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
- The conclusion is exactly `HasConstructibleHigherDirectImages k N Λ hX hS f`.
  Reading the dependency's actual body, this quantifies over all `q : ℕ` and
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, assumes
  `Scheme.IsConstructibleEtaleModuleSheaf F`, and concludes the same constructibility
  predicate for `higherDirectImage Λ f (q : ℤ) F`. Thus degree zero and every positive
  degree are included, with no common bound or vanishing conclusion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`,
  `AlgebraicGeometry.Etale.HasConstructibleHigherDirectImages`: the complete recorded
  signature, docstring and body were read and imported publicly. Its underlying
  coefficient predicate was read in `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`.
- `def-weil-pbc-scheme-conventions` has a convention record, with no declaration or
  module of its own. Its complete statement and record were read. Scheme, `Over`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsProper` and `Spec` use the imported canonical
  definitions; the full `IsProper` declaration was read in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.

The module additionally imports the recorded proof-dependency modules: Mathlib
`AlgebraicGeometry.Noetherian` (finite-type Noetherianness, quasi-separatedness and
minimal closed subsets), `AlgebraicGeometry.ZariskisMainTheorem` (closed immersion
properness), and the recorded modules `BoundedConstructibleComplexes`,
`ConstructibleEtaleModuleQcqsAffineLocal`, `EtaleInverseImageModulesExact`,
`ReductionUniversalHomeomorphism`, `UniversalHomeomorphismInvariance`,
`EtaleModuleEnoughInjectives`, upstream `AlgebraicGeometry.Morphisms.Projective`, and
`SixFunctors.Etale.UpperLowerStar.Defs`. These imports are ordinary imports because they
serve the proof plan. The proof-only nodes `lem-weil-pbc-derived-open-restriction`,
`lem-fin-noetherian-chow-modification`, `thm-fin-projective-constructibility-complete`
and `lem-finrepair-modification-c` have no recorded module on this base; they are
therefore not imported or duplicated. They are not prerequisites for stating this
predicate. The theorem docstring carries all six DAG proof steps and their citations.

Edge cases checked before writing:

- Empty source and target schemes are allowed; the statement requires no nonemptiness.
  The empty closed subset starts the induction, and zero direct images are constructible.
- `q = 0` is included by the existing predicate's `ℕ` binder; negative degrees are not
  asserted. No uniform cohomological bound is inserted.
- The identity and finite proper maps are allowed. No positive dimension, surjectivity,
  projectivity or reduction hypothesis is imposed.
- The zero coefficient ring is allowed. `N = 1` is allowed when it annihilates the ring;
  `N = 0` is excluded precisely by the existing coefficient convention, not by a new
  assumption. No fixed characteristic is imposed beyond that convention.
- `Λ : Type (u + 1)` and the sheaf coefficients `ModuleCat.{u + 1} Λ` match the recorded
  small-etale coefficient interface. All universes and variables are explicitly bound;
  `set_option autoImplicit false` enforces that locally as well.

Searches for an existing theorem:

- `msearch.py ... leanfinder`, query “Higher direct images of constructible finite
  coefficient etale sheaves under a proper morphism of finite type schemes over a field
  are constructible”: eight hits, all about constructible subsets, spectra or limits;
  none states constructibility of higher direct-image sheaves.
- `msearch.py ... loogle`, query `AlgebraicGeometry.IsProper, "constructible"`:
  zero hits.
- `msearch.py ... grep`, query
  `constructible.*(proper|directImage)|proper.*constructible`: zero Mathlib hits.
- `msearch.py ... leansearch`, query “Higher direct images of constructible etale module
  sheaves by proper morphisms are constructible”: unavailable, Internal Server Error.
- `rg -n` with the above pattern and `HasConstructibleHigherDirectImages` in the upstream
  `WeilConjectures` sources and project `lean/Sheaf`: constructible-set results, curve
  special cases, bounded-complex direct image, and the canonical property C and
  cancellation/projective-from-line declarations. None states this theorem.
- `grep -rn thm-fin-proper-constructibility-complete` in upstream `WeilConjectures`:
  no hits. Exact-name `rg` for `hasConstructibleHigherDirectImages_of_proper` across
  Mathlib, upstream and `lean/Sheaf`: no hits before writing.

Validation: `scompile.py NQ thm-fin-proper-constructibility-complete` compiled the
single delivered module on the server cleanly, with no errors or warnings. No local
compiler or library build was run. The required delivery dry run is the final check.


## Second reading by NQ

Independently read the item JSON, all six proof steps, the original blueprint statement
and proof at sec-smooth-purity/sk-prop-sf-cbc/thm-fin-proper-constructibility-complete.md,
the property-C node and its actual declaration body, scheme-conventions node, and the
coefficient-conventions blueprint and Lean predicate. The item's source is this blueprint,
not a Stacks theorem with an additional blanket assumption. Its coefficient convention
fixes a positive annihilator invertible on every scheme carrying coefficients.

Object/hypothesis/conclusion checklist (all verdicts: exact):

- The ambient field k: `(k : Type u) [Field k]`; no algebraic-closure, perfectness,
  characteristic, or finiteness assumption.
- Schemes X and S over k: `{X S : Scheme.{u}}`, `[X.Over (Spec (.of k))]` and
  `[S.Over (Spec (.of k))]`. Both are finite type: the two respective
  `LocallyOfFiniteType` and `QuasiCompact` instances on their structure morphisms.
  Read the convention node: this is its finite-type convention; neither finite
  presentation nor separatedness over k is added.
- A proper morphism between them: `(f : X ⟶ S) [IsProper f]`. Read Mathlib's
  Morphisms/Proper.lean: separated, universally closed, locally finite type;
  universal closedness supplies quasi-compactness. No projectivity, surjectivity,
  reducedness, or nonemptiness is assumed. The literal node and original blueprint
  say every proper morphism between these schemes. The Lean accordingly does not
  require compatibility of the independently selected k-structures. Although the
  expanded proof's first sentence calls it a k-morphism, the remaining argument
  also works without that condition: each closed subscheme is finite type via X,
  and the projective modification is finite type via S. No statement repair needed.
- Finite allowable coefficients implicit in C(f): `(N : ℕ)`,
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, and
  `hX : IsSmoothBaseChangeCoefficients N Λ X`, `hS` on S. Read its body:
  `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
  Thus the binders spell out exactly the inherited source convention.
- Conclusion: `HasConstructibleHigherDirectImages k N Λ hX hS f` from the recorded
  public import ConstructibleHigherDirectImages. Its body is forall `q : ℕ`, forall
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, constructibility of F
  implies constructibility of `higherDirectImage Λ f (q : ℤ) F`, using the same
  recorded `Scheme.IsConstructibleEtaleModuleSheaf` on both sides. This is all of
  C(f), without a bound, extra vanishing, or a restriction to locally constant F.

Edge cases: q=0 is included; the theorem does not assert negative degrees. Empty
schemes and zero sheaves are allowed, with no nonempty index or positive dimension
binder. The zero coefficient ring is allowed, N=1 is allowed, and N=0 is excluded
only by the inherited positive-annihilator convention. All characteristics allowed
by invertibility are covered. The single scheme universe u and coefficient universe
u+1 match the dependency interface and small-etale convention; no extra universe
equality or typeclass is introduced. All variables and universes are bound, and
`autoImplicit false` is set. The node signature was checked byte-for-byte against
the theorem signature before `:= by` and matches.

Independent H4 searches: ran msearch.py leanfinder with the new query
“Proper pushforward of finite locally constant stratified etale module sheaves has
constructible cohomology in every nonnegative degree”. Eight hits concern condensed
locally constant module functors and sheaf constructions; none states this theorem.
Also searched Mathlib/AlgebraicGeometry, upstream WeilConjectures, and project
lean/Sheaf with `proper.*(constructib|higherDirect)`, `constructib.*proper`, and the
exact proposed name. Opened upstream SixFunctors/Etale/Derived/Finiteness/DirectImage:
its finite-type theorem has k-compatibility, derived bounded-constructibility, and
the upstream constructibility predicate, so it is not an exact declaration of this
node. Opened project's ProperBoundedConstructible: it also has a compatibility
hypothesis and a bounded-complex conclusion, not this predicate. Opened
BoundedConstructibleComplexes to check its recorded constructibility encoding;
the property-C body uses that canonical encoding, not a private duplicate.
The worker's Loogle and grep records give the other search kinds; the independent
new LeanFinder and source search confirm their no-exact-match verdict.

H5/H6/H8/H9: no new definitions or sibling/dependency nodes to review. Exactly one
theorem with `by sorry`; nothing proved. Module and theorem docstrings identify
the source and blueprint id. The theorem docstring retains each of the six node
proof steps, including affine locality, minimal bad reduced closed subset, Chow
modification, complement transfer, and injective-resolution passage from reduction.
Imports include the available recorded proof-dependency modules; absent proof-only
modules are not prerequisites to stating the theorem. No file-local notation,
private copy, hidden let, or new axiom appears.

Mismatches found: none. Changes: appended this independent second reading only;
the correct Lean module and node were preserved. Validation: scompile.py NQ
thm-fin-proper-constructibility-complete compiled the sole delivered module on the
server (60-second per-file default) cleanly, with no error or warning. No local
compiler or library build was used.
