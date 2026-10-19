## Worker report

Defines `AlgebraicGeometry.Etale.HasConstructibleHigherDirectImages` in
`Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`. This is a complete
Prop-valued definition, with no theorem, proof, axiom or sorry added.

Source read: the whole blueprint definition
`sec-smooth-purity/sk-prop-sf-cbc/def-finrepair-property-c.md` (order 1592),
plus the surrounding `lem-finrepair-projective-from-line.md` and
`thm-dg-finite-type-constructibility.md`. The latter explicitly identifies the
finite-type schemes as schemes over a field k; the former uses the same
finite-type k-scheme setting in its hypotheses and projective-space argument.

Hypothesis and clause correspondence:

- A field k is explicit as `(k : Type u) [Field k]`, making the surrounding
  finite-type field context explicit without any separable/algebraically closed,
  characteristic or finiteness assumption on the field.
- The fixed finite commutative coefficient ring is `(Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ]`.
- The positive integer N, annihilation by N, and invertibility on both schemes
  are `(N : ℕ)`, `_hX : IsSmoothBaseChangeCoefficients N Λ X` and the same
  hypothesis `_hS` for S. The recorded coefficient definition unfolds to
  `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
  The separate Finite instance allows use of the recorded constructibility
  predicate; it repeats exactly the same finiteness requirement.
- The two finite-type schemes are `{X S : Scheme.{u}}` with their
  `Over (Spec (.of k))` structures and `LocallyOfFiniteType` and `QuasiCompact`
  instances on their structure morphisms. No separatedness, properness,
  nonemptiness or smoothness is required. The node names the morphism f,
  so it is the explicit argument `(f : X ⟶ S)`. No compatibility of f with
  the chosen structure morphisms is added: the node asks for a morphism
  between the finite-type schemes.
- Every q >= 0 is `∀ q : ℕ`; casting to ℤ covers exactly the nonnegative
  degrees of `higherDirectImage` and includes q = 0.
- Every Λ-module sheaf F is the binder
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
- The constructibility assumption on F is precisely
  `Scheme.IsConstructibleEtaleModuleSheaf F`, the predicate used by the
  recorded bounded constructible complexes module, not the older geometric
  stalk formulation `Scheme.IsConstructibleSheaf`.
- The conclusion is that same constructibility predicate applied to
  `higherDirectImage Λ f (q : ℤ) F`.
- No existential degree bound, vanishing, boundedness or uniformity condition
  appears in the definition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`,
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients` (full definition
  and docstring read).
- `def-weil-pbc-scheme-conventions` is explicitly a convention-only node;
  its lean record has null module and declaration. The finite-type convention
  is rendered with the Mathlib `LocallyOfFiniteType` and `QuasiCompact`
  classes that its record prescribes. The schemes and morphisms are Mathlib's.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar` (full signature, surrounding category
  variables and docstring read). The recorded derived declaration
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` is actually located in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`, whose
  full signature and docstring were read. No dependency replacement is needed:
  `higherDirectImage` in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` is exactly the
  existing degree-q homology of this derived pushforward of F in degree zero.
  Its complete definition and docstring were read and it is reused directly.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` (full
  definition and docstring read). This dependency supplies the sheaf notion
  through its public import of
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, whose complete
  declaration `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`
  and docstring were also read. The bounded complex predicate itself is
  intentionally not imposed on a single higher direct image.

Edge cases inspected: q = 0 is included, and arbitrarily large q remain
quantified independently. Zero sheaves, the zero coefficient ring, N = 1
when allowed by annihilation, and empty schemes are not excluded. N = 0
is correctly excluded by the coefficient convention. Finite-type schemes
need not be separated; neither they nor the morphism are required proper.
The universe of module values and coefficients is u + 1, as in all recorded
étale module-sheaf declarations; no smaller test universe is introduced.
Identity morphisms and maps from the empty scheme impose only the intended
constructibility clauses and no extra vanishing demand.

Searches actually run through msearch.py with this group and item:

- LeanFinder: `A scheme morphism whose higher direct images of constructible
  finite coefficient etale sheaves are constructible in every nonnegative degree`.
  Eight hits were constructible subsets, étale and finite-type morphisms,
  including `Scheme.Hom.isConstructible_image`; none defines this property.
- Loogle: `"Constructible", "rightDerived"`: zero hits.
- grep: `Constructible.*(Direct|Image)|constructible.*direct|PreservesConstructible`:
  eighteen hits, concerning constructible subsets and Chevalley, no matching
  module-sheaf property.
- LeanSearch: `Higher direct image preserves constructible etale module sheaves`:
  UNAVAILABLE, Internal Server Error. Not treated as a negative search result.

Direct rg searches in both the upstream WeilConjectures tree and project
lean/Sheaf for `PropertyC|propertyC|property_c|Constructible.*(Direct|Image)|constructible.*direct`
found only unrelated étale-topological-invariance PropertyC and existing
constructibility arguments. The upstream PropertyC at
`AlgebraicGeometry/Sites/EtaleTopologicalInvariance/PropertyC.lean:113`
is a different notion with arguments f, g, u, not constructible higher images.
`grep -rn def-finrepair-property-c` in upstream returned no hit.
`tools/lean_names_upstream.py show def-finrepair-property-c` produced no
attached declaration (only its index census). Searches for
`IsConstructibleHigherDirectImage|PreservesConstructible|IsConstructibleDirectImage`
and the chosen `HasConstructibleHigherDirectImages` in Mathlib, upstream,
project Lean and the upstream name index found no matching declaration.
The existing `Etale.higherDirectImage` was found by rg and reused, not copied.

Server validation: scompile.py compiled the module cleanly in 2.5 seconds,
nice 19, two threads, 60 seconds per file. No local compiler or library build.
No statement correction, disputed statement, new node or dependency module.


## Second reading by NG

Independently read the node and its full blueprint source paragraph (order 1592),
the surrounding projective reduction and finite-type constructibility theorem,
all four statement-dependency nodes, and the declarations and docstrings listed below.
The node cites a blueprint definition, not a Stacks tag; there is no separate
Stacks source paragraph imposing additional standing hypotheses on this definition.
The surrounding `lem-finrepair-projective-from-line` and
`thm-dg-finite-type-constructibility` explicitly use finite-type schemes over a field.

Object/hypothesis/clause checklist, in source order:

- Fixed finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]`. Verdict: exact, including the zero ring.
- Coefficient convention: `(N : ℕ)` and `_hX`, `_hS` of
  `IsSmoothBaseChangeCoefficients N Λ X/S`. Opened its complete definition:
  `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(T, ⊤))`.
  Verdict: the same positive annihilator and invertibility on each scheme;
  the explicit finite instance repeats the convention, adding no restriction.
- Schemes and finite-type context: `{X S : Scheme.{u}}`, `(k : Type u)
  [Field k]`, the two `Over (Spec (.of k))` instances, and
  `LocallyOfFiniteType` plus `QuasiCompact` on their structure maps.
  Verdict: finite type exactly as the convention node specifies, with the
  field context made explicit as in the surrounding source; no separatedness,
  properness, smoothness, algebraic closure or characteristic restriction.
- Morphism: `(f : X ⟶ S)`. Verdict: the source asks for a morphism between
  these schemes and does not impose an additional equation over k.
- All degrees q >= 0: `∀ (q : ℕ)`, passed as `(q : ℤ)`.
  Verdict: exact nonnegative degrees, including zero.
- Every constructible Λ-sheaf F: `F : Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)` and `Scheme.IsConstructibleEtaleModuleSheaf F →`.
  Verdict: precisely the recorded sheaf category and constructibility notion.
- Constructible R^q f_* F: the conclusion is
  `Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)`.
  Verdict: same predicate on the actual higher direct image.
- No uniform vanishing: the body contains just the preceding universal
  implication, with no bound or vanishing clause. Verdict: exact.

Dependency check: opened `Etale.lowerStar` in UpperLowerStar.Defs (arbitrary
scheme morphism; objectwise evaluation on the etale base change),
`Etale.rightDerivedLowerStarPlus` in Derived.UpperLowerStarCoherence
(the right derived functor of that same lowerStar on D+), and
`Etale.higherDirectImage` in SmoothBaseChange.Defs (homology in degree q
of that D+ pushforward applied to F in degree zero). Thus the helper uses
the recorded direct-image notion, not another pushforward. Opened
`DerivedCategory.isBoundedConstructible` and its imported
`Scheme.IsConstructibleEtaleModuleSheaf`: the latter is the finite locally
closed constructible stratification with finite constant module values.
The older `Scheme.IsConstructibleSheaf` is deliberately not substituted.
The scheme-conventions node defines no separate declaration; its prescribed
Mathlib classes are used directly. No unusable dependency, missing notion,
new node or dependency module was found.

Edge cases: q = 0 and every arbitrarily large degree are included; there is
no negative-degree claim. Empty source/target schemes and zero sheaves are
not excluded. The empty stratification is permitted by the imported
constructibility notion. There is no index set or n in this definition.
N = 0 is excluded by the stated positive-integer convention, while N = 1
and the zero coefficient ring are allowed when the convention holds.
No extra characteristic condition appears. Scheme universe u and module
universe u + 1 match the recorded dependency signatures; no independent
smaller test universe is introduced. All variables and universes are bound.

Independent searches, with wording different from the author's:

- msearch LeanFinder: `All positive derived pushforward functors carry finite
  stratified locally constant module sheaves to constructible sheaves`:
  eight hits about condensed locally constant modules and sheaf construction,
  none about this property of etale higher direct images.
- msearch Loogle: `"higherDirectImage"`: zero hits.
- msearch grep: `([Cc]onstructib.*[Pp]ushforward|[Pp]reservesConstructib|
  [Hh]igherDirectImage)`: zero indexed hits.
- Direct rg on Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `HasConstructibleHigher`, `Preserves.*Constructib`, `Constructib.*higher`,
  `higher.*[Cc]onstructib` and `PropertyC` variants. Opened the candidate
  `Scheme.PropertyC` in EtaleTopologicalInvariance/PropertyC: it asks for
  an affine etale local lifting at a point and is unrelated. Opened the
  finiteness DirectImage module's declarations: these are theorems about
  bounded constructibility for particular morphisms or the older stalk
  predicate, not this predicate definition. The already existing
  `higherDirectImage` is reused. Upstream-name lookup for this blueprint
  id yielded no attachment. No duplicate definition found.

No mismatch found; no Lean or node changes were needed. The existing module
and declaration docstrings name the source and blueprint id; this definition
has no proof steps to transcribe. There is no sorry, theorem, hollow data,
local notation, local instance or private declaration. The node's
`lean.statement` was checked byte-for-byte against the file signature.
Validation uses only the mandated server scompile.py, followed by deliver2.py.
