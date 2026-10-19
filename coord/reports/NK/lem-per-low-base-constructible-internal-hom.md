## Worker report

The module `Sheaf.AlgebraicGeometry.LowBaseConstructibleInternalHom` states
`AlgebraicGeometry.Etale.isBoundedConstructible_derivedHom_of_regular_base`, with `sorry`
as its sole proof. There are no new definitions, dependency repairs, or statement changes.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes S and X | `{S X : Scheme.{u}}`, for arbitrary explicitly declared universe u |
| S Noetherian | `[IsNoetherian S]` |
| S regular | `_hS : IsRegularScheme S`, the recorded predicate `IsLocallyNoetherian S ∧ IsRegular S`; stalkwise regularity alone is not substituted |
| Krull dimension at most one | `_hdim : topologicalKrullDim S ≤ 1`, in `WithBot ℕ∞` |
| Prime ell | `(ell : ℕ) [Fact ell.Prime]` |
| ell invertible on S | `_hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s)` |
| X → S | `(f : X ⟶ S)` |
| Separated | `[IsSeparated f]`, the diagonal is a closed immersion |
| Finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded conjunction |
| A = F_ell | `ULift.{u + 1} (ZMod ell)`; the lift is ring-isomorphic to the prime field and provides the coefficient universe required by the recorded small-etale category |
| Ordinary constant-A small-etale derived categories | `DerivedCategoryModule (ULift.{u + 1} (ZMod ell)) X`, definitionally `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} ...))` |
| Every M,N in D^b_c | Arbitrary `(M N : DerivedCategoryModule ... X)` with `_hM` and `_hN` in the recorded `DerivedCategory.isBoundedConstructible ... X` |
| Derived internal sheaf Hom | `((derivedHom (ModuleCat.{u + 1} ...) X).obj (op M)).obj N`, the recorded ordinary-etale specialization publicly imported by def-pur-derived-internal-hom |
| RHom belongs to D^b_c | `DerivedCategory.isBoundedConstructible ... X` applied to that exact object |
| No dualizing object, biduality, potential pinning, or purity hypothesis | The displayed binders are exhaustive; none of those structures or assumptions occurs |

The definition of bounded constructibility was read in full: all cohomology sheaves have a
finite locally closed constructible stratification with finite locally constant module values,
and vanish outside some interval [a,b]. Thus the conclusion includes both constructibility and
boundedness. The unbounded derived Hom is the right adjoint of derived tensor, supplied by
`Etale.derivedHom`; its dependency record explicitly lists that fixed-coefficient presentation.
No generic ringed-site copy is introduced. The recorded derived-category module was read using
`scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedCategories`; its primary
`torsionCohomology` is not needed, but its recorded `DerivedCategoryModule` is used.

Statement dependency declarations (the recorded modules are publicly imported):

- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsSeparated`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType and AlgebraicGeometry.QuasiCompact`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategoryModule`.
- `def-weil-pbc-constructible-complexes`: `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `AlgebraicGeometry.Etale.derivedHom (defined upstream in WeilConjectures.SixFunctors.Etale.Derived.Hom)`.

The theorem docstring contains all seven original proof steps, including each cited DAG
node. All proof dependencies with recorded Lean modules are imported privately unless already
publicly imported. The Mathlib long exact homology sequence and Noetherian-scheme modules are
also imported. `lem-per-low-base-open-sheaf-finiteness` currently has no Lean record, so it has
no import; it is a proof-only prerequisite, not an object needed to state this item.

Source check: read Zheng pp.18–20, including the assumptions before Propositions 3.15–3.16,
Proposition 3.15's regular dimension-at-most-one alternative and Proposition 3.14's finite-Tor
assertion. The finite field specialization has finite Tor dimension. The file retains the
node's independent Noetherian devissage, and uses no later dualizing result.

Edge cases checked before writing:

- Empty S is allowed (`topologicalKrullDim S = ⊥`); any X mapping to it is empty. The stalk
  invertibility condition is then vacuous for the correct mathematical reason.
- Empty X, zero M or N, and arbitrarily shifted bounded complexes are included. No cohomology
  interval, nonempty scheme, or positive-rank hypothesis is imposed.
- Dimension-zero regular bases (fields and finite disjoint unions) and dimension-one regular
  bases, including non-excellent DVRs, satisfy exactly the stated assumptions. There is no
  field-structure or quasi-excellence restriction.
- X can be singular or nonreduced; regularity is required only on S. No properness is assumed.
- Characteristic ell points of S are excluded precisely by stalk invertibility. Every other
  characteristic, including mixed characteristic where ell is invertible, remains allowed.
- The category uses site objects at u+1 and module values at u+1, with the finite coefficient
  ring lifted from Type 0. No equality of independently required site universes is imposed.

Searches (through the prescribed msearch.py, all returned successfully):

- LeanFinder: “Derived internal Hom of bounded constructible etale finite field sheaves over a
  regular noetherian base of dimension at most one is bounded constructible”. Eight results
  concern condensed monoidal structures, internal projectivity, and scheme module pushforward;
  none states this finiteness result.
- LeanSearch: “Derived internal Hom of bounded constructible etale complexes over a regular
  scheme of dimension at most one is bounded constructible”. Eight results are general derived
  categories, bounded representatives, smallness, and Ext, with no etale finiteness theorem.
- Loogle: `"derivedHom"`; zero results.
- Mathlib grep: `constructible.*[Hh]om|[Hh]om.*constructible`, subdirectory AlgebraicGeometry;
  three results in Morphisms/FinitePresentation about constructible images/preimages, not
  internal Hom of sheaves.
- Source and project rg: `low.base|regular.*[Bb]ase|constructible.*[Hh]om|[Hh]om.*constructible`,
  and a source search for the exact item id; no same statement. Read upstream
  `Etale.constructibleFiniteTor_derivedHom_of_isSeparated` (Derived/Dualizing.lean) and
  `Etale.boundedConstructible_derivedHom` (Derived/Stability/DirectImage.lean): both require
  finite type over a field and explicit Tor-amplitude bounds, so neither covers regular
  dimension-one bases. Project `WeilConjectures.finite_constructible_derivedHom_etale` similarly
  has finite-field base and extension-ring coefficient data; it is not this statement.
- Exact proposed name search across Mathlib/project/upstream found no preexisting declaration.

Validation: `scompile.py NK lem-per-low-base-constructible-internal-hom` on the delivered
module succeeded for both sandbox and final module name (3.3 s and 3.8 s), with no warnings
or errors. The needed live EtaleInternalHomLocalization overlay also compiled successfully.
All binders and universe variables are explicit (`set_option autoImplicit false`).
No node fault or STATEMENT-DISPUTED issue was found.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
