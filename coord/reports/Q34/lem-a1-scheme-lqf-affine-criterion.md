## Worker report

The module `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteAffineCriterion` states
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_affine_criterion`, with its whole proof
`sorry`. No definition, helper node, dependency repair, or statement correction is needed.
The source was read in `literature/stacks-project/morphisms.tex`, the lemma labelled
`lemma-locally-quasi-finite-characterize` (Tag 01TK), including the preceding explanation
that a quasi-finite ring map is finite type and quasi-finite at all target primes.

Hypothesis and clause correspondence:

- The arbitrary morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`. There are no
  additional instances imposing finiteness, separation, or a Noetherian condition.
- Condition (1) is `f.IsLocallyQuasiFinite`, the recorded Stacks-style predicate, not
  Mathlib's different predicate `LocallyQuasiFinite`.
- The universal affine pairs in (2) are `∀ (A : X.Opens) (B : S.Opens),
  IsAffineOpen A → IsAffineOpen B → ∀ e : A ≤ f ⁻¹ᵁ B`. The last relation is exactly
  `f(A) ⊆ B`. The induced map on coordinate rings is `(f.appLE B A e).hom`.
- Finite type of this map is the existential witness
  `hft : (f.appLE B A e).hom.FiniteType`. This is the recorded `RingHom.FiniteType`.
  Its definition is `Algebra.FiniteType` for the ring map's `toAlgebra`, so the same
  witness supplies the explicit finite-type argument to `Algebra.IsQuasiFiniteAtPrime`.
- Quasi-finiteness at every prime is `∀ q : PrimeSpectrum Γ(X, A),
  @Algebra.IsQuasiFiniteAtPrime Γ(S, B) Γ(X, A) _ _
  (f.appLE B A e).hom.toAlgebra hft q`. Thus the algebra structure is the canonical one
  for this particular induced section map; no arbitrary map or algebra structure is used.
- Condition (3) existentially quantifies `J : Type u`, `B : J → S.Opens`,
  `I : J → Type u`, and `A : ∀ j : J, I j → X.Opens`. The target cover is
  `(⨆ j : J, B j) = ⊤`, and the source covers are
  `∀ j : J, (⨆ i : I j, A j i) = f ⁻¹ᵁ B j`.
- The witnesses `e : ∀ (j : J) (i : I j), A j i ≤ f ⁻¹ᵁ B j` supply the canonical
  restrictions; these containments already follow from the cover equalities and do not
  strengthen the condition. Each required local quasi-finiteness assertion is
  `(f.resLE (B j) (A j i) (e j i)).IsLocallyQuasiFinite`.
- The three conditions are equivalent by the conjunction of `(1) ↔ (2)` and `(1) ↔ (3)`.
  The coverings in (3) are arbitrary open coverings, without an affine requirement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  and `Spec.map`. Schemes, affine opens, and their section maps use Mathlib's existing API.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and its defining
  `IsQuasiFiniteAtPoint`. The full source and docstrings were read, also using
  `scompile.py --source Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` and its defining
  `Algebra.FiniteType` for `f.toAlgebra`.
- `WeilConjectures.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`;
  the current recorded upstream source was read with `scompile.py --source` because
  it is absent in the older source checkout. It is the identical declaration already
  available through the legacy `Sheaf.RingTheory.QuasiFiniteAtPrime` public import of
  `QuasiFiniteMorphism`. Importing both defining modules would duplicate the name, so
  this module uses that existing transitive import, without defining a second predicate.
- Proof imports preserve all stated proof inputs: `Mathlib.AlgebraicGeometry.AffineScheme`
  (`Scheme.isBasis_affineOpens`), and the recorded modules
  `Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs`
  (`Scheme.Hom.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber`),
  `Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`
  (`Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite`),
  `Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`
  (`Scheme.Hom.isLocallyQuasiFinite_resLE`), and
  `Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated`
  (`Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`). Their source signatures and
  docstrings were read. `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, supplying
  `locallyOfFiniteType_iff` for `lem-weil-pbc-lft-affine-pairs`, is already publicly
  imported by the statement dependency.

Edge cases checked before drafting: the empty source makes the pointwise predicate
vacuous, permits empty source covering indices, and makes the prime quantifier over the
zero coordinate ring empty while retaining its finite-type clause. The empty target
forces the source empty and allows an empty target cover. Empty opens are permitted in
all pairs and coverings. There is no nonempty-index, finite-cover, quasi-compact,
separated, Noetherian, or characteristic assumption. Cover indices in `Type u` suffice:
coverings can be chosen with at most one open neighbourhood per point of a `Scheme.{u}`;
this does not restrict the existence assertion or assume an additional size condition.

Searches made (all through the prescribed tools or read-only source search):

- `msearch.py leanfinder`: “A scheme morphism is locally quasi finite in the finite type
  sense iff every affine chart map is finite type and quasi finite at every prime,
  equivalently Zariski locally on source and target”. Eight hits, principally
  `AlgebraicGeometry.locallyQuasiFinite_iff`, `LocallyQuasiFinite.quasiFinite_appLE`,
  and `locallyOfFiniteType_iff`; none states this three-way equivalence for the recorded
  Stacks predicates.
- `msearch.py loogle`: `"LocallyQuasiFinite", "appLE"`. One hit,
  `AlgebraicGeometry.LocallyQuasiFinite.quasiFinite_appLE`, for Mathlib's different notion.
- `msearch.py grep`: `locallyQuasiFinite_iff|quasiFinite_appLE|isLocallyQuasiFinite`,
  subdirectory `AlgebraicGeometry/Morphisms`. Five hits in `QuasiFinite.lean`.
  Reading the class docstring confirms that Mathlib explicitly omits local finite type.
- `msearch.py leansearch`: “A scheme morphism is locally quasi finite iff affine chart
  maps are finite type and quasi finite at every prime”. Eight hits on the same Mathlib
  class and its generated constructors/criterion; no exact statement.
- `rg` for `IsLocallyQuasiFinite|isLocallyQuasiFinite_iff|locallyQuasiFinite_iff` in both
  `WeilConjectures/` and `lean/Sheaf/`: the project's definition, permanence lemmas, and
  dimension criterion exist, but no affine-and-cover criterion for its predicate.
- `grep -rn` for the item's ID in `WeilConjectures/`: no hits.
- `rg` for `SchemeLqfAffineCriterion|isLocallyQuasiFinite_iff_affine_and_cover|
  isLocallyQuasiFinite_affine_criterion` in Mathlib, upstream source, project source,
  and `dag/lean_names_upstream.json`: no collisions.

Validation: `scompile.py Q34 lem-a1-scheme-lqf-affine-criterion` compiled the delivered
file cleanly both as a sandbox module and under its library module path. No errors or
warnings were printed. The module binds its universe and all variables explicitly.
The declaration docstring records all four steps of the DAG proof. No statement fault
or disputed statement was found.

## Second reading by Q34

I independently read the item node, Tag 01TK in `literature/stacks-project/morphisms.tex` (lines 3838--3890), every statement dependency, and the delivered module. The source has (1) local quasi-finiteness, (2) quasi-finite section maps on every affine pair, and (3) open target and inverse-image covers with locally quasi-finite restrictions. The Lean theorem renders these as two conjuncts: the first iff has arbitrary `A : X.Opens`, `B : S.Opens`, affine-open hypotheses, containment `e : A ≤ f ⁻¹ᵁ B`, an existential `RingHom.FiniteType` witness for `(f.appLE B A e).hom`, and `Algebra.IsQuasiFiniteAtPrime` for every `q : PrimeSpectrum Γ(X,A)` using the same canonical algebra and witness; the second iff quantifies `J`, `B`, `I`, `A`, and containment witnesses, asserts `⨆ j, B j = ⊤`, `⨆ i, A j i = f ⁻¹ᵁ B j`, and local quasi-finiteness of each canonical `f.resLE`. Quantifier order and all conclusion clauses agree with the node. The containment witnesses are canonical consequences of the cover equalities and do not strengthen the existence claim.

The predicate is the project’s Stacks-style `Scheme.Hom.IsLocallyQuasiFinite` from `pqf-def-quasifinite`, whose point predicate includes finite type and isolated fibre behaviour; it is not Mathlib’s finite-type-free `LocallyQuasiFinite`. `RingHom.FiniteType` and `Algebra.IsQuasiFiniteAtPrime` are the exact recorded notions, with the latter supplied the canonical `appLE` algebra. The proof docstring names all four source proof steps and their recorded lemmas. No extra finiteness, separation, Noetherian, characteristic, nonemptiness, or quasi-compactness assumptions occur, and all variables and universes are bound by `{X S : Scheme.{u}}`; empty schemes, empty cover indices, empty opens, zero coordinate rings, and the `n = 0` finite-type case remain covered.

I checked the dependency declarations and docstrings for `def-pc-scheme`, `pqf-def-quasifinite`, `def-weil-affine-spectrum`, `def-weil-pbc-finite-type-algebra`, and `def-weil-pbc-ring-map-quasi-finite-at-prime`, plus the seven proof dependencies named in the node. Searches in Mathlib and both project trees found no exact existing three-way criterion; the nearby Mathlib `LocallyQuasiFinite` criterion uses a different predicate. The module has the required source and blueprint docstrings, contains only `sorry` as its theorem proof, defines no hollow helper, uses no pro-etale or dropped route-pivot machinery, and has no duplicate declaration. `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q34 lem-a1-scheme-lqf-affine-criterion snapshot/lean/Sheaf/AlgebraicGeometry/IsLocallyQuasiFiniteAffineCriterion.lean` compiled both sandbox and library overlays successfully (6.9 s and 7.2 s), with no errors or warnings. No mathematical or Lean correction is needed; this replacement fixes only the missing substantive second-reading report section.
