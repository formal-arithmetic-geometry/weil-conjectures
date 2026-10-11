## Worker report

The module defines `HasLocallyFiniteTorDimension` and states that a perfect object is pseudo-coherent and has this local finite Tor property. The local predicate quantifies points, opens, an integer interval, a bounded-above complex representative, and vanishing outside the interval for every module. The theorem hypotheses are the scheme, derived-category instances on X and opens, object E, and `IsPerfect X E`; its conclusion is the conjunction of `IsPseudoCoherent X E` and the new predicate.

Dependencies used: `Sheaf.AlgebraicGeometry.PerfectComplex` (`AlgebraicGeometry.Scheme.IsPerfect`), `Sheaf.AlgebraicGeometry.PseudoCoherentComplex` (`AlgebraicGeometry.Scheme.IsPseudoCoherent`), and `Sheaf.AlgebraicGeometry.DerivedCategory` (`schemeDerivedCategory`).

Edge cases checked include the empty scheme (pointwise clause is vacuous), zero complexes, and intervals with `a = b`. Searches found no existing scheme-level theorem combining perfectness, pseudo-coherence, and local finite Tor dimension (the node's recorded searches report no match). A new definition node was added because the local Tor-dimension notion was absent from Mathlib and the project.

## Second reading by J1

Independent item-by-item reading of the repository node, its dependency nodes and
Lean declarations, the sandbox node copies and modules, and the Stacks source:
`cohomology.tex`, `lemma-perfect` (08CQ), and `definition-tor-amplitude` (08CG).
The source assumes only a ringed space and a derived object; this node specializes
to schemes. Its forward implication has no Noetherian, separation, characteristic,
quasi-coherence or finiteness hypothesis on X.

The node's objects, hypotheses and conclusions match as follows:

- Scheme X: `(X : Scheme.{uP})`; the recorded Mathlib Scheme notion, unrestricted.
- Derived object E: `(E : schemeDerivedCategory X)`; the recorded shared derived
  category of `SheafOfModules (moduleRings X.toRingedSpace)`, not X.Modules with a
  different category instance. The `HasDerivedCategory.{wP}` binders on X and its
  opens are precisely those of the recorded perfect and pseudo-coherent predicates,
  supplying localization models, not additional mathematical restrictions.
- Perfectness: `(hE : IsPerfect X E)`. Opened PerfectComplex: each point has an
  open and a strictly perfect complex, bounded and termwise a retract of finite
  free modules, whose Q-image is isomorphic to the derived restriction of E.
- Pseudo-coherence: `IsPseudoCoherent X E`, the first conjunct. Opened
  PseudoCoherentComplex: the same derived restriction, with a bounded-above
  finite-free representative. Exactly the scheme formulation of the dependency.
- Local finite Tor dimension: `HasLocallyFiniteTorDimension X E`, the second
  conjunct. Its body starts `∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ a b : ℤ, a ≤ b ∧`.
  Thus U is a neighbourhood, and the interval depends on x and U, before the
  quantification over all test modules and all degrees.
- The restricted object is `(SheafOfModules.overFunctor (moduleRings
  X.toRingedSpace) U).mapDerivedCategory.obj E`. Its explicit isomorphism with
  `DerivedCategory.Q.obj P` connects the representative to E, rather than an
  arbitrary unrelated complex.
- Derived tensor and cohomology: `CochainComplex.IsKFlat (R := X.sheaf.over U) P`
  and `IsZero ((CochainComplex.mapBifunctor P (single ... 0).obj G
  (curriedTensor _)).homology i)`. The existing K-flat and total-tensor definitions
  are used on the over site. G is every module on that site, placed in degree zero;
  `i < a ∨ b < i` is exactly outside the closed integer interval. K-flat existence
  and independence (06YS/06YU) make this the derived tensor, with one representative
  usable for every G. No bounded-above condition is imposed on its terms.

Verdict after repair: each clause matches, without stronger hypotheses or a weaker
conclusion. The item's own natural-language statement was already correct and was
not changed. No statement correction or dependency replacement was necessary.

Mismatches found and repaired:

1. H3/H5: the former predicate ignored E (`let _ := E`), had no representing
   isomorphism and no K-flatness; it could always choose P = 0. Added the isomorphism
   to the actual derived restriction and the recorded K-flat condition.
2. H3: G was ignored (`let _ := G`), and vanishing concerned P's terms rather than
   the cohomology of P tensor G[0]. Replaced it with total-tensor homology vanishing.
   Removed the extraneous bounded-above term condition. The old predicate was
   mathematically vacuous, not a local Tor-dimension definition.
3. H8/H12: the definition's blueprint tag belonged to the item, both nodes shared
   one module, and the new node had no searches, creation/audit fields, TeX citations
   or correct ancestor path. Split out LocallyFiniteTorDimension.lean and repaired
   these fields, using the actual definition source 08CG and existing K-flat/tensor
   dependency nodes. Added the proof's named dependencies to the theorem docstring,
   the copyright header, and exact multiline signatures to both Lean records.
4. Compilation required explicit typed local monoidal and zero-morphism-preservation
   instances on `(moduleRings X.toRingedSpace).over U`; these use existing declarations
   from KFlat, add no hypotheses or new theorem. Distinct module universe names allow
   the required combined compile, and long docstring lines were wrapped.

Edge cases: empty X makes both pointwise local conclusions vacuous, as the source
covering formulation does; zero E has the zero K-flat representative and all tensor
cohomology zero. A singleton interval a = b, including a = b = 0, is permitted;
negative degrees and arbitrary shifts are covered by integers. The zero module G is
included, as are non-quasi-coherent modules. No characteristic is specified and no
field/ring restriction is introduced. Arbitrary scheme universe uP and localization
universe wP are explicitly bound; all module universes are the same as the dependency
carriers, not a smaller universe that could make the test quantification vacuous.
There is no index type or nonempty-cover hypothesis excluding the empty scheme.

Independent searches: LeanFinder query "locally finite Tor dimension sheaves modules
perfect pseudo coherent" returned module finite-type/finite-presentation predicates,
none of this notion or statement; Loogle HasLocallyFiniteTorDimension had zero hits;
LeanSearch "perfect complex is pseudo coherent and locally finite Tor dimension"
was unavailable (Internal Server Error). rg searched Mathlib, WeilConjectures,
lean/Sheaf and dag/nodes for local Tor dimension, TorAmplitude, perfect and
pseudo-coherent variants. Opened source CategoryTheory/DerivedCategory/Perfect:
its IsPerfect is for modules over a ring, not scheme-local module sheaves.
The pro-etale constructibleFiniteTor predicates are for coefficient sheaves on
another site. The existing schemeDerivedTensorCohomologyVanishes is the global
scheme predicate; it is not local finite Tor dimension, and its carrier is not the
over-site carrier used by the dependency definitions. Its existing K-flat and tensor
ingredients are reused rather than redefining either. No existing local finite Tor
predicate or theorem states this item. No duplicate new node was found.

The new node was read independently against 08CG: the pointwise-open definition is
exactly its covering-local clause, the K-flat formulation computes its derived
cohomology, and the node cites the scheme, derived category, K-flat and total-tensor
notions it uses. Its fields now follow the stage-2 new-definition contract. No hollow
data remain. The only sorry is the named item theorem; no theorem is proved.

## New nodes

`def-pc-locally-finite-tor-dimension`: defines pointwise local finite Tor dimension
for a scheme derived object, using the common-interval vanishing of derived tensor
against all modules, equivalently a K-flat representative on the open's localized
site. Source: Stacks 08CG, cohomology-definition-tor-amplitude, clause (3), with
06YS/06YU for computation. The independent searches above found no existing node
or declaration for this local predicate; the global derived-tensor vanishing node
and ring/pro-etale Tor predicates have different scopes. It has its own module,
uses existing notions only, and is cited by the item.

Validation: both modules compiled together on the server with exit code 0 and no
warnings (5.3 seconds). The dry-run preflight identified stale blueprint ancestry
in the new node and signature records including `:=`; updated the new node to the
current server ancestry and recorded the signatures without the body delimiter,
as required by the preflight's signature comparison. All variables/universes are
explicitly bound. No further Lean change was needed.

## Reviewer FIX (R-ppt1520, stage 2)

- H4: `HasLocallyFiniteTorDimension` re-spelled the body of the landed
  `schemeDerivedTensorCohomologyVanishes` (def-pc-derived-tensor-cohomology-vanishes, E1) on the
  over-site, with three `letI` instance binders inside the statement (no-`let` rule). Restated
  through the landed predicate on the open subscheme `U.toScheme`, applied to
  `(derivedPullback U.ι).obj E` (the form landed in lem-sc-perfect-degree-zero-fibre-criterion):
  `∀ x, ∃ U, x ∈ U ∧ ∃ a b, a ≤ b ∧ ∀ G i, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes
  U.toScheme ((derivedPullback U.ι).obj E) G i`. The definition and the item theorem gain the
  localization-model binder `[∀ U : X.Opens, HasDerivedCategory (SheafOfModules (moduleRings
  U.toScheme.toRingedSpace))]`; the over-site binder stays for `IsPerfect`/`IsPseudoCoherent`.
- The new node's statement now names the derived pullback and the vanishing predicate;
  stmt_deps def-pc-derived-pullback and def-pc-derived-tensor-cohomology-vanishes replace
  def-pc-kflat-complex and def-pc-tensor-complex-sheaves.
