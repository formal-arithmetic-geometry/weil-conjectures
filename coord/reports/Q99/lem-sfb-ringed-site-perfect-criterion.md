## Worker report

The delivery states Stacks 08G8 on arbitrary ringed sites in
`Sheaf.Algebra.Homology.RingedSitePerfectCriterion`, with the sole theorem
`SheafOfModules.isPerfectOnRingedSite_iff_pseudoCoherent_locallyFiniteTor` left `sorry`.
The statement and proof of the assigned node are unchanged. Two missing definition nodes
supply the general-site approximation predicate and local Tor condition. They have real
predicate bodies, no postponed proofs, and reuse the published constructions.

Hypothesis and clause correspondence:

- A ringed site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)` and
  `(R : Sheaf J CommRingCat.{max u v r})`. The tensor in the node and its K-flat
  dependencies already require commutative structure rings; this makes that convention explicit.
- Smallness relative to module sheaves is encoded by the coefficient/module size
  `max u v r`, containing both site sizes, with explicit sheafification and
  `WEqualsLocallyBijective` instances on the site and each slice. These are categorical
  infrastructure available in the chosen universe, not geometric conditions on the site.
  In particular site object and morphism universes are independent. `r` permits coefficients
  larger than either. No final object is assumed.
- The unbounded derived category is `DerivedCategory (ringedSiteModules ... R)` under
  `[HasDerivedCategory.{w} ...]`. Slice localizations use the independently bound `w'`.
  No t-structure support predicate is assumed of K.
- Strict perfectness uses the existing `StrictPerfectCoefficientPackageOnSite` with
  `(∃ a b : ℤ, ∀ n, n < a ∨ b < n → IsZero (P.X n))`. Its fields N, i, p and
  splitting say each term is a retract of the finite power of the structure module;
  there is no requirement that these degreewise maps be chain maps.
- `IsMPseudoCoherentOnRingedSite R m K` quantifies `∀ U`, then a covering sieve S,
  then every arrow `f : V ⟶ U` in S. The bounded P and its package are chosen there.
  The morphism `α : DerivedCategory.Q.obj P ⟶ ringedSiteDerivedRestrictionOfUniverses ... V K`
  is in the slice derived category. The final two conjuncts give `IsIso` of H^j(α)
  for `m < j` and `Epi` of H^m(α). Epimorphism in this abelian category means sheaf
  surjectivity, not surjectivity of global sections. The derived-map formulation is
  exactly the item's wording and Stacks 08FU's local derived formulation of 08FT.
- `IsPseudoCoherentOnRingedSite R K := ∀ m : ℤ, IsMPseudoCoherentOnRingedSite R m K`.
  It does not require a common cover or common approximating complex for all m.
- The existing `HasRingedSiteTorAmplitudeOfUniverses` is `a ≤ b ∧ ∀ L q, ...`,
  testing every module sheaf in degree zero by `DerivedCategory.singleFunctor _ 0`;
  H^q vanishes for `q < a ∨ b < q` using `IsZero`. The tensor is the canonical
  resolving-class K-flat localization `siteDerivedTensorIndependentCoefficients`.
  The recorded K-flat predicate and total tensor are reused by that construction.
- The existing `HasFiniteRingedSiteTorAmplitudeOfUniverses` is `∃ a b,` that test.
  `HasLocallyFiniteTorDimensionOnRingedSite` places this existential AFTER choosing
  every covering member V. It tests all modules on C/V, not only restrictions of
  global modules. It uses R.over V and the recorded canonical derived restriction.
- Perfectness is exactly the existing `IsPerfectOnRingedSiteOfUniverses R K`:
  a representative admitting bounded finite-free-retract quasi-isomorphisms on a
  covering sieve of every object, equivalent to the item's derived local-isomorphism
  description by Stacks 08G6. No second perfectness predicate is introduced.
- The conclusion is precisely `IsPerfectOnRingedSiteOfUniverses ... ↔
  IsPseudoCoherentOnRingedSite ... ∧ HasLocallyFiniteTorDimensionOnRingedSite ...`.
  There is no quasi-compactness, coherence, boundedness, enough-points, constant-ring,
  affine, or scheme hypothesis.

Dependency declarations used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, Q.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the transparent
  Mathlib module-sheaf category.
- `def-weil-size-convention`: metatheoretic convention, no declaration; implemented by the
  displayed explicit universe parameters and localization infrastructure.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, reused through the tensor localization.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, the total tensor.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and the package from its public
  `StrictPerfectPackageOnSite` import. Added the existing owning node to stmt_deps.
- `Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`:
  `CategoryTheory.ringedSiteDerivedRestrictionOfUniverses`, restricts Q.objPreimage and localizes.
- `Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses`:
  `CategoryTheory.HasRingedSiteTorAmplitudeOfUniverses`,
  `CategoryTheory.HasFiniteRingedSiteTorAmplitudeOfUniverses`. Despite its owning node's
  specialized title, these published declarations take arbitrary ringed sites and ring sheaves.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `homologyFunctor`.

The theorem imports every available proof dependency as a non-public proof import:
tensor closedness, bounded flat models, localized ringed sites, exact restriction,
Tor interval restriction, standard t-structure, truncation/heart infrastructure,
bounded-below isomorphism criterion, flat finitely presented local retracts.
`lem-sfb-flat-approximation-opcycle` has no recorded Lean declaration or Mathlib match
on the read base, so no import can yet be attached for it. Its mathematical step is
fully retained in the theorem docstring; it is only a proof prerequisite, not a notion
needed to type this statement. The docstring expands all five DAG proof steps, including
the finite presentation, good truncation, and why no brutal truncation at b is performed.

Edge cases checked before writing: zero ranks (Fin 0) and zero complexes are allowed;
the zero complex has interval [0,0]. The zero ring is allowed. If an empty sieve covers,
the local assertions are correctly vacuous. If the site has no objects, every local
predicate is vacuous. Non-quasi-compact sites permit nonuniform bounds, ranks and covers;
there is no hidden global boundedness. Negative degrees and every integer m are included.
The case a=b is included; Tor tests require a≤b through the existing predicate.
An epimorphism is local sheaf surjectivity, avoiding a false global section condition.

Searches: `msearch.py` LeanFinder for “A derived complex on a ringed site is perfect iff
pseudo coherent and locally finite Tor dimension” returned eight t-structure hits and no
criterion. Loogle `"Perfect", "PseudoCoherent"` returned zero hits. Mathlib grep
`Perfect.*PseudoCoherent|perfect.*pseudo.?coherent` returned zero. Additional LeanSearch
for m-pseudo-coherent local approximations returned finite-presentation/quasicoherence hits,
not this predicate; LeanFinder for local Tor/pseudo-coherence returned finite-type and
finite-presentation hits. For the new nodes the recorded queries include LeanSearch
“locally finite Tor dimension ringed site covering interval”, LeanFinder “m pseudo coherent
approximations on a ringed site and locally finite Tor dimension”, Mathlib grep
`PseudoCoherent|LocallyFiniteTor`, and project rg of definition names. Existing scheme/ring
predicates do not apply to arbitrary sites; existing perfectness and universal Tor tests
do and are reused. DAG definition search found only the scheme local Tor node;
`blueprint_refs.py search 'ringed site pseudo-coherent'` returned zero, and search for
'locally finite tor dimension' found only the bounded-constructible coefficient blueprint
node. `rg` for the assigned id in WeilConjectures found no declaration. Concept searches
of both WeilConjectures and Sheaf found scheme/ring perfectness criteria only.

No STATEMENT-DISPUTED or source correction is needed. Stacks 08FT, 08FU, 08FZ, 08G5,
08G7 and 08G8 were read in sites-cohomology.tex, with tag labels checked in tags/tags.

## New nodes

`def-sfb-ringed-site-pseudocoherent-complex`: Stacks 08FT and 08FU's local derived
strictly-perfect approximation definition and the all-integer pseudo-coherence predicate.
Existing scheme/space/ring definitions specialize to those geometries and do not supply
this arbitrary-site notion. The published perfect coefficient packages and canonical
slice derived restriction are reused, with no copy of their definitions. Searches and
negative results are recorded in mathlib_searches. Module:
`Sheaf.Algebra.Homology.RingedSitePseudoCoherent`.

`def-sfb-ringed-site-locally-finite-tor-dimension`: Stacks 08FZ(3), a covering of every
object with finite Tor dimension on each member. It reuses the existing universal
ringed-site Tor test and its existential ordered interval. The missing notion is the
covering quantifier, not a new tensor or new Tor test. Existing local Tor dimension
is scheme-only. Searches and results are in mathlib_searches. Module:
`Sheaf.Algebra.Homology.RingedSiteLocallyFiniteTor`.

## Second reading by Q99

Independent reading by the maintainer's second reader (the worker's own self-check, which
said it was not an independent review, is replaced). Read: the item node, its eight
stmt_deps, Stacks sites-cohomology.tex 08FT, 08FU, 08FZ, 08G5, 08G7, 08G8, the three
delivered modules, and the used declarations `IsPerfectOnRingedSiteOfUniverses`,
`IsLocallyStrictPerfectComplexOfUniverses`, `StrictPerfectCoefficientPackageOnSite`,
`ringedSiteDerivedRestrictionOfUniverses`, `HasRingedSiteTorAmplitudeOfUniverses`,
`HasFiniteRingedSiteTorAmplitudeOfUniverses`, `siteDerivedTensorIndependentCoefficients`.

Node clauses and their Lean:

1. Ringed site (C, O), small relative to the module-sheaf universe: `C : Type u`,
   `Category.{v} C`, `J`, `R : Sheaf J CommRingCat.{max u v r}`; module sheaves of the
   underlying `RingCat` sheaf in universe `max u v r`. The sheafification and
   `WEqualsLocallyBijective` instances on J and its slices are the same infrastructure the
   owner `IsPerfectOnRingedSiteOfUniverses` requires; no geometric condition. Commutative O is
   the convention of Stacks and of the derived tensor. Correct.
2. K ∈ D(O), unbounded: `K : DerivedCategory (ringedSiteModules ...)`, no IsGE/IsLE. Correct.
3. Strictly perfect complex: bound `∃ a b, ∀ n, n < a ∨ b < n → IsZero (P.X n)` plus
   `Nonempty (StrictPerfectCoefficientPackageOnSite _ P)` (degreewise i, p with i ≫ p = 𝟙 into
   a finite product of the unit module). Exactly "bounded, terms direct summands of finite
   free". Correct.
4. m-pseudo-coherent (08FT/08FU): `IsMPseudoCoherentOnRingedSite`: ∀ U, a covering sieve S,
   ∀ f : V ⟶ U in S, a strictly perfect P on C/V and `α : Q.obj P ⟶ K|_V` (canonical
   `ringedSiteDerivedRestrictionOfUniverses`), `IsIso (H^j α)` for m < j, `Epi (H^m α)`.
   Derived-map form is the item's own wording and 08FU. Epi in module sheaves is sheaf
   surjectivity, as in Stacks. Correct.
5. Pseudo-coherent: `∀ m, IsMPseudoCoherentOnRingedSite R m K`; covers depend on m. Correct.
6. Tor amplitude [a,b] (08FZ(1)): existing `HasRingedSiteTorAmplitudeOfUniverses`:
   `a ≤ b` and for every module sheaf L and q < a ∨ b < q, `IsZero (H^q (K ⊗^L L[0]))`
   with the recorded K-flat derived tensor. Finite Tor dimension (08FZ(2)): `∃ a b`.
   Correct; the tensor is pinned by its representative comparison and IsZero is
   iso-invariant.
7. Locally finite Tor dimension (08FZ(3)): `HasLocallyFiniteTorDimensionOnRingedSite`:
   ∀ U, covering sieve, ∀ member V, finite Tor amplitude of `K|_V` over `R.over V`, testing
   all O_V-modules; interval chosen after V. Correct; the slice ring `R.over V` agrees
   definitionally with the restricted underlying ring (the file compiles with it).
8. Perfect (08G5): the existing owner `IsPerfectOnRingedSiteOfUniverses`: a representative P
   of K which on a covering sieve of every object receives a quasi-isomorphism from a
   strictly perfect complex. This equals "locally isomorphic in D to a strictly perfect
   complex": a quasi-isomorphism gives the derived isomorphism; conversely a derived map
   out of a strictly perfect complex is a chain map after refining the cover (Stacks,
   sites-cohomology, local-actual lemma), and both sides quantify over covers. One
   definition per notion: the recorded owner is reused, and its node is now in stmt_deps.
9. Conclusion: `IsPerfect… ↔ IsPseudoCoherent… ∧ HasLocallyFiniteTorDimension…`, both
   directions. No quasi-compactness, coherence, boundedness, enough-points or final-object
   assumption. Correct.

Edge cases: empty site / empty covering sieve: all three predicates vacuous together;
K = 0: perfect via the zero complex, Tor interval [0,0], every m-approximation by 0;
zero ring: all module sheaves zero, both sides true; negative m and a = b are included;
universes u, v, r, w, w' are independent and bound, with no equality forced.

Records: the item's statement, proof and proof_deps are unchanged; stmt_deps gain the two new
definition nodes and the landed owner def-weil-pbc-strict-perfect-coefficient-package. Each
`lean.statement` matches its file verbatim. The new nodes have the fields of the extra-nodes
rule, self-contained statements with cited definitions, Stacks source places, and
LeanSearch/LeanFinder/grep searches. A search of side-live found no arbitrary-site
pseudo-coherence or locally finite Tor definition (def-pc-locally-finite-tor-dimension is
scheme-only; lem-sfb-ringed-site-pseudocoherent-top-finite-type has no Lean record).
Docstrings carry the source place and blueprint id; the theorem docstring has all five
proof steps; the only proof is `sorry`; the definitions have real bodies.

Changed: only this report section. Lean files and node records are unchanged.
