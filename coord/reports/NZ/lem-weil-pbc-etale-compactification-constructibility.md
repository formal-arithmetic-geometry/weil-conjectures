## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility` states
`AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_homology_compactSupportCandidate`.
Its only theorem has proof `sorry`; no definitions or proofs were added.

Source read: `literature/stacks-project/more-etale.tex`, theorem-constructible-shriek
(Tag 0GL0), lines 4710–4755, and section-derived-lower-shriek-compactification,
lines 3046–3079. A finite commutative ring is Noetherian and torsion, so this is the
source's bounded-below specialization, with no invertibility hypothesis.

Clause-by-clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Each is quasi-compact: `[CompactSpace X]`, `[CompactSpace Y]`.
- Each is quasi-separated: `[QuasiSeparatedSpace X]`, `[QuasiSeparatedSpace Y]`.
- The morphism: `(f : X ⟶ Y)`; separated: `[IsSeparated f]`.
- Finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, precisely the convention node's three conditions.
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Fixed compactification: `(c : Compactification f)`. The actual scheme is `c.Z`,
  open immersion j is `c.i`, proper map p is `c.g`, and `c.comm : f = c.i ≫ c.g`
  gives the factorization. Its open immersion is quasi-compact by
  `Compactification.quasiCompact_openImmersion` applied to the existing
  `[QuasiCompact f]`; no stronger compactification notion is imposed.
- The compact-support candidate is the recorded
  `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c`, definitionally
  the derived exact extension by zero followed by the derived direct image.
- Bounded-below input: `K : DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`; `K.obj` is its underlying
  unbounded derived object. This uses the dependency's recorded small-etale module
  encoding and its existing bounded-below full subcategory, with no upper bound.
- Constructible input cohomology in every degree: `hK : ∀ q : ℤ,
  Scheme.IsConstructibleEtaleModuleSheaf
  ((DerivedCategory.homologyFunctor _ q).obj K.obj)`.
- Every integer output degree: `(q : ℤ)` and the conclusion
  `Scheme.IsConstructibleEtaleModuleSheaf` of degree-q homology of the candidate
  applied to `K.obj`. There is no extra boundedness, vanishing, or Tor conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- The convention dependency has no declaration of its own; Mathlib's `CompactSpace`,
  `QuasiSeparatedSpace`, `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`,
  `QuasiSeparated`, and compactification's `IsProper`/`IsOpenImmersion` implement it.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, with its
  full definition/docstring read at lines 74–100.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek` (lines 291–296), used inside
  that recorded candidate, and its exact derived extension.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` (lines 159–166); the derived counterpart
  `rightDerivedLowerStarPlus` is in Derived.UpperLowerStarCoherence, lines 74–81.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: its documented existing vocabulary
  `DerivedCategory.Plus`, `DerivedCategory.homologyFunctor`, and the six-functor
  module-sheaf derived encoding. Its torsion predicate is unnecessary because
  every module over the finite ring is already torsion.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, full definition and
  docstring read, finite locally constant module values on constructible strata.
- `WeilConjectures.Compactification.Defs`: `Compactification`, all fields and
  docstring read; its quasi-compactness comparison explains the compactification
  correspondence without introducing another notion.

The modules of recorded proof dependencies are imported without `public`:
AffineSpace, EtaleInverseImageModulesExact, EtaleModuleSheavesGrothendieckAbelian,
TruncationHypercohomology, ConstructibleSheaf.KernelCokernel,
Compactification.NagataCompactification, and RightDerivedFunctorPlus.
Other Mathlib proof dependencies are available transitively. The following proof
nodes have no Lean record yet, so have no module to import:
lem-weil-pbc-constructible-qcqs-affine-local,
lem-weil-pbc-etale-affine-line-shriek-sheaf-constructible,
lem-weil-pbc-etale-quasifinite-shriek-constructible,
lem-weil-pbc-etale-shriek-compactification-independence,
lem-weil-pbc-etale-shriek-qcqs-composition,
lem-weil-pbc-etale-shriek-relative-mayer-vietoris, and thm-cbc-finite-torsion.
The docstring carries all seven proof steps verbatim from the node.

Edge cases checked: empty source or target; zero coefficient ring (no Nontrivial
assumption); zero complex; arbitrary negative, zero and positive degrees; a lower
bound of either sign; cohomology unbounded above; identity compactification for a
proper map; non-Noetherian qcqs bases; coefficients whose characteristic is not
invertible on the base. None is excluded. The universe is the recorded coefficient
universe `u + 1` for schemes in `u`, with every universe and variable explicit.
No node correction, new node, dependency replacement, or statement dispute arose.

Searches actually run via `msearch.py` for this item:

- LeanFinder: “Derived proper pushforward after extension by zero preserves
  constructible cohomology for bounded below etale complexes with finite coefficients”.
  Eight hits on derived t-structure bounds, ordinary sheaf pushforward and condensed
  sheaves; none states the requested theorem.
- Loogle: `"shriek", "constructible"`: zero hits.
- Mathlib grep: `constructible.*[Ss]hriek|[Ss]hriek.*constructible`: zero hits.
- LeanSearch: “compact support etale derived pushforward preserves constructible
  cohomology”: unavailable, Internal Server Error (not a negative search result).
- `rg` on the upstream WeilConjectures tree and project `lean/Sheaf` for the node id
  and `constructible.*[Ss]hriek|[Ss]hriek.*[Cc]onstructible`: upstream stability results
  exist, but the candidate `constructibleFiniteTor_rightDerivedLowerShriek` in
  Derived/Stability/DirectImage.lean:166–179 assumes finite-type schemes over a field,
  invertible coefficient exponent and finite Tor amplitude; its full signature and
  docstring were read, and it does not state this qcqs bounded-below assertion.
  Project hits concern other statements, e.g. finite-cover lower shriek.
- `rg` on `dag/lean_names_upstream.json` for shriek/Shriek inspected the existing
  candidate and extension-by-zero names. A final full-name/node-id grep of Mathlib,
  upstream and `lean/Sheaf` found no collision for the new theorem.

Validation: scompile.py compiled this delivered file cleanly on the server in 1.7 s,
nice 19, two threads, 60-second limit. No local compiler was used.


## Second reading by NZ

Independent second reader: read the node, its seven statement dependencies and
recorded declarations, the delivered module, and Stacks more-etale.tex,
section-derived-lower-shriek-compactification (3046–3079) and
 theorem-constructible-shriek (4710 onwards, Tag 0GL0). The source assumes qcqs
schemes, separated finite presentation, a Noetherian coefficient ring, and
bounded-below torsion constructible cohomology (or its torsion-ring unbounded
variant). A finite commutative ring satisfies the coefficient assumptions; the
node deliberately requests the bounded-below specialization. No invertibility,
field, Noetherian scheme, or upper cohomological bound is required.

Object/hypothesis/conclusion checklist, in node order:

1. X and Y are schemes: `{X Y : Scheme.{u}}`. PASS; Mathlib Scheme is the
   def-pc-scheme declaration, with no base scheme or field imposed.
2. Both schemes are quasi-compact and quasi-separated: `[CompactSpace X]`,
   `[QuasiSeparatedSpace X]`, and the corresponding two Y instances. PASS.
3. f is the specified morphism: `(f : X ⟶ Y)`; separated: `[IsSeparated f]`.
   PASS; no surjectivity or properness of f is assumed.
4. f is of finite presentation: `[LocallyOfFinitePresentation f]`,
   `[QuasiCompact f]`, `[QuasiSeparated f]`. PASS; exactly the three conditions
   of def-weil-pbc-scheme-conventions, not merely local finite presentation.
5. Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. PASS; no Nontrivial, invertibility, or field instance.
6. Fixed compactification: `(c : Compactification f)` provides `c.Z`,
   `c.i : X ⟶ c.Z`, `c.g : c.Z ⟶ Y`, properness of c.g, open immersion c.i,
   and `c.comm : f = c.i ≫ c.g`. PASS. Read Compactification.Defs:
   although its structure does not require quasi-compact c.i,
   `c.quasiCompact_openImmersion` derives it from the present QuasiCompact f.
   Thus every permitted datum and precisely the requested factorizations occur.
7. Candidate Rp_* j_! K: the recorded
   `rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c`.
   PASS; read its definition as mapDerivedCategory of exact open extension by
   zero followed by total right derived lowerStar. Read lowerStar and
   openImmersionLowerShriek in their recorded modules: small-etale module
   sheaves and the required functors, not pro-etale or structure-sheaf modules.
   The recorded plus-compatibility identifies this restriction to D+ with the
   bounded-below functor; using the unbounded functor on K.obj changes nothing.
8. K in D+(X_et, Λ): `K : DerivedCategory.Plus (Sheaf
   X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, underlying object `K.obj`.
   PASS; read DerivedCategories and Mathlib TStructure, whose Plus is the full
   subcategory bounded below for the standard t-structure.
9. Every cohomology sheaf of K constructible: `hK : ∀ q : ℤ,
   Scheme.IsConstructibleEtaleModuleSheaf
   ((DerivedCategory.homologyFunctor _ q).obj K.obj)`. PASS; read the recorded
   IsConstructibleEtaleModuleSheaf definition: finite locally closed partition,
   constructible strata, inverse image locally constant with finite MODULE
   values. No replacement by subset constructibility or finite Tor amplitude.
10. Output degree q ranges over every integer: `(q : ℤ)` after hK. Conclusion
    is the same IsConstructibleEtaleModuleSheaf predicate on degree-q homology
    of this fixed candidate applied to K.obj. PASS; every conclusion clause
    occurs, with no extra vanishing, boundedness, or Tor assertion.

Edge cases: empty X or Y, zero ring (CommRing allows it), zero complex,
negative/zero/positive q, any lower bound, and no upper bound are all allowed.
There is no index-set restriction. The n=0 affine-space case occurs only in the
proof plan and is explicitly treated by the identity compactification. No
characteristic is excluded, including coefficients not invertible on the base.
All universes and binders are explicit. The coefficient universe u+1 is the
recorded six-functor convention, allows every finite ring up to universe lift,
and introduces no small-test-object hypothesis.

Independent searches (different wording from the first reader):

- LeanFinder via msearch.py: “Higher direct images with proper support of a
  bounded below constructible complex over a finite ring are constructible”.
  Eight hits: constructible subset images and standard t-structure bounds;
  none is this sheaf-cohomology statement.
- Loogle via msearch.py: `"constructible", "homology"`: zero hits.
- LeanSearch via msearch.py: “The compact support derived image of a
  constructible bounded below etale complex is constructible”: unavailable,
  Internal Server Error; not treated as evidence of absence.
- rg on Mathlib for constructible with shriek/directImage/pushforward and
  compactSupport with constructible: no matches. rg on upstream WeilConjectures
  and project lean/Sheaf for constructible with lowerShriek/compactSupport/
  shriek finds specialized results. Opened Stability/DirectImage.lean:
  constructibleFiniteTor_rightDerivedLowerShriek requires finite-type schemes
  over a field, invertible coefficient exponent and finite Tor input. It is not
  this qcqs bounded-below theorem. The other results concern open extension,
  finite covers, or bounded categories; no duplicate of this statement found.

No mismatch was found; no Lean or node change was necessary. No new definition
nodes or dependency modules are present, and no statement correction or citer
review is triggered. The sole theorem remains sorry, no construction is hollow,
and no proof was added. The declaration and module docstrings name the source
and blueprint id; the declaration docstring carries all seven node proof steps.
Proof-dependency imports match the worker report, with unstated dependencies
explicitly listed there. No local definitions, notation or instances are used.
All lines are at most 100 columns. The node lean.statement is byte-for-byte the
file signature, excluding the proof delimiter.

Validation: independently compiled the only delivered file using scompile.py
on the server: clean, 1.7 s, nice 19, two threads, 60-second limit, no warnings.
The initial invocation used a relative path from the repository and failed
before compilation with FileNotFoundError; rerunning from the sandbox succeeded.
