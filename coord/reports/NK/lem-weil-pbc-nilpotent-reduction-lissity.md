## Worker report

The item is stated by `SheafOfModules.locallyConstantFiniteTypeModules_reduction_pow`
in `Sheaf.Paper.NilpotentReductionLissity`, with proof `sorry`. The original statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the two
new definition nodes below. No dependency record is replaced.

Clause-by-clause correspondence:

- Small site: `{C : Type u} [Category.{u} C]`, `T : Precoverage C`, with `HasIsos`,
  `IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`, and its
  `T.toGrothendieck`, exactly the dependency's recorded site encoding.
- Commutative Noetherian coefficient ring: `(B : Type u) [CommRing B] [IsNoetherianRing B]`.
- Ideal: `(J : Ideal B)`, without properness or nilpotence hypotheses.
- Constant coefficient ring: `constantCoefficientRing T.toGrothendieck B` is the ring
  underlying `(constantSheaf _ CommRingCat).obj (CommRingCat.of B)`.
- Derived object: `K : DerivedCategory (SheafOfModules ...)`. `HasDerivedCategory.{w}`
  chooses the localization size for B and its quotients; no boundedness follows from it.
- Bounded above: `hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
  ((DerivedCategory.homologyFunctor _ i).obj K)`. There is no bound below.
- Derived reduction modulo J: applying
  `constantCoefficientScalarExtension _ (Ideal.Quotient.mk J)` to K. This selects the
  left-derived functor supplied by `derivedChangeOfRings` with its universal property,
  not an arbitrary triangulated functor.
- Hypothesis on every cohomology sheaf: `hmod : ∀ i : ℤ, ...`.
  `IsLocallyConstantFiniteTypeModules` says every V has a covering sieve S, and every
  `f : U ⟶ V` in S has a module `M : ModuleCat B`, `Module.Finite B M`, and an isomorphism
  of module sheaves on the slice U between F and `constantCoefficientModule ... M`.
  M may vary with the cover member. No points or finite underlying sets are assumed.
- Conclusion for powers: `∀ m : ℕ, 1 ≤ m → ∀ i : ℤ, ...`, applied to extension by
  `Ideal.Quotient.mk (J ^ m)`, with local models finite over exactly `B ⧸ J ^ m`.
- Nilpotent conclusion: the second conjunct is `∀ m : ℕ, 1 ≤ m → J ^ m = ⊥ → ∀ i : ℤ,
  ...` for cohomology of K itself with local models finite over B itself.

Dependency declarations used, with full signatures/docstrings read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (every ideal is FG).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`: `SheafOfModules.derivedChangeOfRings`.
  Its existential conclusion specifies extension on objects/maps, its additive structure,
  left-derived universal property, triangulatedness, and computation on K-flat complexes.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, identified on models by `homologyFunctorFactors`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is the
  transparent abbreviation of the exact `SheafOfModules` category used here.
- The recorded precoverage classes and `toGrothendieck` in Mathlib encode the site.
- `Sheaf.Paper.StrictPerfectCoefficientPackage`:
  `SheafOfModules.strictPerfectConstantPresheaf` is reused, not copied.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over` / `overFunctor`, the match of `def-pur-localized-ringed-site`.

The main module imports the recorded modules of all stated proof dependencies:
`CohomologyInWeakSerreSubcategory`, `KFlatResolution`, `Flat`, `KFlat`,
`DerivedChangeOfRings` (publicly through the coefficient module), `BoundedFlatReplacement`,
`BoundedAboveFlatSheafKFlat`, and the recorded definition modules. The nodes
`locally-constant-derived-serre` and `locally-constant-tensor` have no Lean record yet.
`site-module-presheaf-sheafification-exact` has Mathlib matches, no project module;
its sheafification operation is already imported by the coefficient construction.

Edge cases: m = 1 is precisely the hypothesis; m = 0 is excluded as in Tag 094I.
J = bottom recovers K; J = top has zero quotients at all positive powers and no false
nilpotent conclusion. Zero rings and zero objects are allowed. Empty sites make the local
condition vacuous as required; empty covering sieves are permitted when the topology
admits them. There is no nonemptiness requirement or bound on covers/generators. The
common u contains any given small site and ring, with no test-object quantification in a
smaller independent universe. All variables and universes are explicitly bound.

Searches performed:

- msearch LeanFinder, propagation from derived reduction modulo an ideal: completion and
  local-cohomology hits, no matching statement.
- msearch Loogle `DerivedCategory, Ideal`: zero hits.
- msearch grep `locallyConstant.*[Tt]ensor|nilpotent.*[Cc]ohomology`: zero hits.
- msearch LeanFinder, constant coefficient module sheaf/derived scalar extension: unit,
  sheafification and affine tilde hits; no selected constant-coefficient derived functor.
- msearch LeanFinder, local constant finite-module sheaves: `SheafOfModules.IsFiniteType`
  and finite-presentation/generator constructions, not the local constant model predicate.
- msearch Loogle `Module.Finite`: finds the ordinary module finiteness used here.
  The unqualified `constantSheaf` query was rejected as unknown and is not no-match evidence.
- msearch LeanSearch was attempted twice; internal server error, recorded unavailable.
- msearch grep `constantCoefficient|IsLocallyConstantFiniteTypeModules`: zero hits.
- Direct rg in WeilConjectures, lean/Sheaf, the upstream-name index and DAG: no existing
  main statement, selected constant-coefficient functor, or arbitrary-site local finite
  constant-module predicate. Found and reused `derivedChangeOfRings` and
  `strictPerfectConstantPresheaf`. Searching the item id in upstream also found no match.
- `blueprint_refs.py search` for both new notions: no blueprint definition node.

Actual msearch query/result digests are transcribed in both new nodes. The local grep
record also records the source/project/DAG searches. Existing etale/pro-etale lissity
predicates do not handle this arbitrary site; ordinary finite type supplies generators,
not local constant descriptions. The Stacks source was read directly at labels
`lemma-locally-constant-bounded` and `lemma-locally-constant-tensor-product`, including proofs.
No statement correction or STATEMENT-DISPUTED flag is needed.

All three delivered files compiled separately in dependency order using scompile.py on
the server (nice 19, two threads, 60 seconds per file), without errors or unexpected
warnings. Definitions have real data. The two named local-bijectivity facts needed for
sheafification are sorry theorems with proof descriptions and the coefficient-node tag.

## New nodes

`def-weil-pbc-constant-coefficient-scalar-extension` supplies the typed constant
commutative-coefficient ring/module adapter and selects the existing universally
characterized derived scalar-extension functor. Source: Stacks Tags 06YY and 094I.
The existing generic theorem is existential and cannot itself be applied as a functor.
Its universal property determines the selection up to natural isomorphism, exactly the
notion relevant to cohomology local constancy. The existing constant-module presheaf is
reused. `strictPerfectConstantSheaf` sheafifies into the RingCat constant ring; the adapter
sheafifies that same presheaf along the CommRingCat unit with commutativity forgotten,
so its ring is exactly the one accepted by the recorded derived-change-of-rings theorem.
No new category or tensor product is introduced. The module states the two well-definedness
facts needed for this adapter: local injectivity/surjectivity follow since forgetting
commutativity leaves the underlying functions and their covering sieves unchanged.
Searches above found no existing adapter or selected functor, and no definition node.

`def-weil-pbc-locally-constant-finite-type-modules` defines covering-sieve local finite
constant-module descriptions, using `Module.Finite`, `SheafOfModules.over`, and the
coefficient adapter. Source: Stacks Tags 094H and 094I. The module may vary with each
cover member. Searches above found no existing general-site predicate or definition node;
etale/pro-etale predicates fix a different site, and finite type alone lacks constancy.

## Second reading by NK

Independent second reader: read the sandbox's three nodes and three modules, the
repository dependency nodes and their recorded declarations, and Stacks
sites-cohomology.tex at `lemma-locally-constant-bounded` (094I) and
`lemma-locally-constant-tensor-product` (094H), including their proofs. Also read
sites-modules.tex at `definition-locally-constant` and
`lemma-locally-constant-finite-type`. The preceding lemmas with a final object do
not impose a final-object assumption on 094H or 094I.

Object/hypothesis/conclusion inventory and correspondence:

- A small site C: `{C : Type u} [Category.{u} C] (T : Precoverage C)` and the
  four precoverage classes, with topology `T.toGrothendieck`. These are exactly
  the site axioms in `def-weil-pbc-sites-and-cohomology`, including pullbacks for
  covering arrows; no arbitrary pullbacks or final object are required. Pass.
- A commutative Noetherian ring B: `(B : Type u) [CommRing B]
  [IsNoetherianRing B]`. Read `IsNoetherianRing` in Mathlib's Noetherian/Defs;
  it means finiteness of ideals, as the node requires. Pass.
- An arbitrary ideal J: `(J : Ideal B)`; neither properness nor nilpotence is
  assumed in the main implication. Pass.
- Constant coefficients: `constantCoefficientRing T.toGrothendieck B` is the
  recorded `constantSheaf` in CommRingCat, followed by forgetting commutativity.
  It is not a structure sheaf or a completed coefficient sheaf. Pass.
- An object K in D of these module sheaves: the explicit `K : DerivedCategory
  (SheafOfModules ...)` uses precisely the category underlying
  `ringedSiteModules`. Read that abbreviation and `derivedChangeOfRings`, not
  only their names. The `HasDerivedCategory.{w}` instances specify localization
  size, not geometric or finiteness hypotheses. Pass.
- K lies in D-minus: `hbounded` asks for an integer b with zero homology in
  every i greater than b. Read Mathlib's `homologyFunctor` and
  `homologyFunctorFactors`: on cochain complexes this is cohomology H^i.
  No lower bound or bounded representative is assumed. Pass.
- Every H^i of the derived reduction modulo J has a local finite constant
  B/J-module description: `hmod : ∀ i : ℤ, IsLocallyConstantFiniteTypeModules
  ... (B ⧸ J) ...`. The functor is `constantCoefficientScalarExtension` along
  `Ideal.Quotient.mk J`. Its actual choice chain selects LF from the final
  existential in `derivedChangeOfRings`, after E, its object/map equations and
  additivity; LF has the left-derived universal property and K-flat computation.
  Thus this is the required reduction, not an unconstrained functor. Pass.
- For each m at least one, every H^i of reduction modulo J^m has a local finite
  constant B/J^m-module description: the first conjunct has quantifiers
  `∀ m : ℕ, 1 ≤ m → ∀ i : ℤ` and exactly that coefficient ring. Pass.
- If a positive power vanishes, every H^i of K itself has a local finite
  constant B-module description: the second conjunct is
  `∀ m : ℕ, 1 ≤ m → J ^ m = ⊥ → ∀ i : ℤ, ... B ... K`. This is precisely the
  nilpotent specialization in the node, without a converse. Pass.

New-node review:

- `def-weil-pbc-constant-coefficient-scalar-extension`: its source describes
  constant coefficients and derived change of rings. The module supplies a real
  constant-ring object, its real whiskered unit and constant-module sheafification,
  reusing `strictPerfectConstantPresheaf`. The two local-bijectivity facts have
  named sorry proofs and describe why forgetting commutativity preserves the
  underlying functions and witness sieves. Choosing LF is permitted: its
  universal property determines the functor up to natural isomorphism, the
  equality relevant downstream. No arbitrary coefficient object is chosen.
- `def-weil-pbc-locally-constant-finite-type-modules`: opened the actual
  `SheafOfModules.over`/`overFunctor` definitions in PushforwardContinuous.
  The covering sieve and its arrows express the localizations C/U of the source;
  the isomorphism is in modules over the restricted constant ring. The finite
  model M may depend on each cover member and uses `Module.Finite`, not finiteness
  of its underlying set. This agrees with both the node and the source.
- Both new nodes have the required definition-node metadata, the item's chapter
  and unit, empty proof fields, searches, and the verified ancestor
  `thm-weil-pbc-amplification-proper`. Their statement dependencies account for
  all explicitly cited notions. They are both cited by the item. No dependency
  module or statement correction is included.

Edge cases: m=0 is excluded only from the positive-power conclusions; m=1 recovers
hmod. J=bottom gives the identity reduction; J=top gives zero quotient coefficients,
with no nilpotent consequence unless B is zero. Zero rings, zero modules, empty
sites, and covering sieves with no arrows are allowed. The local predicate does
not impose points, nonempty covers, a common finite model, or finite underlying
sets. There is no scheme, characteristic, Noetherian-site or field hypothesis.
The common universe u can contain any given small site and coefficient ring;
there is no independent smaller universe of test objects. Every variable and
universe is bound. No extra clause or missing hypothesis was found.

Independent searches: msearch LeanFinder query "Cohomology sheaves locally constant
finitely generated reduction by nilpotent ideal" found condensed-module functors,
`SheafOfModules.IsFiniteType`, generators and finite-presentation results, none of
which state this derived assertion or the local constant predicate. Loogle
`Module.Finite` confirmed the reused finiteness declaration. The attempted Loogle
`IsLocallyConstantSheaf` query reports an unknown identifier and is not no-match
evidence. Direct rg for locallyConstant/LocallyConstant and constant-module/scalar
extension declarations in Mathlib Sites, module sheaves, upstream WeilConjectures,
and repository lean/Sheaf found only constituent operations or specialized
etale/pro-etale/condensed notions. Opened the pro-etale constant-module construction:
it fixes Y.ProEt and lifted coefficients, so cannot supply this arbitrary-site
adapter. The strict-perfect RingCat construction is reused at presheaf level;
the CommRingCat ring is required by the recorded derived-change-of-rings theorem.
DAG and blueprint searches found no node for these two arbitrary-site notions.
The worker's LeanSearch service failures remain explicitly recorded as unavailable.

No mathematical mismatch was found; no Lean or node change was needed. All source
and declaration docstrings identify their source and blueprint node. The main
proof docstring carries each of the four node proof steps and their dependencies.
Every delivered theorem remains sorry; every definition has real data. All three
modules compiled separately in dependency order through scompile.py on the server,
nice 19, two threads, 60 seconds per file, with no errors or unexpected warnings.
The node lean.statement signatures were checked against the source verbatim.
