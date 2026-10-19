## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction` states
`AlgebraicGeometry.Etale.isBoundedConstructible_of_finite_boundary`, with whole proof `sorry`.
Its docstring expands the seven proof steps of the node. No definitions are introduced and
no natural-language statement, dependency, or proof field is changed.

Hypothesis and conclusion correspondence:

- The field of the unit is `(k : Type u) [Field k]`, with no characteristic, algebraic
  closedness, or perfection restriction.
- Finite-type k-schemes Y and S are `[Y.Over (Spec (.of k))]` and
  `[S.Over (Spec (.of k))]`, each with `LocallyOfFiniteType` and `QuasiCompact` on its
  structure morphism. The k-morphism b is `(b : Y ⟶ S) [b.IsOver (Spec (.of k))]`;
  properness is `[IsProper b]`.
- Finite coefficients are `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` and
  `hcoeff : IsSmoothBaseChangeCoefficients N Λ S`. The recorded predicate expands to
  positive N, finite Λ, `(N : Λ) = 0`, and N invertible on S. Its invertibility pulls
  back along b, a, and i to the other schemes, so this states the coefficient convention
  on all schemes concerned. The separate `Finite` instance supplies the existing
  bounded constructibility predicate's instance argument; it duplicates no new restriction.
- The open immersion is `(a : G ⟶ Y) [IsOpenImmersion a]`.
- Its closed complement is `(i : Z ⟶ Y) [IsClosedImmersion i]` and
  `hcomplement : Set.range i.base = (Set.range a.base)ᶜ`. This permits every closed
  subscheme structure on the complementary set, including nonreduced structures.
- Finiteness of bi is `[IsFinite (i ≫ b)]`, in Lean's composition order.
- K in D⁺ is the binder
  `K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  `K.obj` is the corresponding object of the ambient derived category.
- Bounded constructibility of a* K is `hopen`, applying the recorded predicate
  `DerivedCategory.isBoundedConstructible Λ G` to
  `(upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K.obj`.
  Exact inverse image acts termwise; this is ordinary étale inverse image.
- Bounded constructibility of Rb* K is `hpush`, applying the same recorded predicate
  on S to `((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).obj K).obj`.
- The conclusion is precisely `DerivedCategory.isBoundedConstructible Λ Y K.obj`.
  It asks for all cohomology sheaves constructible in the dependency's sense and a
  finite cohomological support interval; there is no Tor-amplitude condition.

Statement dependencies read and reused:

- `sbc-def-coefficient-conventions`: `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`,
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients` (full definition read).
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, together
  with the definition of `AlgebraicGeometry.Etale.DerivedCategoryModule` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` and Mathlib's
  `DerivedCategory.Plus`. The module explains the sheaf-valued module encoding used here.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` (full definition read).
  This is used rather than the upstream predicate with a different constructibility notion.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and the recorded
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, whose actual defining module is
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence` (signature and docstring
  read there). The declaration gives exactly the bounded-below module pushforward required.
- `def-weil-pbc-inverse-image`: `AlgebraicGeometry.Etale.upperStar` and
  `upperStarLowerStarAdjunction` in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
  full definitions and the accompanying exactness instances read. The imported framework's
  `mapDerivedCategory` applies this exact functor on the derived category.
- `def-weil-pbc-scheme-conventions` is a convention-only record, not a declaration.
  Its recorded Mathlib classes `IsProper`, `IsFinite`, `IsOpenImmersion`,
  `IsClosedImmersion`, `LocallyOfFiniteType`, `QuasiCompact` are used directly.

All recorded proof-dependency modules are imported, including the newly stated exact-functor
and K-injective total-derived modules. The following proof dependencies have no Lean record
and therefore have no module to import yet: `lem-cbc-open-closed-recollement`,
`lem-weil-derived-direct-image-composition`, `lem-fin-proper-bounded-constructible`,
`lem-fin-finite-reflects-derived`. They remain named in the proof docstring. The size
convention has no declaration; Mathlib proof leaves are covered by the Noetherian,
derivability, homology-sequence and exact-functor imports. There is no omitted import to
avoid a cycle.

Edge cases checked before drafting: a may have empty source (finite b then supplies
reflection); Z may be empty (a covers Y); Y and S may be empty; K may be zero or supported
in any integer interval. No nonemptiness, dimension bound, or cohomological degree bound
is imposed. The coefficient ring may be the zero ring; positive N and invertibility are
exactly the supplied convention, including N = 1. Arbitrary nonreduced complementary
closed subschemes are allowed. Scheme and coefficient universes match the dependency
encoding, with explicit universe u and all variables bound. The theorem states no
assertion about adic or pro-étale complexes.

Searches for an existing statement (2026-10-15):

- `msearch.py`, LeanFinder: “A bounded below etale complex is bounded constructible if
  its open restriction and proper pushforward are bounded constructible and the closed
  boundary is finite”. Eight hits, including `Scheme.Hom.isConstructible_image`,
  `Scheme.Hom.isLocallyConstructible_image`, spectrum constructible-set complexity and
  topology constructible-image/preimage results; none states this theorem.
- `msearch.py`, Loogle: `"isBoundedConstructible"`: zero hits.
- `msearch.py`, grep: `finite.*boundary|boundary.*reconstruction|isBoundedConstructible`:
  five unrelated Mathlib filter, CW complex and manifold boundary hits.
- `msearch.py`, LeanSearch: “bounded constructible etale complex reconstruction proper
  pushforward finite closed complement”: unavailable, Internal Server Error.
- `rg` in the source's `WeilConjectures` and the project's `lean/Sheaf`, using the item id,
  `finiteBoundary|finite_boundary`, and concept variants
  `finite.*boundar|boundar.*finite|reconstruct.*constructib|constructib.*reconstruct`:
  no exact theorem. Results concern finite boundaries of curves, coherent/affine
  reconstruction and unrelated cochain boundaries. Targeted reading/search of
  `SixFunctors`, `ConstructibleSheaf` and `CategoryTheory/DerivedCategory` found integral
  projection-formula reconstruction, not ordinary étale finite-boundary reconstruction.
- `rg` for `isBoundedConstructible_of_finite_boundary` in the upstream name index,
  upstream source and project Lean: no existing name.

Source checked: the full blueprint lemma and its proof, and its unit's `_section.md`.
No node fault, statement correction, or STATEMENT-DISPUTED issue was found.

Validation: the initial module compiled cleanly through `scompile.py` on the server
(nice 19, two threads, 60 seconds per file). Explicit public imports of the two recorded
ambient-definition modules were then added; the final dry run recompiles the delivered file.

## Second reading by NU

I independently read the sandbox node, its seven proof steps, the complete delivered
module, all six statement-dependency records and their defining declarations. I read the
source blueprint lemma and unit section, and Stacks `etale-cohomology.tex`,
`lemma-ses-associated-to-open` (095L). The latter allows an arbitrary closed subscheme
and its complementary open, without reducedness or a nonemptiness hypothesis. The node's
explicit finite-type k-scheme convention supplies the base field omitted from the short
blueprint lemma; the delivered Lean follows the node. There is no new statement correction.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

1. The field k is `(k : Type u) [Field k]`. There is no algebraic-closedness,
   perfection, cardinality, or characteristic assumption.
2. Y and S are `{Y S : Scheme.{u}}` with their respective `Over (Spec (.of k))`
   instances. `LocallyOfFiniteType` and `QuasiCompact` on each structure morphism
   express finite type exactly; neither scheme is additionally assumed separated.
3. The proper k-morphism is `(b : Y ⟶ S) [b.IsOver (Spec (.of k))] [IsProper b]`.
   Its direction and compatibility with the two specified k-structures are correct.
4. The coefficient data are `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`
   and `hcoeff : IsSmoothBaseChangeCoefficients N Λ S`. I opened this definition:
   it is `0 < N ∧ Finite Λ ∧ (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`.
   The separate finite instance is the same finiteness condition required to type
   the constructibility predicate. Invertibility on Y, G and Z follows by pullback
   of the global section along their maps to S; it is not an omitted assumption.
5. The open source is G, with `(a : G ⟶ Y) [IsOpenImmersion a]`.
6. The boundary is Z, with `(i : Z ⟶ Y) [IsClosedImmersion i]` and
   `hcomplement : Set.range i.base = (Set.range a.base)ᶜ`.
   This specifies the complementary underlying set without imposing an unwarranted
   reduced scheme structure, consistently with the source.
7. The boundary-to-base composite is finite: `[IsFinite (i ≫ b)]`.
   Lean's order here is precisely the node's bi.
8. K is an object of `DerivedCategory.Plus (Sheaf Y.smallEtaleTopology
   (ModuleCat.{u + 1} Λ))`. I checked `DerivedCategoryModule` in upstream
   `SixFunctors.Etale.Derived.Coefficients`: the ambient derived category is exactly
   the derived category of these module-valued sheaves. Mathlib's Plus is the
   bounded-below full subcategory, and `K.obj` is its ambient object.
9. The open hypothesis `hopen` applies `DerivedCategory.isBoundedConstructible Λ G`
   to `(upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K.obj`.
   I read the upstream definition and adjunction of `upperStar`: this is the
   ordinary constant-coefficient inverse image, and the imported exactness permits
   its termwise induced derived functor. It is not a different tensor pullback.
10. The image hypothesis `hpush` applies the same predicate on S to
    `((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).obj K).obj`.
    I opened `UpperLowerStarCoherence`: this functor is exactly
    `(lowerStar _ b).rightDerivedFunctorPlus`, with domain and codomain D-plus.
    The sheaf pushforward in `UpperLowerStar.Defs` is restriction along etale
    base change, as the direct-image dependency specifies.
11. The conclusion `DerivedCategory.isBoundedConstructible Λ Y K.obj` says exactly
    K belongs to D-b-c. I opened `BoundedConstructibleComplexes`: it requires all
    integer cohomology sheaves to satisfy the project's recorded
    `Scheme.IsConstructibleEtaleModuleSheaf`, and integers a ≤ b with zero cohomology
    outside [a,b]. I also read that constructible-sheaf definition: finite locally
    closed constructible stratification and etale-local finite constant module values.
    No Tor-amplitude or adic/pro-etale condition appears. Quantifiers are in the
    same dependency order as in the node; the independent G and Z structures over k
    are inherited through their immersions, so no extra instances are needed.

Edge cases: an empty G, empty Z, empty Y or S, and the zero complex are allowed.
No index type or dimension parameter requires nonemptiness. The support interval is
existential and can be anywhere in the integers. N = 0 is excluded by the source's
positive-N convention, N = 1 and the zero coefficient ring are allowed, and in positive
characteristic the restriction is exactly invertibility of N on S. Arbitrary nonreduced
boundary structures are allowed. The explicit scheme universe u and coefficient/module
universe u+1 agree with the recorded ambient encoding; finite coefficients can be lifted
into this universe. There are no independent test-universe quantifiers or unbound names.

Independent duplicate searches used different phrases from the worker:

- LeanFinder via `msearch.py`: “constructibility detected by open restriction and proper
  pushforward with finite closed complement”. Eight hits, all constructible subsets
  and their images/preimages; none is the complex reconstruction theorem.
- Loogle via `msearch.py`: `"isBoundedConstructible"`, zero hits.
- Grep via `msearch.py`: `constructible.*(cone|closed)|recollement`, nine hits on
  constructible topological subsets and spectrum complexity, none relevant.
- LeanSearch via `msearch.py`: “bounded constructible complexes recovered from open
  restriction and proper image finite complement”; service unavailable (Internal
  Server Error), recorded as unavailable rather than negative evidence.
- Direct rg on Mathlib, upstream WeilConjectures and project lean/Sheaf:
  `constructib.*(reconstruction|finite_boundary)|finite_boundary|finiteBoundary|reconstruct.*constructib`.
  The only hits are unrelated finite cocone boundaries and boundaries of curves.
  Reading the actual bounded-constructibility dependency also confirms that the upstream
  predicate uses a different recorded sheaf notion and is not a replacement theorem.

No mismatch was found; I changed no Lean or node content. There are no new definition
nodes or dependency modules to audit, no data definitions or hidden proof obligations,
and the sole theorem proof is wholly `sorry`. The docstring follows all seven node steps,
including establishing boundedness before using the D-b triangulated-subcategory theorem.
I checked the proof-dependency module records against the imports: all recorded modules
are present; the four as-yet-unstated proof dependencies listed in the worker report have
no module to import. Public imports expose the statement's ambient definitions. Source
citations, blueprint tags, namespaces and line widths meet the conventions. A direct
string comparison confirms `lean.statement` equals the file signature verbatim.

Validation: the delivered module is checked through server-only `scompile.py`, followed
by `deliver2.py --no-push` and the delivery tool's repeated server compile and preflight.
