## Worker report

Module: `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`.
Declaration: `AlgebraicGeometry.coherentFormalModules_local_exactness`.
This is a statement only, with one `sorry` proof and no new definitions.

Hypotheses and clauses matched to Lean:

- Noetherian scheme X: `(X : Scheme.{u}) [IsNoetherian X]`. Mathlib's
  `IsNoetherian` combines local Noetherianity and compactness.
- Quasi-coherent ideal I: `(I : X.IdealSheafData)`, the same bundled ideal used
  in the formal-module dependency. No abstract mono or replacement ideal is used.
- Every open U is Noetherian: the existential witness
  `hN : ∀ U : X.Opens, IsNoetherian U.toScheme`. This is a conclusion, not an
  additional assumption. Mathlib does not synthesize this instance automatically.
- The restricted quasi-coherent ideal is `I.comap U.ι`, whose type is the ideal
  sheaf data of the open scheme. Pullback along an open immersion is restriction.
- Well-defined restriction on formal modules: the family `ρ` has domain
  `CoherentFormalModule X I` and codomain the same category on U and its restricted
  ideal. Existentially specifying the functor is part of the theorem's
  well-definedness assertion; there is no hollow definition.
- The functor is specifically termwise restriction on both objects and arrows:
  `ρ U ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
  (IsCoherentFormalModule I).ι ⋙
  (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
  (Scheme.Modules.restrictFunctor U.ι)`.
  The full-subcategory inclusion forgets only the property proofs. Equality of
  these functors fixes the underlying inverse systems, their transitions, and
  every morphism, not merely the isomorphism classes of their levels.
- Additivity: `(ρ U).Additive` for every open U.
- Preservation of short exact sequences: for every `S : ShortComplex
  (CoherentFormalModule X I)`, `S.ShortExact` implies that its map is short exact.
- Arbitrary open covering: `(J : Type v) (U : J → X.Opens)` and `iSup U = ⊤`.
  The index universe v is independent; neither finiteness nor nonemptiness is
  assumed for a cover.
- Maps beta and alpha with alpha composed with beta zero: exactly `S.f`, `S.g`,
  and `S.zero` for an arbitrary short complex S. Every such pair defines one.
- Exactness at the middle object iff exactness after all restrictions:
  `S.Exact ↔ ∀ j, (...map... S (ρ (U j))...).Exact`.
- The final five-term short exactness equivalence:
  `S.ShortExact ↔ ∀ j, (...map... S (ρ (U j))...).ShortExact`.
  Mathlib's predicate includes middle exactness, monicity of f and epicity of g.
- `hz` is an existentially supplied proof of preservation of zero morphisms,
  needed by Mathlib's `ShortComplex.map`; it places no extra hypothesis on X,
  I, the covering or the sequence. Its truth follows from the asserted additivity.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `IsNoetherian`; the former is the recorded declaration for pqf-def-locnoeth.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentFormalModule`,
  `IsCoherentFormalModule`, and its full-subcategory inclusion, recorded by
  def-weil-pbc-coherent-formal-module. The index `op n` means level n+1.
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`:
  `coherentFormalModule_abelian`, the recorded theorem asserting nonempty
  abelian structure and the termwise cokernel property. Imported directly.
  Exact and ShortExact can be stated without choosing that abelian structure.
- `Mathlib.Algebra.Homology.ShortComplex.Exact` and `.ShortExact`:
  `CategoryTheory.ShortComplex.Exact` and `ShortExact`, the exact-sequence
  dependency's recorded Mathlib notions. Their full signatures and docstrings
  were read. Exact is equivalent to image=kernel in the abelian category.
- Mathlib's `Scheme.IdealSheafData.comap`, `Functor.whiskeringRight`, and
  `Scheme.Modules.restrictFunctor` give the existing restriction operations.

Edge cases checked: U empty and U=X; X empty; zero formal modules; arbitrary
(including infinite) covering index types. An empty covering satisfies `iSup U=⊤`
only for the empty scheme, where locality has the expected vacuous meaning.
No level-zero annihilation condition is introduced: the existing formal module
encoding uses levels n+1 throughout. A formal-module kernel is not asserted to
be termwise injective, which would be false; all exactness is categorical.
No characteristic, separatedness, base or finite-cover condition was added.

Searches executed using `/home/ubuntu/weil-launcher/msearch.py` (the sandbox's
`searches.jsonl` records the actual outputs):

- LeanSearch: "restriction of coherent formal modules to opens is exact and
  exactness is local on an open cover". Service returned Internal Server Error;
  unavailable, so no mathematical verdict is inferred from this search.
- LeanFinder: "restriction of inverse systems of coherent modules is exact".
  Eight hits: adic completion exactness, condensed exactness, Nobeling results
  and linearMap_rangeRestrict; none is about formal coherent module restriction.
- Loogle: `CategoryTheory.ShortComplex.Exact`. Found the exactness predicate and
  its general categorical consequences, not this geometric statement.
- Mathlib grep: `CoherentFormal|IsCoherentFormal` in AlgebraicGeometry: no hits.
- Source repository rg for `CoherentFormal` and this item's id: no hits.
- Project rg for `CoherentFormalModule`, `coherentFormalModule`, and restriction:
  found the existing definition, abelianity, stabilized-kernel, affine-equivalence,
  and isomorphism-local modules. None states the item's locality of exactness.
  The isomorphism-local module uses the same ordinary module restriction functor.

Source checked: https://stacks.math.columbia.edu/tag/087X (parts (2) and (3),
with the full proof). The named local TeX file is absent on this machine, so the
Stacks primary source was read online. It agrees with the node. The docstring
records all five proof steps, including the stabilized-kernel argument and the
local epi/kernel-lift criterion. No statement correction, disputed statement,
new node, or dependency replacement is needed.

Validation: server single-file compilation passed cleanly in 1.8 seconds.

## Second reading by N1

Read the sandbox node and Lean independently, the four statement-dependency nodes
and their recorded source declarations, and Stacks `coherent.tex`, section
`section-coherent-formal` (lines 6248 onward), lemma
`lemma-inverse-systems-abelian` (6313 onward), including its kernel construction
and final sentence. The local literature checkout is absent; downloaded the
primary Stacks TeX into this item's scratchpad. The section-wide assumptions are
exactly Noetherian X and a quasi-coherent ideal, with positive-index coherent
adic inverse systems. Online tag 087X was also checked.

Object/hypothesis/conclusion inventory and individual verdicts:

1. X is an arbitrary Noetherian scheme: `X : Scheme.{u}` and `[IsNoetherian X]`.
   Read Mathlib's class: locally Noetherian plus `CompactSpace X`, precisely the
   node's locally Noetherian plus quasi-compact convention. MATCH.
2. I is a quasi-coherent ideal subsheaf: `I : X.IdealSheafData`. Read its
   affine-ideal localization data and `comap` in Mathlib, not merely their names.
   This is the dependency's same bundled ideal; no extra finiteness assumption.
   MATCH.
3. Coh(X,I) and its morphisms: `CoherentFormalModule X I`. Read
   `IsCoherentFormalModule`: coherent levels, annihilation by I^(n+1), and the
   specified induced quotient isomorphism recovering the transition. The full
   subcategory of `ℕᵒᵖ ⥤ X.Modules` has compatible natural transformations as maps.
   `op n` represents positive level n+1. MATCH.
4. For every open U, the open subscheme is Noetherian: existential
   `hN : ∀ U : X.Opens, IsNoetherian U.toScheme`; this is a conclusion and supplies
   the dependency category's instance, never an added hypothesis. MATCH.
5. The ideal restricted to U remains quasi-coherent: `I.comap U.ι` has type
   `U.toScheme.IdealSheafData`. Its pullback-ideal definition along the open
   immersion is the restriction of I, including its scheme structure. MATCH.
6. Well-defined restriction on objects AND arrows: existential functor family
   `ρ`, with equality after the full-subcategory inclusions to whiskering by
   `Scheme.Modules.restrictFunctor U.ι`. Read that functor's source: it is module
   restriction along an open immersion, with sections on an open identified with
   sections on its image. Equality of the whole functors fixes the inverse
   systems, transitions and maps. A lift into the full subcategory supplies the
   defining property proofs; no unknown data is defined with sorry. MATCH.
7. Additive restriction: `∀ U, (ρ U).Additive` in the first conjunction. MATCH.
8. Carries every short exact sequence to a short exact sequence: `∀ S,
   S.ShortExact → (S.map (ρ U)).ShortExact`, with the explicit zero-preservation
   witness `hz U`. Read `ShortComplex.ShortExact`: exact, mono first arrow, epi
   second arrow. MATCH.
9. Arbitrary open covering: `∀ (J : Type v) (U : J → X.Opens), iSup U = ⊤ → ...`.
   No nonempty or finite-cover hypothesis. MATCH.
10. Objects A,B,C and arrows beta,alpha with alpha beta = 0: arbitrary
    `S : ShortComplex (CoherentFormalModule X I)`; its three objects, `f`, `g`
    and `zero` give exactly those data. MATCH.
11. Exact at B iff exact at every restricted B: `S.Exact ↔ ∀ j, ...Exact`.
    Read `ShortComplex.Exact`: existence of zero homology data; in the abelian
    category this is image equals kernel, as the recorded exact-sequence node
    specifies. Read `coherentFormalModule_abelian`: it supplies the abelian
    structure on precisely this category, not another inverse-system category.
    No termwise-kernel or termwise-injectivity condition is substituted. MATCH.
12. Five-term short exactness iff short exactness on each covering member:
    `S.ShortExact ↔ ∀ j, ...ShortExact`. Both end conditions are included. MATCH.
13. Quantifier order: one family of restrictions works for all opens, covers and
    short complexes. `hz` is an existential conclusion about these same functors,
    following from additivity and enabling `ShortComplex.map`; it imposes no
    hypothesis on the geometric data. MATCH.

Edge cases: empty U, U=top and empty X are included. An empty covering has
`iSup U=top` only on the empty space; all module sheaves there are zero, so the
vacuous local tests have the expected result. Zero modules and zero complexes
are included. There is no positive lower bound on a Lean index: n=0 is source
level 1, and source level 0 is not imposed. Zero and unit ideals are allowed.
No characteristic, base field, separatedness or additional Noetherian condition
is added. `u` is arbitrary and the covering index universe `v` is independent;
this is a cover, not a filtered-colimit indexing universe restriction.
All variables and universes are explicitly bound.

Independent searches (actual calls recorded in searches.jsonl):

- LeanFinder: "adic sheaf systems restriction detects exact complexes on a
  covering" returned Mayer-Vietoris square exactness, degreewise exactness of
  homological complexes, condensed exact limits, adic completion exactness and
  module localization exactness. None concerns Coh(X,I) restriction/locality.
- Loogle: `CategoryTheory.Functor.Additive` found the additive predicate and its
  general categorical consequences, not this geometric theorem.
- LeanSearch: "An adic inverse system of coherent sheaves has exact restriction
  functors and exactness descends from open covers" returned unavailable
  (Internal Server Error); no negative verdict inferred from this service.
- `rg` for adic sheaf systems, formal restriction/exactness, and the full
  declaration name in Mathlib, WeilConjectures and project Lean. Also searched
  `coherentFormal`, `CoherentFormal` and `IsCoherentFormal` in the source and
  Mathlib AlgebraicGeometry: no declaration there of this notion or theorem.
  The project's landed formal-module definition and abelianity are used.
  Opened `CoherentFormalModuleIsomorphismLocal.lean`: its conclusion is locality
  of isomorphisms, not locality of exactness, and it uses the same restriction.
  No duplicate definition or existing exact statement was found.

No mismatch found; no Lean or node changes. There are no new definition nodes,
dependency replacements or statement corrections to review. The module has
one theorem with `sorry`, no proved theorem, no hollow definition, no local
notation or private alias. Its source docstrings and five proof steps match
all five node proof steps, including stabilized kernels and the local
kernel-lift/cokernel argument. Kept the correct statement unchanged.

Second-reader validation: server single-file compilation passed in 2.0 seconds,
with no warnings or errors. Checked that lean.statement equals the full source
signature verbatim and all module lines have at most 100 characters.
