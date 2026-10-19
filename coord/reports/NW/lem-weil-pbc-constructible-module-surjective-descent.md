## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleModuleSurjectiveDescent` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_of_surjective_pullback`.
Its only proof is `sorry`; no definition or auxiliary theorem was added.

Read the complete item, all six statement dependencies and their recorded declarations,
the proof dependency, the stage-2 brief, stage document, worker role, delivery-errors H,
and the CompactObject example. Read the local Stacks source `etale-cohomology.tex`,
`lemma-check-constructible` (Tag 095Q), lines 12276–12324: part (3) asserts the iff for a
Noetherian ring. A finite commutative ring is Noetherian; finite-generation and finite-value
formulations agree for its modules. The node correctly specializes the converse.

Hypothesis and conclusion correspondence:

- Schemes T and U: `{T U : Scheme.{u}}`; the universe `u` is explicitly declared.
- Quasi-compactness of both schemes: `[CompactSpace T] [CompactSpace U]`.
- Quasi-separatedness of both: `[QuasiSeparatedSpace T] [QuasiSeparatedSpace U]`.
- The named morphism a and its surjectivity on points: `(a : T ⟶ U) [Surjective a]`.
- A finite commutative coefficient ring: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
- The sheaf of Λ-modules on the small etale site of U:
  `(G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, the recorded constructible-module
  encoding authorized by the etale-sheaves dependency and brief-stage2 §2.
- Constructible inverse image: `hG : IsConstructibleEtaleModuleSheaf
  ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj G)`.
- Conclusion: `IsConstructibleEtaleModuleSheaf G`. The identical predicate on both sides
  is the recorded finite locally closed constructible stratification definition, with
  finite locally constant values as module sheaves, not merely as underlying sets.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  read their complete definitions and docstrings at lines 36–48 and 73–76.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`,
  read lines 53–60; its sole field is surjectivity of the map on points.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`; read its variables, full signature and construction
  and the preceding docstring. It accepts arbitrary scheme morphisms with no etaleness,
  flatness, properness or finite-presentation hypothesis.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`; read the entire module.
  It quantifies over `LocallyClosedStratification`, requires constructible parts, and uses
  `upperStar`, `LocallyConstantDatum`, and finite constant module values.
- The etale-sheaves dependency records several encodings. Its module-sheaf clause here
  uses the existing `CategoryTheory.Sheaf` and `ModuleCat`, already available through
  the constructibility import. The locally constant set-valued declarations of that
  mixed dependency are not used. The available local `EtaleSheaves.lean` source and its
  definitions were read; the canonical upstream module path in its record is absent
  in this source snapshot. This does not require that unused set-valued module here.
- The scheme-conventions dependency explicitly defines no new notion; its qcqs scheme
  convention is rendered by the two topological instances for each scheme.

The sole proof dependency `lem-weil-pbc-etale-constructible-surjective-pullback` has no
Lean record yet, so there is no proof-only module to import. The docstring carries its
one-step specialization argument, ready for stage 3.

Edge cases checked: neither scheme is required nonempty; the empty-to-empty morphism
and zero module sheaf are admitted. No nontriviality hypothesis excludes the zero ring.
Identity morphisms give the expected self-implication. There is no assumption on a beyond
surjectivity; in particular no flatness, etaleness, or finite presentation was added.
The chosen coefficient universe is the recorded definition's universe and represents
any finite ring up to transport. No index sets or strata are chosen by this theorem,
so empty stratifications retain the definition's behavior. No statement correction or
dispute is needed.

Searches run for this item:

- `msearch.py ... leanfinder "Constructibility of etale module sheaves descends along a
  surjective morphism of quasi compact quasi separated schemes"`: eight hits, concerning
  etale morphisms and constructible images of subsets, none stating sheaf descent.
- `msearch.py ... loogle "IsConstructibleSheaf, Surjective"`: zero hits, unknown identifier
  `IsConstructibleSheaf` in the Mathlib index.
- `msearch.py ... leansearch "constructible etale sheaf surjective pullback descent"`:
  unavailable, Internal Server Error; this is not evidence of absence.
- `msearch.py ... grep "constructible.*surjective|surjective.*constructible"`: two hits,
  in prime spectrum constructible sets and constructible topology, neither sheaf descent.
- `rg` for `IsConstructibleEtaleModuleSheaf`, `surjective.*[Cc]onstructible`, and
  `[Cc]onstructible.*surjective` in project Sheaf and upstream WeilConjectures:
  found the existing predicate and its uses, but no descent declaration.
- `grep -rn` for the full node id in upstream WeilConjectures: no match.
- `rg` for the item id and proposed declaration in `dag/lean_names_upstream.json`,
  upstream WeilConjectures and project Sheaf: no match.

Validation: server compile through `scompile.py`; dry run through `deliver2.py --no-push`.
The second reader will add the independent reading and deliver; this worker does not push.

## Second reading by NW

Independently read the sandbox node and module against Stacks Tag 095Q,
`etale-cohomology.tex`, `lemma-check-constructible`, including its complete proof.
Its hypotheses are stated locally: a surjective morphism between qcqs schemes and,
in part (3), a Noetherian coefficient ring. No ambient field, characteristic,
separation, finite-presentation or flatness assumption is inherited. A finite
commutative ring is Noetherian. Also read 03RW and 095E: on a qcqs scheme the
source's affine-local definition is equivalent to the global constructible
locally closed partition used by this node. Over a finite ring, finite-type
modules have finite underlying sets, and finite modules are finitely generated.
Thus the node is the stated finite-ring converse of 095Q(3), without correction.

Object-by-object, hypothesis-by-hypothesis, and conclusion checklist:

- The schemes T and U are `{T U : Scheme.{u}}`. Verdict: exact. Read Mathlib's
  `Scheme` structure and `Scheme.Hom`: these are locally affine locally ringed
  spaces and their morphisms, as in `def-pc-scheme`.
- Each scheme is quasi-compact: `[CompactSpace T] [CompactSpace U]`. Verdict:
  exact topological quasi-compactness; no Hausdorff hypothesis is present.
- Each scheme is quasi-separated: `[QuasiSeparatedSpace T] [QuasiSeparatedSpace U]`.
  Verdict: exact. Read `def-weil-pbc-scheme-conventions`, which collects the
  existing notions and introduces no further structure or declaration.
- The specified morphism is `(a : T ⟶ U)`, with `[Surjective a]`. Verdict: exact.
  Opened the surjectivity dependency and Mathlib's `UnderlyingMap.lean`:
  `Surjective.surj` is precisely `Function.Surjective a` on underlying points.
  No condition on local rings or geometric points replaces this assumption.
- The coefficient ring is `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
  Verdict: exact finite commutative ring, including the zero ring; no field or
  nontriviality instance has been introduced.
- The module sheaf G on U's small etale site is
  `(G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Verdict: exact.
  Read the etale-sheaves dependency's full statement and mixed Lean record:
  its note explicitly permits this coefficient-category encoding for the
  constructible/six-functor material. Its set-valued predicates are not used.
  The recorded `WeilConjectures.AlgebraicGeometry.EtaleSheaves` file is absent
  in this source snapshot; it supplies none of this signature's required
  declarations. `CategoryTheory.Sheaf` and `ModuleCat` are the actual objects.
- The inverse image is
  `((Etale.upperStar (ModuleCat.{u + 1} Λ) a).obj G)`. Verdict: exact.
  Opened `UpperLowerStar/Defs.lean`, including the section variables and the
  definition and adjunction: it is left Kan extension along base change
  followed by sheafification for arbitrary a. Its category-structure
  requirements are supplied for ModuleCat; no etale, flat or proper
  assumption is smuggled into the theorem.
- The hypothesis is `hG : IsConstructibleEtaleModuleSheaf` of that inverse
  image. Verdict: exact. Opened the recorded predicate's entire module and
  its `LocallyClosedStratification` dependency, and opened the upstream
  `LocallyConstantDatum` signature. The predicate chooses a finite partition
  by immersed locally closed schemes, requires constructible subsets, and
  requires module-sheaf isomorphisms with constant finite modules on an
  etale cover. It is the dependency node's notion, including module rather
  than merely set-valued local constancy; no private replacement occurs.
- The sole conclusion is `IsConstructibleEtaleModuleSheaf G`. Verdict: exact
  same predicate on the original G, with no extra conjunct or witness and
  with all objects fixed before the implication from hG.

Edge cases: no nonemptiness hypothesis excludes the empty scheme; a surjection
from an empty T forces U empty. The predicate's `Fin S.n` permits n = 0,
with partition coverage then forcing the empty underlying space. Empty etale
cover index types are allowed precisely where they cover an empty stratum.
The zero sheaf, zero ring and every finite-ring characteristic remain admitted.
There is no unrelated numeric parameter. Universe u is explicitly bound;
both schemes use the usual common scheme universe, and coefficients and
sheaf values use the dependency's u+1 convention. There is no quantification
over test schemes in a smaller universe and no extra size hypothesis. Different
initial scheme universes can be accommodated in a common larger universe;
finite coefficients introduce no restriction on possible ring isomorphism types.

Independent H4 searches (queries different from the first worker's):

- LeanFinder: "A sheaf of finite ring modules is constructible when its inverse
  image under a surjective scheme morphism is constructible". Eight results:
  scheme-image constructibility and finite-type module-sheaf predicates, none
  the inverse-image reflection theorem.
- Loogle: `"constructible", "pullback"`. No results.
- LeanSearch: "Surjective inverse image reflects constructibility of module
  sheaves". Service unavailable, Internal Server Error; no absence conclusion
  is drawn from this failed search.
- Search service grep: `constructible.*descent|constructible.*surjective|surjective.*constructible`.
  Two results, in constructible topology and prime spectra, neither this theorem.
- Direct rg in Mathlib, upstream WeilConjectures and project lean/Sheaf for
  constructible/descent/surjectivity/inverse-image combinations and for the
  exact predicate. Read the nearby upstream UniversalHomeomorphism and
  Refinement search hits: these descend finite local constancy along special
  morphisms, not constructibility along arbitrary qcqs surjections. Existing
  noetherian and limit descent statements also concern different conclusions.
  The recorded constructibility definition is reused. The exact proposed
  declaration and blueprint id have no source or upstream-name-table match.

There are no new definition nodes or dependency modules in this delivery, and
no statement_change or disputed statement. The sole proof dependency still has
no Lean record; the theorem docstring faithfully records its specialization,
the resulting iff, and the reverse implication applied to hG. All three imports
serve the signature. Both docstrings identify 095Q(3) and the blueprint node.
The module adds only the named theorem with `sorry`, no definitions or proofs.
No unbound variable, hidden let/show binder, file-local notation or oversized
line occurs. Programmatically checked that `lean.statement` is verbatim the
file's theorem signature. No mismatch found; Lean and node left unchanged.
Only this independent reading was appended to the worker report.

Validation: the delivered file compiled cleanly using server-side scompile.py:
1.4 seconds, nice 19, two threads, 60-second file limit; no errors or warnings.
