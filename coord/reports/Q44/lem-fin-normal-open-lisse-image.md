## Worker report

The module `Sheaf.AlgebraicGeometry.NormalOpenLisseImage` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open`.
Its sole theorem has proof `by sorry`. No definition or additional theorem is introduced.
The node copy changes only `lean`; its mathematical statement and dependencies are unchanged.

The hypothesis and conclusion correspondence is:

- “over a field”: `{K : Type u} [Field K]` and `[X.Over (Spec (.of K))]`.
  This uses the scheme-over-base convention, without choosing a new named structure map.
- “X integral”: `[IsIntegral X]`, Mathlib's existing scheme-integrality class.
- “of finite type”: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`. Both conditions are retained; neither separatedness
  nor a Noetherian assumption is added.
- “k : V ↪ X is an open”: `(k : V ⟶ X) [IsOpenImmersion k]`, with
  `{X V : Scheme.{u}}`. An arbitrary open immersion allows exactly an open subscheme up to
  its canonical isomorphism, without a special affine or principal-open restriction.
- “nonempty normal”: `(hV : IsNormalScheme V)`. The recorded definition is
  `IsIntegral V ∧ ∀ v, IsDomain (V.presheaf.stalk v) ∧
  IsIntegrallyClosed (V.presheaf.stalk v)`. Its `IsIntegral V` clause already includes
  `Nonempty V`, so no separate duplicate nonemptiness hypothesis is needed.
- “over a finite ring”: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
  Commutativity is the dependency's coefficient convention and is explicit in the node's
  proof; finiteness is finiteness of the underlying set.
- “module sheaf L”: `(L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  This is the fixed-coefficient module-valued encoding prescribed for constructible sheaves
  by `def-weil-pbc-etale-sheaves`, not a structure-sheaf-module category.
- “finite locally constant”: `[IsFiniteLocallyConstantSheaf L]`, the exact declaration of
  `def-constructible-finite-locally-constant`. It extends local constancy and finite stalks
  in the finitely generated module sense. Over finite Λ these are finite sets.
- “k_* L”: `(Etale.lowerStar (ModuleCat.{u + 1} Λ) k).obj L`, the recorded canonical
  direct image, whose value on an etale W over X is L on W ×_X V.
- “is constructible”: `IsConstructibleEtaleModuleSheaf` of that direct image, exactly the
  dependency's finite stratification with finite constant module charts. The conclusion
  uses the module-sheaf constructibility predicate, rather than set constructibility.

Dependency declarations read and used:

- `def-sbc-normal-dominant-galois`: module `Sheaf.AlgebraicGeometry.NormalScheme`,
  `AlgebraicGeometry.IsNormalScheme`; also Mathlib `AlgebraicGeometry.IsIntegral`.
  The normality definition and its docstring were read locally and confirmed using
  `scompile.py --source Sheaf.AlgebraicGeometry.NormalScheme`.
- `def-weil-pbc-scheme-conventions`: a convention record with no owning declaration or
  module. The relevant existing definitions are `AlgebraicGeometry.Scheme`,
  `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsOpenImmersion`.
  Mathlib's finite-type and quasi-compact definitions and integrality class were inspected.
- `def-weil-pbc-etale-sheaves`: module `WeilConjectures.AlgebraicGeometry.EtaleSheaves`,
  with the prescribed module sheaf encoding `Sheaf _ (ModuleCat Λ)` from its node record.
  Its source/docstrings and the referenced category-valued sheaf conventions were read.
  Its set-valued predicates are not substituted for module local constancy.
- `def-constructible-finite-locally-constant`: module
  `WeilConjectures.ConstructibleSheaf.Defs`,
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`. Its full class and parent-class
  signatures and docstrings were read, including the geometric-stalk finiteness convention.
- `def-weil-pbc-etale-constructible-sheaf`: module
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`. The full body and docstring
  were read locally and confirmed with `scompile.py --source`.
- `def-weil-pbc-direct-image`: module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`. Its full signature, objectwise formula and docstring
  were read in the upstream source.

All stated proof dependencies' recorded modules are imported without `public`, except for
those already imported publicly as statement dependencies. Mathlib leaves contribute their
source modules. The three proof-only nodes without a Lean record in the read snapshot are
`fin2-lem-lisse-trivialized-finite-etale`, `lem-fin-normalization-extends-cover`, and
`lem-fin-normal-constant-open-image`; these are not required to type the statement and their
proof steps remain explicitly documented. The theorem docstring follows all seven steps of
the node, naming the relevant DAG dependencies: finite etale trivialization, the monic unit,
finite generic extensions, finite normalizations, the injection into finite pushforwards,
constructibility of that target, and the Noetherian subobject conclusion.

Edge cases checked before writing: empty X and empty V are excluded by the stated
integrality and normality hypotheses, respectively. The identity open V = X is allowed.
The zero sheaf and the zero coefficient ring are allowed. There is no restriction on the
characteristic of K, no invertibility or prime-to-characteristic condition on Λ, and no
smoothness, properness, or separatedness assumption on X. No finiteness condition on the
boundary or affine hypothesis is added. The universes are the recorded small-etale convention:
schemes and the field in universe u, coefficient ring and module values in u+1.

Searches made with the prescribed `msearch.py` wrapper (recorded in sandbox searches.jsonl):

- LeanFinder, query “The direct image of a finite locally constant etale module sheaf along
  a nonempty normal open immersion into an integral scheme of finite type over a field is
  constructible”: 8 hits, all about constructible subsets (scheme images, preimages and
  prime spectra). None states constructibility of a sheaf direct image.
- Loogle, query `"IsConstructibleSheaf", "lowerStar"`: zero hits.
- Mathlib grep, query `constructible.*(lowerStar|pushforward)|normal.*open.*constant`,
  subdirectory `AlgebraicGeometry`: zero hits.
- LeanSearch, query “The direct image of a finite locally constant etale module sheaf from
  a normal open subscheme of an integral scheme of finite type over a field is constructible.”:
  service unavailable, Internal Server Error. The other search services and local grep ran.
- Local `rg` of the exact node id and proposed declaration name through upstream
  `WeilConjectures/`, project `lean/Sheaf/`, and `dag/lean_names_upstream.json`: zero hits.
- Local `rg` for `normal.{0,80}open.{0,80}(lisse|constructible)`,
  `constructible.{0,80}normal.{0,80}open`, and
  `open.{0,80}normal.{0,80}(lisse|constructible)` through upstream and project Lean: zero hits.
  Broader topic searches found normal-open existence, constant-open units, and finite-map
  pushforward theorems; none has this node's statement.

The blueprint markdown path named by the node is absent from this read-only local checkout;
the node's full statement and seven-step expanded proof were read. No source-based correction
was needed or made. There are no new nodes, dependency repairs, or mathematical statement
faults identified.

Validation: `scompile.py Q44 lem-fin-normal-open-lisse-image
lean/Sheaf/AlgebraicGeometry/NormalOpenLisseImage.lean` compiled both the sandbox probe and
library module cleanly, with no errors or unexpected warnings. The required delivery dry run
is the final validation step; the independent second reader will write its own section.

## Second reading by Q44

I reread the item node, its source place, the recorded statement dependencies, and
`lean/Sheaf/AlgebraicGeometry/NormalOpenLisseImage.lean` independently of the worker
report. The source place is the blueprint file
`sec-smooth-purity/sk-prop-a1-kummer/lem-fin-normal-open-lisse-image.md`, whose statement
has exactly these clauses:

- An integral scheme `X` of finite type over a field.
- A morphism `k : V ⟶ X` that is an open immersion, with `V` a nonempty normal open.
- A finite locally constant module sheaf `L` over a finite (commutative) coefficient ring.
- The conclusion that the direct image `k_* L` is constructible.

The Lean rendering is, item by item:

- `{K : Type u} [Field K]` and `{X V : Scheme.{u}} [X.Over (Spec (.of K))]` render a
  field and schemes over its spectrum.
- `[LocallyOfFiniteType (X ↘ Spec (.of K))]` together with
  `[QuasiCompact (X ↘ Spec (.of K))]` is the recorded finite-type convention; no
  separatedness, noetherianity, or other extra finiteness hypothesis is assumed.
- `(k : V ⟶ X) [IsOpenImmersion k]` renders the open immersion.
- `(hV : IsNormalScheme V)` unfolds to `IsIntegral V` and integrally closed domain
  stalks, so it includes the source's nonemptiness and normality requirements.
- `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]` renders the finite commutative ring,
  and `L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)` is the recorded module
  sheaf encoding.
- `[IsFiniteLocallyConstantSheaf L]` renders finite local constancy.
- The conclusion is exactly
  `IsConstructibleEtaleModuleSheaf
  ((Etale.lowerStar (ModuleCat.{u + 1} Λ) k).obj L)`, the constructibility of `k_* L`.

Verdict: every object, hypothesis, universe, quantifier, and conclusion clause agrees
with the node and source. I found no mismatch and made no mathematical change.

Edge cases checked: the empty `X` and empty `V` are excluded exactly where the source
requires them (`IsIntegral X` and `IsNormalScheme V`); the identity open is allowed; the
zero sheaf and zero coefficient ring are allowed; `n = 0` does not occur; and no
characteristic, smoothness, properness, separatedness, or prime-to-characteristic
condition is added. The scheme universe is `u`, while the coefficient and module-value
universe is `u + 1`, as required by the dependency convention.

Searches: the worker's LeanFinder, Loogle, LeanSearch, Mathlib grep, upstream grep, and
project grep were reread in `searches.jsonl`. They found no existing declaration of this
statement or notion; LeanSearch was unavailable, while all other searches returned no
matching direct-image constructibility theorem. The existing declarations used by the
module (`IsNormalScheme`, `IsFiniteLocallyConstantSheaf`,
`IsConstructibleEtaleModuleSheaf`, and `Etale.lowerStar`) were opened and match their
recorded dependency nodes. No new definition node, dependency module, statement
correction, or citer audit is needed.

The module compiled cleanly with the required command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q44 lem-fin-normal-open-lisse-image
lean/Sheaf/AlgebraicGeometry/NormalOpenLisseImage.lean`.
