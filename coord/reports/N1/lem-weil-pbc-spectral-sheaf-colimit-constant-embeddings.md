## Worker report

The module `Sheaf.Topology.SpectralSheafColimitConstantEmbeddings` states
`TopCat.spectral_sheaf_colimit_constant_embeddings`, with its sole proof `sorry`.
It introduces no definitions. All variables and the universe `u` are explicitly bound.
No node statement or dependency list is changed.

The node's hypotheses and conclusions correspond as follows:

- A spectral space is `X : TopCat.{u}` with `[SpectralSpace X]`.
- A sheaf of sets is `F : X.Sheaf (Type u)`.
- The preliminary explanation of the constant sheaf on a closed subset is rendered
  literally in the target section types: the factor over an open `U` is
  `LocallyConstant {x : X // x ∈ U ∧ x ∈ Z k} (S k)`. The subtype topology is the
  topology of the intersection of the open with the closed subset. Restrictions are
  `LocallyConstant.comap` along its inclusion. Mathlib local constancy takes a bare
  coefficient type; no topology or nonemptiness is imposed on `S k`.
- The directed set is `I : Type u`, with `Preorder I`, `Nonempty I`, and
  `IsDirected I (· ≤ ·)`. The latter says any two indices have a common upper bound.
  The index universe is the objects' universe, not an independent smaller universe.
- The system of sheaves and transition maps is `D : I ⥤ X.Sheaf (Type u)`.
  A preorder is its thin category: `D.map (homOfLE h)` is the transition map for `h`.
  `D.map_id` and `D.map_comp` encode exactly the two system laws.
- The compatible morphisms to `F` are `ι : D ⟶ (Functor.const I).obj F`.
  Its components are the cocone morphisms, and naturality is precisely their
  compatibility with the transitions.
- Colimit with vertex `F` is `Nonempty (IsColimit (Cocone.mk F ι))`. This is the
  universal property in the category of sheaves, without asserting a sectionwise
  colimit or replacing `F` by an unspecified isomorphic vertex.
- For each `i`, the number of factors is `n : ℕ`, allowing zero. The subsets are
  `Z : Fin n → Set X`; their closedness and constructibility are
  `∀ k, IsClosed (Z k) ∧ Topology.IsConstructible (Z k) ∧ Finite (S k)`.
- The finite sets are `S : Fin n → Type u`, with `Finite (S k)` in that clause;
  no choice of enumeration and no inhabitedness is required.
- The product over each open is the dependent function type
  `(k : Fin n) → LocallyConstant {x : X // x ∈ U ∧ x ∈ Z k} (S k)`.
- The morphism into this sectionwise product is encoded by its full data:
  `e : ∀ U, (D.obj i).obj.obj (op U) → ((k : Fin n) → ...)`, together with the
  displayed equality for every restriction `f : V ⟶ U`, section `s`, and factor `k`.
  That equality is exactly the naturality condition, factor by factor. The inclusion
  used by `comap` sends `x` to `⟨x.1, f.le x.2.1, x.2.2⟩`.
  This data is equivalent to a presheaf natural transformation into the specified
  product. Its target is the actual sectionwise product of locally constant-map
  sheaves; since sheaf morphisms are underlying presheaf natural transformations,
  this expresses the stated sheaf morphism without defining another sheaf model.
- Injectivity on every open is `∀ U : Opens X, Function.Injective (e U)`.

Dependency declarations read and used:

- `def-weil-spectral-space`: `SpectralSpace`, from
  `Mathlib.Topology.Spectral.Basic`. Its class extends T0, compact, quasi-sober,
  quasi-separated and prespectral, matching uniqueness of generic points as well.
- `def-weil-constructible-subset`: `Topology.IsConstructible`, from
  `Mathlib.Topology.Constructible`, membership in the Boolean subalgebra generated
  by retrocompact opens.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and
  `CategoryTheory.Limits.IsColimit`, available through the recorded module
  `Mathlib.CategoryTheory.Limits.HasLimits`. The full signatures and docstrings of
  `Cocone`, `IsColimit`, and the generated chosen-colimit interface were read.
  An explicit cocone is used because this node fixes the colimit vertex to `F`.
- Mathlib's `TopCat.Sheaf` and `LocallyConstant`/`LocallyConstant.comap` give the
  other notions already spelled out in the node; no missing notion needs a node.

Edge cases checked before drafting: empty `X`; initial and terminal sheaves;
`n = 0` (the dependent product is a singleton, so the injection requires at most
one section over every open); empty `Z k` (again a singleton factor over each open);
empty finite `S k` (no global sections on a nonempty domain, but the empty open has
its unique empty map); singleton directed index; non-antisymmetric preorders.
Neither the embedding nor cocone asserts that transitions are injective.
No noetherian, separated, nonempty-space or nonempty-coefficient hypothesis is added.

Source read: the local `literature/stacks-project` sources are absent on this machine,
so the actual source was opened at [0CAI](https://stacks.math.columbia.edu/tag/0CAI),
[0CAL](https://stacks.math.columbia.edu/tag/0CAL), and
[09ZG](https://stacks.math.columbia.edu/tag/09ZG). The finite-subset construction in
0CAI gives a directed indexing set. 0CAL gives the finite closed constructible
constant-sheaf embedding, and 09ZG uses their combination. No statement fault or
statement dispute was found.

Searches for existing declarations:

- `msearch.py ... leanfinder`: “Every sheaf of sets on a spectral space is a directed
  colimit of subsheaves of finite products of pushed forward finite constant sheaves”.
  Eight hits, concerning condensed/LightCondensed locally constant colimits and
  topological-to-condensed comparison functors. None is this theorem.
- `msearch.py ... leansearch`: “Every sheaf of sets on a spectral space is a filtered
  colimit of sheaves embedding into finite products of closed pushforward constant
  sheaves”. The service returned UNAVAILABLE / Internal Server Error; no verdict
  is claimed for that search.
- `msearch.py ... loogle "LocallyConstant, Presheaf"`: zero hits; unknown identifier
  `Presheaf`. Follow-up `loogle "LocallyConstant.comap"`: twelve hits, confirming
  Mathlib's pullback of locally constant maps and its restriction laws, with no
  spectral-sheaf decomposition theorem.
- `msearch.py ... grep "LocallyConstant|constantSheaf" Topology/Sheaves`: zero hits.
  Direct `rg` for `LocallyConstant|locallyConstant` in Mathlib's Topology/Sheaves and
  CategoryTheory/Sites likewise found no literal locally constant sheaf construction.
- `rg` over `WeilConjectures` and project `lean/Sheaf` for spectral spaces, colimits,
  locally constant sections and constructibility found no existing statement.
  Relevant project encodings were read in `InverseImageClosedPushforwardConstant`,
  `ClosedPushforwardConstantRestriction`, and `SpectralClosedRestriction`; these
  concern restriction or inverse image, not this decomposition. The explicit
  locally constant section types follow those already used there.
- `rg` for the item id in `WeilConjectures` and `dag/lean_names_upstream.json`: no hits.
  `rg` for the chosen full declaration's suffix in Mathlib, `WeilConjectures`, and
  project `lean/Sheaf`: no collision.

Validation: `scompile.py N1 lem-weil-pbc-spectral-sheaf-colimit-constant-embeddings`
compiled the module on the server in 1.2 s, exit code 0, without warnings.

## Second reading by N1

I reread the node statement, its Stacks source (Modules Tags 0CAI and 0CAL, combined in
Etale Cohomology Tag 09ZG), the dependency records, and
`Sheaf/Topology/SpectralSheafColimitConstantEmbeddings.lean` independently.
The correspondence is as follows.

- The node's spectral space `X` is rendered by `(X : TopCat.{u}) [SpectralSpace X]`;
  this is the recorded Mathlib realization of `def-weil-spectral-space`.
- The sheaf of sets is `F : X.Sheaf (Type u)`, with the same universe as `X`.
- The directed index is `I : Type u` with `Preorder I`, `Nonempty I`, and
  `IsDirected I (· ≤ ·)`, exactly expressing a nonempty directed set in the index
  universe required for sheaves on `X`.
- The sheaf system is `D : I ⥤ X.Sheaf (Type u)`; its functor laws are precisely
  the transition identity and composition clauses in the node.
- The cocone maps are `ι : D ⟶ (Functor.const I).obj F`; naturality is their
  compatibility with every transition. `Nonempty (IsColimit (Cocone.mk F ι))`
  states the required colimit universal property with vertex exactly `F`.
- For each `i`, the factors are `n : ℕ`, `Z : Fin n → Set X`, and
  `S : Fin n → Type u`. The clause
  `IsClosed (Z k) ∧ Topology.IsConstructible (Z k) ∧ Finite (S k)` gives exactly
  constructible closed subsets and finite coefficient sets, with `n = 0` allowed.
- The factor over an open `U` is
  `LocallyConstant {x : X // x ∈ U ∧ x ∈ Z k} (S k)`, which is the node's
  locally constant maps on `U ∩ Z k`; the displayed subtype map in the final clause
  is restriction along `V ∩ Z k ↪ U ∩ Z k`.
- The embedding is represented by its section maps `e U`, with
  `∀ U, Function.Injective (e U)` and the displayed restriction equality. Since
  sheaf morphisms are natural transformations of the underlying presheaves, these
  clauses give exactly the required morphism into the sectionwise finite product and
  its injectivity on every open.

No extra Noetherian, separated, nonempty-space, inhabited-coefficient, or transition
injectivity hypothesis is present. Empty `X`, empty `Z k`, empty coefficient types,
zero factors (`n = 0`), singleton directed systems, and non-antisymmetric preorders
remain covered. The empty product is the singleton section type, as required by the
literal finite-product formulation.

I checked the dependency declarations: `SpectralSpace` is Mathlib's exact spectral
space class, `CategoryTheory.Limits.Cocone`/`IsColimit` provide the recorded colimit
notion, and `Topology.IsConstructible` is the recorded constructibility notion. I
searched Mathlib, `WeilConjectures`, and the project `lean/Sheaf` with `rg`, and used
`msearch.py`/LeanFinder queries for spectral sheaf colimits and locally constant
sheaves; no existing declaration states this theorem. The only related hits are
condensed locally constant-colimit results and generic sheaf colimit infrastructure.

No mismatch was found, so no source, statement, dependency, or Lean repair was needed.
The module compiles with `scompile.py` (exit code 0, no warnings other than permitted
`sorry` policy).
