## Worker report

The module `Sheaf.RingTheory.LocalColimitResidueField` states
`CommRingCat.local_colimit_residue_field`, with its single proof `sorry`.
It has no definitions and no auxiliary postponed theorems. The existing node is
unchanged except for `lean`; no statement correction, new node or dependency repair
is needed. `autoImplicit` is disabled, and all variables and universes are explicit.

Source read: `literature/stacks-project/algebra.tex`, Tag 04GI,
`lemma-colimit-henselian`, especially lines 42926–42940. The proof explicitly says
that the local-ring colimit is local and that its residue field is the colimit of
the stage residue fields, with this argument omitted. The node expands precisely
that algebra assertion. Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/` followed by
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
The algebra input serves its open-direct-image branch via the recorded root-tower
chain; it adds no global assumption from the henselian application.

Hypothesis and clause correspondence:

- Nonempty small directed poset: `{I : Type u} [PartialOrder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. Mathlib's category of a preorder represents exactly the
  order arrows. The index and ring-carrier universe are the same, following the
  project's colimit size convention; `u` is arbitrary.
- Direct system of commutative local rings: `F : I ⥤ CommRingCat.{u}` and
  `[∀ i : I, IsLocalRing (F.obj i)]`. Functor identities provide exactly the system
  identities. Mathlib's local rings are nonzero and have a unique maximal ideal,
  as in the node. No henselianity is assumed.
- Locality of every transition map: `[∀ (i j : I) (f : i ⟶ j),
  IsLocalHom (F.map f).hom]`. For local rings this is equivalent to
  `(maximalIdeal (F.obj j)).comap (F.map f).hom = maximalIdeal (F.obj i)`;
  see `IsLocalRing.local_hom_TFAE` and `IsLocalRing.maximalIdeal_comap`.
  Thus this binder is exactly the stated inverse-image equality, not an extra
  injectivity or surjectivity condition. These Prop-valued instances are quantified
  hypotheses, not file-local instances or chosen extra data.
- The specified colimit `(A, α)`: `(c : Cocone F) (hc : IsColimit c)`; its ring is
  `c.pt`, and its structure maps are `(c.ι.app i).hom`. This retains an arbitrary
  given colimit rather than specializing to one concrete quotient construction.
- Locality of A and all α: the conclusion first supplies
  `∃ (_ : IsLocalRing c.pt) (_ : ∀ i : I, IsLocalHom (c.ι.app i).hom), ...`.
  These are proofs of properties, used as instances in the remainder of the
  proposition, not arbitrary ring or map choices.
- M is the union of the images of the stage maximal ideals, and is the unique
  maximal ideal: the set equality
  `(IsLocalRing.maximalIdeal c.pt : Set c.pt) = ⋃ i : I,
  (c.ι.app i).hom '' (IsLocalRing.maximalIdeal (F.obj i) : Set (F.obj i))`.
  The left side is an actual ideal with its maximality and uniqueness supplied by
  `IsLocalRing c.pt`; consequently the equality asserts ideal closure as well as
  the desired maximality of the raw union. It does not replace the union by the
  generally larger sum/span of image ideals.
- Contraction under every α: the next conjunct is
  `∀ i, (IsLocalRing.maximalIdeal c.pt).comap (c.ι.app i).hom =
  IsLocalRing.maximalIdeal (F.obj i)`.
- Fields k_i and k: `IsLocalRing.ResidueField (F.obj i)` and
  `IsLocalRing.ResidueField c.pt` are definitionally the quotients by their maximal
  ideals, equipped by Mathlib with their canonical field structures. The proved
  set equality identifies the latter quotient with the node's `A/M`.
- Well-defined field homomorphisms on transitions and cocone legs: the statement
  uses the existing ring homomorphisms
  `IsLocalRing.ResidueField.map (F.map f).hom` and
  `IsLocalRing.ResidueField.map (R := F.obj i) (S := c.pt) (c.ι.app i).hom`.
  Their bodies are the quotient lifts `[x] ↦ [u(x)]` required by the node.
  Between fields, a unital ring homomorphism is a field homomorphism.
  `map_residue` gives the stated formula on representatives, and `map_id` and
  `map_comp` give the residue diagram identities and cocone compatibility using
  the original functor/cocone identities. These well-definedness and functoriality
  facts are already part of the existing API, not extra assumptions.
- Injectivity of each ρ_i: the third conjunct is
  `∀ i, Function.Injective (IsLocalRing.ResidueField.map ... (c.ι.app i).hom)`.
- Colimit of the residue diagram in commutative rings: the final conjunct
  quantifies over every `B : CommRingCat.{u}` and every family
  `h : ∀ i, IsLocalRing.ResidueField (F.obj i) →+* B`. Compatibility is precisely
  `(h j).comp (IsLocalRing.ResidueField.map (F.map f).hom) = h i` for every order
  arrow. The conclusion is `∃! g : IsLocalRing.ResidueField c.pt →+* B,
  ∀ i, g.comp (IsLocalRing.ResidueField.map ... (c.ι.app i).hom) = h i`.
  This writes the full categorical colimit universal property explicitly, using
  the dependency's meaning of colimit, without inventing another diagram
  construction. B is a commutative ring, not restricted to fields or nonzero rings.
- The final exclusion of injectivity, surjectivity, flatness and finiteness
  hypotheses is honored: none occurs among the hypotheses.

Dependencies read and used:

- `def-weil-pbc-category-colimit`: recorded module
  `Mathlib.CategoryTheory.Limits.HasLimits`, declaration
  `CategoryTheory.Limits.colimit`, and its recorded `Cocone`/`IsColimit` API.
  Read `HasLimits.lean` lines 168–190 and the full structures/docstrings in
  `Limits/Cones.lean` lines 125–138 and `Limits/IsLimit.lean` lines 59–71.
  The statement publicly imports this recorded module and uses the arbitrary
  cocone form of exactly its universal property.
- Proof-only `lem-pc-filtered-colimit-commrings-elementwise`: the recorded
  Mathlib matches are `Concrete.isColimit_exists_rep` and
  `Concrete.isColimit_rep_eq_iff_exists` in
  `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, with the instance
  `CommRingCat.FilteredColimits.forget_preservesFilteredColimits` in
  `Mathlib.Algebra.Category.Ring.FilteredColimits`. Read the complete signatures,
  surrounding binders and implementation at lines 113–180 and 350–365 respectively.
  Both modules are imported without `public` for the planned proof.
- Proof-only `lem-weil-pbc-local-ring-unit-criterion`: its recorded match
  `IsLocalRing.notMem_maximalIdeal`,
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`, lines 78–84 (including
  its docstring). It is imported without `public` as required.
- Existing Mathlib notions: `CommRingCat` from `Algebra.Category.Ring.Basic`;
  the order category from `CategoryTheory.Category.Preorder`;
  `IsLocalRing.ResidueField`, `residue`, and its canonical field instance from
  `RingTheory.LocalRing.ResidueField.Defs`; canonical maps and their formula,
  identity and composition laws from `RingTheory.LocalRing.ResidueField.Basic`,
  lines 93–136; locality equivalence from `LocalRing.RingHom.Basic`, lines 84–107.
  All were read in source. There is no private copy of these notions.

Edge cases checked before writing:

- Empty I is excluded by the node and `[Nonempty I]`; it is necessary because
  the empty union is not the maximal ideal of the initial ring.
- A singleton diagram gives its original local ring, ideal and residue field.
- Systems of fields are allowed: the maximal ideals and their union are zero.
- The noninjective local quotient Z/4 → F₂ is permitted; nothing relies on
  injectivity of transition or structure maps on the original rings.
- Z_(p) → Q is correctly excluded because it does not contract the zero maximal
  ideal to (p). A local ring stage itself cannot be the zero ring, consistently
  with the unique-maximal-ideal hypothesis.
- The colimit universal property allows the zero target ring B; the unique zero
  homomorphisms satisfy the quantified clause. There is no accidental assumption
  that B is a field.
- No characteristic, flatness, finiteness, or henselianity restriction is present.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder`: "A directed colimit of local rings and local
  homomorphisms is local and its residue field is the colimit of the residue
  fields". Eight hits, including `ResidueField.map`, `map_residue`, `lift`,
  `residue`, and residue-field instances; no theorem carrying the complete node.
- `msearch.py ... loogle "IsLocalRing, DirectLimit"`: zero hits.
- `msearch.py ... grep
  "(colimit|DirectLimit).*(local|residue)|(local|residue).*(colimit|DirectLimit)"
  RingTheory`: zero hits.
- `msearch.py ... leansearch`: "The residue field of a directed colimit of local
  rings along local homomorphisms is the colimit of the residue fields".
  Eight hits, including the residue-field definitions and maps and
  `Ring.DirectLimit.commRing`; none supplies locality, the union description and
  this residue colimit property together.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for local/colimit and
  residue/colimit combinations, and colimit declarations in both RingTheory
  directories, found specialized strict-henselization and model-tower material,
  not this arbitrary local-ring colimit theorem.
- `rg` for the exact item id in `lean/WeilConjectures` returned no match.
  `rg` for `localColimitResidueField|local_colimit_residue_field` in
  `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`
  returned no match. Thus the proposed full declaration name is new.
- Searched the Mathlib residue/functor APIs, read the quotient map implementation
  and its full signatures, and reused them rather than introducing a helper.

Validation: prescribed `scompile.py` compiled both the sandbox version and the
intended library module cleanly (1.2 s and 1.1 s). The initial instance-resolution
failure on the constant-functor target of a cocone leg was fixed by explicitly
supplying `(R := F.obj i) (S := c.pt)` to the existing residue-map constructor.
The final dry run recompiles the module with auto-implicit binding disabled.
No mathematical statement fault or disputed assertion was found.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
