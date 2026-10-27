## Worker report

The module `Sheaf.AlgebraicGeometry.StandardPhCompositeRefinement` states
`AlgebraicGeometry.Scheme.standard_ph_composite_refinement`, with one `sorry`
and no definitions or proved theorems. The node is unchanged except for `lean`.

Source read: `literature/stacks-project/topologies.tex`, Tag 0DBF,
`lemma-refine-by-standard-ph`, assertion (2), including the proof mislabelled
"Proof of (3)". The full node's seven proof steps were read. Its last covering
argument uses inverse-image opens and affine refinement, so these opens need
not themselves be affine before the final refinement.

Hypothesis and conclusion correspondence:

- The base scheme is `(S : Scheme.{u})`. `(T : Over S)` supplies the scheme
  `T.left` together with its structure map to `S`. Every other scheme in the
  statement has the induced structure over `S` through its displayed map to
  `T.left`; this entails no extra hypothesis or change to the objects.
- Affineness of `T` is `[IsAffine T.left]`. Mathlib's canonical-spectrum
  definition is equivalent to being isomorphic to some spectrum:
  `Scheme.isoSpec` exhibits that spectrum and `IsAffine.of_isIso` gives the
  reverse implication.
- `U` and `p : U ⟶ T.left` give the first map. `[IsProper p]` is properness,
  and `hp : Function.Surjective p` is surjectivity on underlying points.
- The finite first affine open covering is `m : ℕ`, `Uj : Fin m → U.Opens`,
  `hUaff : ∀ j, IsAffineOpen (Uj j)`, and
  `hUcover : (⨆ j, Uj j) = ⊤`. Its maps are the canonical open immersions
  `(Uj j).ι`, with domain `(Uj j).toScheme`.
- `V : Fin m → Scheme.{u}` and `q : ∀ j, V j ⟶ (Uj j).toScheme`
  are the schemes and second maps; `hqproper` and `hqsurj` impose exactly
  properness and pointwise surjectivity for each `j`.
- The second finite affine open coverings are `n : Fin m → ℕ`,
  `Vji : ∀ j, Fin (n j) → (V j).Opens`, `hVaff`, and `hVcover`.
  In particular, the second finite cardinality can vary with `j`.
- The conclusion's `∃ (Z : Scheme.{u}) (r : Z ⟶ T.left)` with
  `IsProper r ∧ Function.Surjective r` is the requested proper surjection.
- `∃ (N : ℕ) (Za : Fin N → Z.Opens)` followed by affineness and
  `(⨆ a, Za a) = ⊤` is precisely the finite affine open covering of `Z`.
- For every `a`, the existential `j : Fin m`, `i : Fin (n j)` selects the
  required pair, and `f : (Za a).toScheme ⟶ (Vji j i).toScheme` is its map.
  The equation
  `f ≫ (Vji j i).ι ≫ q j ≫ (Uj j).ι ≫ p = (Za a).ι ≫ r`
  says that it is a morphism over `T`, with precisely the requested
  factorization. Postcomposition with `T.hom` makes it a morphism over `S`.
- All scheme universes are explicitly `u`; all index sets are finite types
  `Fin m`, `Fin (n j)`, `Fin N`. No larger or independent scheme universe
  and no nonemptiness condition has been imposed.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-proper-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
  It extends separated, universally closed and locally finite type;
  universally closed implies quasi-compactness, matching finite type.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. The canonical maps used here are
  `Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict`, which has the
  corresponding `IsOpenImmersion` instance.
- `def-weil-size-convention` has its explicit metatheoretic convention
  record, with no declaration to import. It is implemented by `universe u`
  and the explicit scheme universe annotations.

Supporting Mathlib interfaces read: `IsAffine`, `IsAffineOpen`,
`Scheme.Opens.toScheme`, `Scheme.Opens.ι`, and `CategoryTheory.Over` (an
object is an arrow into its base). No notion is privately redefined.
All recorded modules of stated proof dependencies are imported without
`public`; the four statement dependencies have their Mathlib imports
publicly available. Proof dependencies with no recorded declaration were
not restated, since the theorem's signature does not need their statements:
`lem-pc-fppf-affine-open-cover`, `lem-weil-pbc-affine-scheme-qcqs`,
`lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-weil-pbc-qcqs-over-affine`, `lem-weil-pbc-scheme-coproduct-family`,
`lem-weil-pbc-scheme-image-qc-kernel`, `lem-weil-pbc-surjective-base-change`.

Edge cases checked before writing:

- Empty `T`: choose `Z = T`, the identity, `N = 0`; the covering equation
  holds and the factorization request quantifies over the empty `Fin 0`.
- `m = 0`: `hUcover` forces `U` empty; surjectivity then forces `T` empty.
- `n j = 0`: `hVcover` forces `V j` empty and surjectivity of `q j` forces
  `Uj j` empty. No index is selected there unless a resulting chart actually
  maps to it; the final construction chooses a nonempty member instead.
- Nonempty `T`: surjectivity of `r` and the covering equation rule out
  `N = 0`, without adding positivity hypotheses.
- Arbitrary base schemes, empty affine opens, and arbitrary finite sizes
  remain included. In particular no Noetherian assumption was added.

Searches actually run:

1. `msearch.py ... leanfinder` with query "Composites of finite affine open
   covers of proper surjections onto an affine scheme admit a single proper
   surjective affine open refinement": eight hits, including
   `Scheme.AffineCover`, `Scheme.instIsAffineXSchemeFiniteSubcover`, and
   `Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`. None constructs a
   refinement of two successive proper-surjective families.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsOpenImmersion`: zero hits.
3. `msearch.py ... grep` with query
   `standardPh|standard_ph|phTopology|phCover` in `AlgebraicGeometry`:
   zero Mathlib hits.
4. `msearch.py ... leansearch` with query "Two successive finite affine open
   coverings of proper surjective morphisms have a refinement by a single
   proper surjective morphism and a finite affine open covering": eight
   hits about affine properties and affine refinements; none states this
   proper-surjective composite-refinement theorem.
5. `rg` with `standardPh|standard_ph|phTopology|phCover|composite_refinement`
   in `lean/WeilConjectures` and `lean/Sheaf`: no upstream match; Sheaf hits
   concern the ph site and its affine sieve basis, whose proof calls the
   present lemma but whose theorem does not state the present conclusion.
6. `rg` for the item ID in `lean/WeilConjectures`: no hits.
7. `rg` for `standard_ph_composite_refinement|standardPhCompositeRefinement`
   in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json`: no hits before creating the module.

Proof-stage interface observation: the node's `sk-thm-chow-projective`
attachment is `ChowModification.nonempty_data` and
`ChowModification.isClosedImmersion_toProjectiveSpace`. The actual upstream
module documents and assumes a Noetherian base. Tag 0DBF and the present
node allow arbitrary affine bases. This pre-existing proof-dependency
interface issue was also noted in the stage-1 review. It does not prevent
stating this theorem and is not a reason to restrict its signature; its
proof stage will need general projective domination as in Stacks Tag 0202.
None of the four statement dependencies has an unusable interface.

Validation: `scompile.py Q38 lem-trf-standard-ph-composite-refinement`
compiled both the sandbox and library-module forms cleanly (2.1 s and 3.7 s),
with no warnings. An initial nonexistent import path for the over category
was replaced by the actual `Mathlib.AlgebraicGeometry.Restrict` module,
which also supplies the open-subscheme API used in the statement.
No statement correction, new node, or dependency module was needed.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
