## Worker report

Module: `Sheaf.AlgebraicGeometry.QuasicoherentAcyclicEmbedding`.
Declaration: `AlgebraicGeometry.Scheme.exists_quasicoherent_acyclic_embedding`.
This is the embedding assertion of Stacks Tag 0BDY, Lemma 30.4.3 (1), with the
node's field hypothesis retained. Its proof is `sorry`; no definitions or proofs
have been added. The docstring includes all four DAG proof steps and their inputs.
The source was read at https://stacks.math.columbia.edu/tag/0BDY because this
machine has no `literature/stacks-project/coherent.tex`.

Each hypothesis and clause is rendered as follows:

- A field k: `(k : Type u) [Field k]`.
- A scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]`.
- Quasi-compactness of X: `[CompactSpace X]`, the compactness of its underlying
  topological space, with no Hausdorff or separation condition.
- Affine diagonal: `[IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))]`.
  This is the diagonal over k, as in the node's lead review and its affine-intersection
  proof input. Over an affine base this is equivalent to all intersections of affine
  opens being affine (`isAffineHom_diagonal_iff`), and hence to the absolute affine
  diagonal condition in Tag 0BDY. No separatedness is required.
- F an O_X-module: `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`.
- F quasi-coherent: `[F.IsQuasicoherent]`. This is the local free-presentation
  definition in Mathlib, equivalent on schemes to the affine-local associated-module
  definition, explicitly identified in the dependency module Coherent.
- Existence of a quasi-coherent O_X-module F': the existential binder on exactly the
  same module-sheaf category, with `F'.IsQuasicoherent`.
- A monomorphism F to F': `∃ i : F ⟶ F', Mono i`. Mono is in module sheaves; for
  quasi-coherent objects it is the same embedding as in the quasi-coherent subcategory.
- Every higher cohomology group vanishes: `∀ p : ℕ, 1 ≤ p → IsZero
  ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F')`. This says the derived
  global-sections module is zero, equivalently its underlying abelian group is zero.
  The same F' works in all positive degrees; degree zero is unrestricted.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; commutative division ring.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, Mathlib.AlgebraicGeometry.Scheme;
  its full locally-affine locally-ringed-space structure and morphisms.
- `pqf-def-coherent`: imported `Sheaf.AlgebraicGeometry.Coherent` and read its
  `AlgebraicGeometry.RingedSpace.IsCoherent` signature and docstring. Only the
  quasi-coherent clause of this three-notion dependency is needed. Its module explicitly
  directs that clause to `SheafOfModules.IsQuasicoherent` in
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent, which is used directly;
  coherence and finite type are not hypotheses of this item. No replacement definition.
- `def-sc-ringed-space-module-cohomology`: added this already-landed definition node
  to stmt_deps, using `AlgebraicGeometry.RingedSpace.moduleCohomology` from
  `Sheaf.Topology.RingedSpaceModuleCohomology`, the right derived global-sections
  functor on module sheaves, rather than abelian-sheaf Ext cohomology.
- Auxiliary Mathlib notions: `AlgebraicGeometry.Scheme.Over` from
  Mathlib.AlgebraicGeometry.Over and `AlgebraicGeometry.IsAffineHom` from
  Mathlib.AlgebraicGeometry.Morphisms.Affine, whose signatures/docstrings were read.
  `AlgebraicGeometry.moduleRings` is the existing structure-ring-sheaf abbreviation
  in `Sheaf.Paper.DerivedHomMayerVietoris`, imported through the dependency modules.

Edge cases checked before writing: the empty scheme is allowed (there is no
Nonempty binder); the zero module embeds by its identity and is acyclic; p = 0 is
excluded precisely by `1 ≤ p`, whereas p = 1 is included. On an affine X any
quasi-coherent F is already acyclic. Non-separated schemes with affine diagonal
remain allowed. No finite-type, coherent, proper, smooth, or characteristic
restriction occurs. Both X and the field are in the common universe u, as required
by Scheme.Over; universe enlargement represents objects initially in smaller
universes, so no geometric case is excluded. Module sheaves use the existing
universe-u carrier, with no new derived-category or injective-resolution hypothesis.

Searches for an existing statement (all on 2026-10-11):

- msearch.py leanfinder, query `quasi coherent module on quasi compact scheme affine
  diagonal embeds into higher cohomology acyclic module`: eight hits, principally
  IsQuasicoherent and quasicoherentData plus affine-limit results; no embedding lemma.
- msearch.py loogle, query `SheafOfModules.IsQuasicoherent, CategoryTheory.Mono`:
  zero hits.
- msearch.py leansearch, query `quasi coherent sheaf embeds into acyclic quasi coherent
  sheaf affine diagonal`: unavailable, Internal Server Error.
- msearch.py grep, query `universal.*delta|acyclic|embedding`, Mathlib/AlgebraicGeometry:
  25 hits, concerning open embeddings and related geometric constructions; no match.
- rg in WeilConjectures and lean/Sheaf for the node id, universal delta, acyclic, and
  quasi-coherent existence: no declaration stating this embedding. The DirectImage
  source mentions Tag 0BDY in a docstring, but its declaration is a higher-direct-image
  comparison, not this assertion; its full signature was inspected.
- rg for `exists_quasicoherent_acyclic_embedding`, `universal.*delta`, and `0BDY` in
  WeilConjectures/AlgebraicGeometry, lean/Sheaf/AlgebraicGeometry, and
  dag/lean_names_upstream.json: only the unrelated DirectImage docstring.

No statement correction, new node, unusable dependency, or statement dispute.
The node's lead note says that the unused field hypothesis is deliberate and must
remain. Server compile passed with exit code 0, no errors and no warnings.

## Second reading by M1

I independently read the node copy, its source and proof, the delivered Lean module,
and all four statement-dependency nodes. I also opened the dependency modules
Coherent and RingedSpaceModuleCohomology and the Mathlib declarations below.
The local Stacks checkout is absent. I read the actual coherent.tex source at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
label lemma-affine-diagonal-universal-delta-functor, together with the beginning
of section-quasi-coherence, and checked https://stacks.math.columbia.edu/tag/0BDY.
The section imposes no standing extra hypotheses. Part (1) is precisely this
embedding assertion; part (2), universality, is not a conclusion of this node.
The source allows any quasi-compact scheme with affine diagonal. The node's
additional field/base data is intentional, explicitly required by its lead note.

The full object/hypothesis/conclusion inventory, checked against the signature:

- Field k: `(k : Type u) [Field k]`. Pass. Mathlib's Field extends CommRing
  and DivisionRing and includes nontriviality. This is def-weil-field's notion,
  not a characteristic-zero or algebraically closed specialization.
- Scheme X over that field: `(X : Scheme.{u})` and
  `[X.Over (Spec (CommRingCat.of k))]`. Pass. def-pc-scheme records Mathlib's
  Scheme, whose local_affine field supplies locally affine neighbourhoods.
  Mathlib's Scheme.Over is OverClass and supplies exactly the structure morphism
  `X ↘ Spec (CommRingCat.of k)`.
- X quasi-compact: `[CompactSpace X]`. Pass. This is compactness without a
  Hausdorff requirement, hence quasi-compactness of the underlying scheme space.
- X has affine diagonal:
  `[IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))]`. Pass.
  IsAffineHom requires affine inverse images of affine opens. I read
  Mathlib's isAffineHom_diagonal_iff: over the affine base Spec k, it says
  exactly that intersections of any two affine opens in X are affine.
  The same criterion over Spec Z gives the absolute condition in Stacks.
  Consequently the relative diagonal binder does not strengthen this node.
- F an O_X-module:
  `(F : SheafOfModules.{u} (moduleRings X.toRingedSpace))`. Pass.
  moduleRings (read in DerivedHomMayerVietoris) forgets the commutative structure
  of X's actual structure sheaf to rings; no substitute ring or category is used.
- F quasi-coherent: `[F.IsQuasicoherent]`. Pass. I read the actual Mathlib
  IsQuasicoherent definition (local cokernels of maps between free sheaves)
  and Coherent's explicit identification of this clause of pqf-def-coherent.
  On schemes it is the affine-local associated-module notion of the node.
  The dependency's IsCoherent predicate is not substituted for quasi-coherence.
- There is an O_X-module F' in the same category: the existential
  `∃ F' : SheafOfModules.{u} (moduleRings X.toRingedSpace)`. Pass.
- F' is quasi-coherent: `F'.IsQuasicoherent`. Pass; neither coherence nor
  finite generation is asserted or assumed.
- There is a monomorphism F to F': `∃ i : F ⟶ F', Mono i`. Pass.
  Morphisms are O_X-linear sheaf maps. Monomorphisms in module sheaves are
  sheaf embeddings, so this renders an embedding between the two quasi-coherent
  objects without needing a second definition of the quasi-coherent category.
- All higher cohomology of the same F' vanishes:
  `∀ p : ℕ, 1 ≤ p → IsZero
  ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F')`. Pass.
  I read moduleCohomology and globalSectionsFunctor: these are right derived
  global sections in O_X-modules, exactly the recorded dependency's cohomology.
  IsZero of the resulting global-sections module means that its abelian group
  vanishes. Both F' and i precede p, so no degree-dependent embedding is allowed.

Edge cases: the empty scheme and zero module are admitted; no Nonempty binder
or nonzero-sheaf condition appears. An empty finite affine cover is permissible
in the documented construction. No index set occurs in the theorem itself.
Degree zero is unrestricted, and degree one and every higher natural degree are
included. Fields of every characteristic are allowed. Non-separated schemes
with affine diagonal remain admitted. No Noetherian, finite-type, proper,
smooth, finiteness-of-cohomology or derived-category hypothesis occurs.
The single declared universe u is arbitrary and binds k, X and the module
carriers; enlargement to a common universe represents differing initial sizes.
No independent smaller testing universe or hidden free variable occurs.

Independent duplicate searches (2026-10-11):

- msearch leanfinder: `effaceable cohomology quasicoherent sheaves monomorphism
  higher cohomology zero`; eight results, including sheaf cohomology definitions,
  Mayer-Vietoris monomorphisms and unrelated complex/group-cohomology lemmas;
  none states the embedding assertion.
- msearch loogle: `SheafOfModules, IsZero`; unavailable identifier IsZero,
  so this is not counted as a successful absence check. A second query,
  `SheafOfModules.IsQuasicoherent`, returned 12 hits: the predicate, constructors,
  local-presentation/local-freeness facts, restrictions and pushforwards, but no
  acyclic embedding theorem.
- msearch leansearch: `effaceability of positive cohomology for quasi coherent
  modules on schemes`; unavailable (Internal Server Error), recorded as such.
- Direct rg of Mathlib's AlgebraicGeometry and ModuleCat/Sheaf, the source's
  AlgebraicGeometry, and lean/Sheaf/AlgebraicGeometry for
  `quasicoherent.*(embedding|acyclic)|(?:embedding|acyclic).*quasicoherent|effaceab`
  returned no match. Broader rg over WeilConjectures and lean/Sheaf for acyclic,
  effaceability, universal delta, 0BDY and the proposed declaration found many
  unrelated homological/etale results but no matching statement.
- Focused rg for 0BDY, universal delta and the proposed declaration, also in
  dag/lean_names_upstream.json, found only the source DirectImage docstring.
  I opened its actual declaration exists_addEquiv_sections_higherDirectImage_H:
  it compares sections of higher direct images with cohomology, assumes separated
  quasi-compact f over an affine base, and asserts no acyclic embedding.

No mathematical mismatch was found. No Lean or node changes were needed;
this independent second-reading record is the only substantive addition.
There are no new nodes or dependency modules in this delivery and no statement
correction to audit. The docstring reproduces all four proof steps and cites
all non-elementary proof inputs. The only theorem proof is sorry; there are no
new definitions, hollow data or proved auxiliary facts. Imports serve the
module-sheaf/quasi-coherent notions, cohomology, affine diagonal and base data.
The recorded lean.statement agrees verbatim with the file's signature.
Remote scompile completed successfully (exit 0, 2.3 seconds), without warnings.
