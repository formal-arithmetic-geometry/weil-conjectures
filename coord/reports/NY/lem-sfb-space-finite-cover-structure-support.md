## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFiniteCoverStructureSupport` states
`AlgebraicGeometry.AlgebraicSpace.finiteCover_structure_coherent_support`.
Its only proof is `sorry`. No definitions or other declarations are added.
The source was read directly in `literature/stacks-project/spaces-cohomology.tex`,
`lemma-finite-morphism-Noetherian` (Tag 0GF7), including its proof. The node's
additional geometric conclusions are exactly the observations in that proof.
There is no statement correction or statement dispute.

Hypotheses and the fibre product:

| Node | Lean |
| --- | --- |
| A scheme S | `{S : Scheme.{u}}` |
| Algebraic spaces X and Y over S, and their morphism f | `{X Y : AlgebraicSpace S}`, `(f : Y ⟶ X)` |
| f representable and finite on every scheme test | `hf : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom` |
| f surjective on atlas point spaces | `hs : pointImage f.hom.hom = Set.univ` |
| X locally Noetherian on every etale scheme chart | `hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)` |
| A closed immersion i:Z→X | `{Z : AlgebraicSpace S}`, `(i : Z ⟶ X)`, `hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom` |
| Z'=Y×_X Z with projections i' to Y and f' to Z | `{Z' : AlgebraicSpace S}`, `(i' : Z' ⟶ Y)`, `(f' : Z' ⟶ Z)`, `hp : IsPullback i'.hom f'.hom f.hom i.hom` |

The last row is the universal-property presentation of precisely the fibre product
in the node, rather than an arbitrary commutative square. It is a pullback of fppf
sheaves, the underlying sheaves of these algebraic spaces. Quantifying over its
realizations introduces no extra mathematical assumption: the existing fibre-product
existence theorem supplies one, and any two are uniquely isomorphic preserving both
projections. The result is invariant under that isomorphism. This is the convention
already used by `etale_module_pushforward_restriction`.

Conclusion, in order of the conjunctions:

1. `IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f'.hom.hom` says f' is finite.
2. `pointImage f'.hom.hom = Set.univ` says f' is surjective on point classes.
3. `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i'.hom.hom` says i' is closed.
4. `∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T)` says Y is locally Noetherian.
5. The identical quantification for Z says Z is locally Noetherian.
6. The identical quantification for Z' says Z' is locally Noetherian.
7. `((moduleDirectImage f').obj (SheafOfModules.unit Z'.structureSheaf)).IsQuasicoherent`
   is quasi-coherence of G=f'_*O_Z'. The unit is the regular structure module on
   the existing small etale ringed site; direct image is the existing canonical
   compatible-section construction, including its structural scalar action.
8. For every `T : Z.EtaleSite`, `RingedSpace.IsCoherent` of
   `((Z.schemeRestriction T).obj G)` is exactly coherence on the etale scheme
   chart, expressed as its canonical ordinary Zariski module. Together with
   conjunction 7 this is precisely the node's definition of coherent on Z.
   In particular, no finite-presentation replacement or additional Noetherian
   hypothesis is being substituted for the stated coherence convention.
9. `moduleSupport G = Set.univ` says Supp(G)=|Z|, using the existing geometric
   nonzero-germ support and the same point classes as `pointImage`.

The node's explanatory definition of Noetherian adds no hypothesis: it does not
assume X Noetherian, and this theorem therefore has no quasi-compactness or
quasi-separatedness binder. All modules remain in section universe u on the
original small etale sites; there is no lift of coefficients or identification
of independent universes. Every variable and universe is explicitly bound, and
`autoImplicit` is disabled.

Dependency declarations used in the statement:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`. The full signatures and
  docstrings of these declarations were read.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the small-site
  slice sheafification instances, for Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`, read as finite type and finite-type
  kernels of maps from finite free modules on every open.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and the
  atlas topology on the existing `Point` type (public through ModuleSupport).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`: `IsPullback`,
  the universal-property form of the fibre product in `def-pc-fibre-product`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  specified by `ModuleDirectImageModel` and its section-limit universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport`, the
  nonzero-geometric-germ criterion, not support of global sections.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`,
  explicit restriction to open subschemes with the canonical regular-function map.

The last three owning definition nodes already exist and are landed. They are
added to `stmt_deps` under the rule permitting additional landed notions; their
Lean declarations are used unchanged. No dependency records are modified and no
new nodes are needed. Every original statement dependency remains. The
ringed-site-model dependency `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap` is
imported for the proof's existing enlarged-site interpretation; its recorded
source and chart-normalized structural-map signatures were inspected.

All recorded proof-dependency modules are imported, including the fibre-product
and point-open-calculus theorems, finite scheme pushforward coherence, the
Zariski/etale quasi-coherent comparison, pointed etale stalks, filtered-colimit
zero detection, and etale-local Noetherian descent. Mathlib proof leaves use
`Mathlib.RingTheory.Noetherian.Basic`, `Mathlib.AlgebraicGeometry.Noetherian`,
and `Mathlib.AlgebraicGeometry.Sites.EtalePoint`; the etale morphism class is
publicly available through the statement imports. The proof dependency
`lem-sfb-finite-space-morphism-topology` has no recorded module yet, so there
is no import to add for it. It remains in `proof_deps` and in the proof docstring.

Edge cases checked before writing:

- Z empty: Z' is empty by its pullback property, support and surjectivity are
  equalities of empty sets, and chartwise coherence remains meaningful.
- X empty: any Y, Z and Z' mapping into it are empty, with no excluded case.
- Empty source Y: surjectivity forces X empty; no nonemptiness binder was added.
- i the identity, including a nonreduced X: the statement specializes to
  coherence and full support of f_*O_Y, with no reducedness assumption.
- Identity f and arbitrary closed i: G is O_Z, including nilpotent closed subspaces.
- X locally Noetherian but not quasi-compact: every argument and binder is local
  on etale charts. No finite atlas or global Noetherian hypothesis is imposed.
- Every chart, not only a chosen atlas or affine chart, is quantified over in
  both local Noetherianity and coherence. No scheme-only restriction is imposed
  on the algebraic spaces themselves.

Searches made before writing:

- `msearch.py ... leanfinder` with query "For a finite surjective morphism of
  algebraic spaces to a locally Noetherian space the pushforward of the structure
  sheaf is coherent with full support": 8 hits, including scheme
  `LocallyOfFiniteType.isLocallyNoetherian`, `IsFinite`, and finite morphism
  consequences; no algebraic-space theorem matching the node.
- `msearch.py ... loogle '"AlgebraicSpace", "IsFinite"'`: 0 hits.
- `msearch.py ... grep 'finite.*coherent|support.*finite' AlgebraicGeometry`:
  one hit, a locally finite-support comment in AlgebraicCycle/Basic, unrelated.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` for finite-cover structure
  support and related names: scheme-only finite-structure theorems and existing
  algebraic-space helper constructions, no theorem with this statement.
- `rg -n 'lem-sfb-space-finite-cover-structure-support' lean/WeilConjectures`:
  no match. `rg` for `finiteCover_structure_coherent_support` over Mathlib, both
  project roots and `dag/lean_names_upstream.json`: no match before writing.
- Concept searches over algebraic-space modules found the existing
  `moduleDirectImage`, `moduleSupport`, and `schemeRestriction`. Their owning
  DAG records and full sources were read and reused; no duplicate was written.

Validation: the prescribed `scompile.py NY
lem-sfb-space-finite-cover-structure-support` compiled the delivered file in both
sandbox and final module locations on the server (1.8 seconds each), with no
errors or warnings. The prescribed `deliver2.py ... --no-push` then passed
the server preflight and per-file compile, printing OK for dry-run commit
`ed0bdb219a4`. The packet contains exactly the module, item node, and report.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
