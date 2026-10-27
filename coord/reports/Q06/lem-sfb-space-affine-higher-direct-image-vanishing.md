## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineHigherDirectImageVanishing` states
`AlgebraicGeometry.AlgebraicSpace.isZero_affine_higherDirectImage`. The proof is `sorry`.
Source read: Stacks `spaces-cohomology.tex`, Tag 073H, lines 1304–1315; the node's
four accepted proof steps and its interpretation on additive sheaves were read.

Clause correspondence:

- Base scheme: `{S : Scheme.{u}}`, using `AlgebraicGeometry.Scheme` and its morphisms
  from `Mathlib.AlgebraicGeometry.Scheme` (def-pc-scheme).
- Algebraic spaces over S: `{X Y : AlgebraicSpace S}`, using the fppf-sheaf full
  subcategory of `Sheaf.AlgebraicGeometry.AlgebraicSpace` (def-trf-algebraic-space).
- The map Y → X: `(f : Y ⟶ X)`, an actual natural transformation over S.
- Affineness and representability: `hf : IsRepresentableWith
  (fun _ _ p ↦ IsAffineHom p.left) f.hom.hom`. The property is affineness of the
  representing scheme projection on every scheme test, not affineness of an arbitrary
  nonaffine test scheme itself. This includes the identity on every space.
- The module: `(F : Y.Modules)` with `hF : F.IsQuasicoherent`. The predicate is
  Mathlib `SheafOfModules.IsQuasicoherent`, with the existing slice instances and
  `QCoh` specialization from `AlgebraicSpaceQuasiCoherentModule`.
- Underlying additive sheaf: `(SheafOfModules.toSheaf Y.structureSheaf).obj F`,
  retaining the section universe u, not lifting coefficients.
- Canonical additive direct image: `abelianDirectImage f` from the repaired enlarged
  site dependency. It extends uniquely, evaluates at Y ×_X V, then restricts to schemes.
- Right derived functor computed by injective resolutions: `I : InjectiveResolution
  ((SheafOfModules.toSheaf Y.structureSheaf).obj F)` and the homology of
  `(abelianDirectImage f).mapHomologicalComplex (ComplexShape.up ℕ)` applied to
  `I.cocomplex`. This is stated for EVERY resolution, hence is resolution-independent
  vanishing of R^q f_*(F_ab). It is not the underlying sheaf of a module right derived
  functor. The node's sites/cohomology dependency supplies the convention and existence
  of injective resolutions. No global instance or resolution-choice assumption is added.
- Every positive integer: `(q : ℕ) (hq : 0 < q)` ranges over exactly those degrees;
  negative or zero degree is not claimed. Vanishing as an abelian sheaf is `IsZero`.

Dependency sources read in full for their used interfaces: `AlgebraicSpace` (schemes,
representability, small etale topology, structure sheaf and Modules),
`AlgebraicSpaceQuasiCoherentModule` (the Mathlib local-presentation predicate and QCoh),
`SiteCoveringAxioms` (the site convention and retained Sheaf/cohomology convention),
and `SpaceCotangentRingMap` / `EnlargedEtaleRingedSite` (actual restriction and
fibre-product direct image). The statement imports those dependencies publicly; stated
proof dependencies are plain imports. The groupoid-equivalence proof node is not yet
stated and therefore has no import. The proof docstring preserves all four steps.

Edge cases checked: F = 0, empty source/target, the identity on a nonaffine scheme,
q = 0 (excluded), q = 1 (included), non-Noetherian bases, and spaces without qcqs
assumptions. The identity case confirms that affineness concerns scheme projections,
not that all scheme base changes have affine source. Site objects have universe u+1,
morphisms u, and additive coefficients u; none are forced equal. The arbitrary
resolution formulation avoids an unsupported large-site global injective instance.

Searches (all against the given live source paths):

- msearch LeanFinder: “Affine morphisms of algebraic spaces have vanishing positive
  higher direct images of quasi coherent additive sheaves”; eight affine-scheme and
  limit-section hits, no match.
- msearch Loogle: `"rightDerived", "pushforward"`; zero hits.
- msearch grep: `AlgebraicSpace|affine.*higherDirectImage|higherDirectImage.*affine`;
  zero Mathlib hits.
- msearch LeanSearch: “Higher direct images of quasi coherent sheaves along affine
  morphisms of algebraic spaces vanish”; affine scheme geometry hits, no match.
- rg of `lean/WeilConjectures` for the item id: no declaration. Concept/name searches
  of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and `dag/lean_names_upstream.json`:
  scheme vanishing theorems exist; `SpaceAffineModuleHigherImageVanishing` derives in
  modules and cites this node, so does not state this additive result. No existing
  `abelianDirectImage` or `enlargedAbelianEquivalence` for algebraic spaces was found.
- DAG grep and `tools/blueprint_refs.py search 'abelian direct image'`: no standalone
  definition node, no blueprint match. The missing helper belongs to the already
  recorded enlarged-site morphism, so no new definition node is introduced.

Every delivered file compiled separately in dependency order using scompile.py;
no errors or warnings. No statement correction or STATEMENT-DISPUTED finding.

## Dependency modules

`lem-trf-space-enlarged-etale-ringed-site-model`: its module
`Sheaf.AlgebraicGeometry.SpaceCotangentRingMap` retains all previous declarations and
adds the missing abelian specialization of its canonical small-etale direct image.
The previous interface only exposed set/ring/module equivalences, so could not type
this node's direct image on AddCommGrpCat.{u}. The new restriction-equivalence theorem
uses atlas equalizers; its data are the existing restriction functor. The equivalence
is `Functor.asEquivalence` for that functor. `abelianDirectImage` is the composite of
its inverse, the existing `enlargedDirectImage f AddCommGrpCat.{u}`, and target
restriction. Its additivity theorem follows from componentwise addition. All postponed
claims carry the owning node id and source/proof docstrings; they specialize the same
restriction equivalence and canonical morphism already stated by that node. The item's
stmt_deps adds this existing landed dependency because its declarations now occur in
the signature. No existing declaration signature or definition data changes.

## Second reading by Q06

A second source-to-signature pass was performed by this worker; no other agent was
started, as the dispatch brief prohibits that. The maintainer's independent review
remains required. The initial module-derived draft was rejected during this pass:
forgetting a module higher image would have required the very comparison this additive
node supports. It was replaced by actual abelian direct image applied to an arbitrary
abelian injective resolution. The final signature matches all clauses above and adds
no geometric, finiteness, coefficient-size, or resolution-existence restriction.
The dependency module preserves the old normalized ring construction and adds only
its abelian specialization, with no arbitrary functor or unnormalized map.
