## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceIntegralFactorizationEtaleBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.integralFactorization_etale_baseChange`, with its sole
proof `sorry`. No definitions, axioms, helper theorems, or dependency replacements are
introduced. The natural-language statement, proof, and proof dependencies are unchanged.

Clause-by-clause rendering:

- `S : Scheme.{u}` and all six spaces `Y X N W YW NW : AlgebraicSpace S` give schemes
  and algebraic spaces in the recorded size convention. All variables and the universe
  are explicitly bound; `autoImplicit` is false.
- `f : Y ⟶ X`, `i : Y ⟶ N`, `n : N ⟶ X`, and `_hfactor : i ≫ n = f`
  give exactly the stipulated factorization (Lean composition reads left to right).
- `_hqc : IsQuasiCompactPresheafMap f.hom.hom` is the existing affine-test predicate.
  Its existing definition owner is `def-sfb-space-quasi-compact-presheaf-map`.
  It is equivalent to the node's all-quasi-compact-scheme-test condition: cover a
  quasi-compact test scheme by finitely many affine opens; take the supplied
  quasi-compact scheme atlases on these opens and assemble them by finite disjoint
  union. Conversely, every affine test scheme is quasi-compact. This equivalence
  explains the interface; no affine-tests theorem is used to state this theorem.
- `_hsep : IsSeparatedPresheafMap f.hom.hom` is representability of the relative diagonal
  by closed immersions. Its existing definition owner
  `def-sfb-presheaf-map-separated-diagonal` is added to statement dependencies.
  No separatedness of the base is assumed.
- `_hn : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) n.hom.hom`
  expresses integrality by integral scheme projections of every scheme test, including
  representability. This uses the existing general scheme-test interface, not a new
  integral-morphism predicate.
- `_huniversal` quantifies over every algebraic space T, integral q : T → X, and
  a : Y → T with `a ≫ q = f`. Its `∃! h : N ⟶ T, i ≫ h = a ∧ h ≫ q = n`
  asserts existence and uniqueness with both required equations.
- `w : W ⟶ X` and `_hw : IsEtale w.hom.hom` are precisely representable étaleness on
  all scheme tests; surjectivity is not assumed.
- `pY`, `fW`, `_hY : IsPullback pY.hom fW.hom f.hom w.hom` and `pN`, `nW`,
  `_hN : IsPullback pN.hom nW.hom n.hom w.hom` specify Y ×_X W and N ×_X W as
  cartesian squares of fppf sheaves. The fibre-product dependency ensures these are
  algebraic spaces. This uses arbitrary representing squares, as in the existing
  étale module restriction interface, and excludes no choice of fibre product.
- `iW`, `_hiY : iW ≫ pN = pY ≫ i`, and `_hiW : iW ≫ nW = fW` specify the induced
  base-change arrow. The pullback universal property determines it uniquely, so these
  are the defining projection equations, not an assumption about an arbitrary arrow.
- The first conclusion is `IsRepresentableWith ... nW.hom.hom`: n_W is integral.
- The second conclusion quantifies over every TW, integral qW : TW → W, and aW
  compatible with fW, then asserts `∃! hW : NW ⟶ TW` with `iW ≫ hW = aW` and
  `hW ≫ qW = nW`. It includes both required equations and uniqueness of the map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, their scheme-test signatures, and the full-subcategory morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with sheaf-pullback closure and universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  `pointImage`, `PointRepresentative.map`; the topology is retained through import,
  although the node's atlas definition of quasi-compactness needs no explicit point binder.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.Integral`: `IsFinite`, `IsIntegralHom`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`. In particular the integral
  property retains affineness and the integral affine-open ring maps.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`,
  `diagonalPresheafMap`, `IsSeparatedPresheafMap`. These plain definitions are
  owned by the two existing:true definition nodes named above. Neither the étale-local
  theorem nor the affine-tests theorem is used as a statement input. The unused
  `SpaceQuasiCompactAffineTests` import is removed.
- Size convention: explicit universe u, inherited site objects in u+1 and sections in u;
  the convention node has no declaration and requires no separate import.

Every already stated proof dependency is imported privately: the modules
`AlgebraicSpaceQuasiCoherentPushforward` (the direct-image quasi-coherence theorem),
`AlgebraicSpaceQuasiCoherentIntegralClosure` (`existsUnique_quasiCoherent_integralClosure`),
`AlgebraicSpaceRelativeSpecCorrespondence` (`space_relative_spec_correspondence`),
`AlgebraicSpaceQuasiCoherentModule` (`QCoh`, using Mathlib's IsQuasicoherent),
`AlgebraicSpaceModulePullbackQuasiCoherent` (`isQuasicoherent_moduleTensorPullback`),
`AlgebraicSpaceModuleOperations` (the specified chart-limit direct image, its adjunction,
unit and tensor pullback), and `AlgebraicSpaceEtaleModulePushforwardRestriction`
(`etale_module_pushforward_restriction`). Their source signatures and docstrings were
read; the statement docstring reproduces the six-step proof using those same objects.

Source checked directly: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-properties-normalization` (Tag 0ABP), part (1), and
`lemma-characterize-normalization` (Tag 0823). The source covers qcqs morphisms; the
node deliberately states its separated case and is left unchanged. Initiality identifies
the arbitrary given factorization with relative normalization, so the source applies.

Edge cases checked mathematically before writing:

- Empty Y is allowed; the zero integral algebra and empty relative spectrum present no
  exception. Neither nonemptiness nor dominance is imposed.
- Empty W and empty scheme tests are allowed; the empty atlas is quasi-compact. The
  finite affine-cover assembly explicitly allows the empty finite cover.
- Identity w and arbitrary nonsurjective étale w are allowed. In the identity case the
  conclusion is the assumed initial property; for an open restriction the same source
  normalization argument applies, with no covering assumption on w.
- No normality, reducedness, finite type, noetherian, characteristic, or base-separation
  hypothesis was added. Integral q and qW may be non-finite.
- The cartesian hypotheses and projection identities express only the objects and
  induced maps introduced by the node. They are invariant under their unique
  fibre-product isomorphisms and do not substitute any arbitrary map for the induced map.

Searches for an existing exact statement:

- `msearch.py leanfinder`, query "Etale base change preserves universal integral
  factorization of algebraic spaces": 8 hits, all scheme/ring étale or integral permanence
  declarations, no algebraic-space universal-factorization assertion.
- `msearch.py loogle`, query "AlgebraicGeometry.IsIntegralHom, CategoryTheory.IsPullback":
  0 hits.
- `msearch.py leansearch`, query "universal integral factorization of algebraic spaces
  commutes with etale base change": 8 scheme/ring permanence hits, no exact match.
- `msearch.py grep`, query `normalization.*[Bb]ase[Cc]hange|integral.*factorization`,
  Mathlib subdirectory AlgebraicGeometry: 0 hits.
- `rg` on both the upstream WeilConjectures and project Sheaf trees for the item id,
  normalization/base-change terms, integral-factorization terms, and the exact planned
  declaration name found no duplicate. The existing `NormalizationCover` module concerns
  schemes and does not state the algebraic-space assertion. The relative-Spec module
  already uses the same `IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left)` formula.
- DAG/blueprint search for integral algebraic-space notions, and direct reads of the
  recorded dependencies, confirm the general representability interface suffices;
  no new notion or node is necessary.

No STATEMENT-DISPUTED issue, statement correction, or dependency interface fault was found.
The requested CompactObject example is now a withdrawn empty module; its node points to
its existing upstream declaration. This does not affect the present statement.

Validation of the original statement: scompile.py compiled the module in both sandbox
and library contexts without errors or warnings. The repaired module is recompiled,
then checked by the required delivery dry run before the final push.


## Repair of returned delivery f45fb6357f61

H2 is repaired. Compared with the retained returned packet, the item replaces
`lem-trf-space-qc-separated-etale-local` and `lem-sfb-space-quasicompact-affine-tests`
in stmt_deps by `def-sfb-space-quasi-compact-presheaf-map` (Q97) and
`def-sfb-presheaf-map-separated-diagonal` (Q32). Both current-main definition records
were read along with the exact source declarations in SpaceQCSeparatedEtaleLocal.
The current-main item has neither returned theorem dependency, so this packet adds
only the two definition owners to its original dependency list.

The unused public import of SpaceQuasiCompactAffineTests is dropped. The existing
public import of SpaceQCSeparatedEtaleLocal remains because it supplies the two plain
definitions. The module docstring now explains the equivalence between the affine
atlas predicate and all quasi-compact scheme tests, including the empty finite cover.
The report's former references to theorem nodes as definition owners are corrected.

The Lean theorem signature remains byte-identical to the returned packet, and matches
lean.statement verbatim. The natural-language statement, proof, proof_deps, source,
and every other non-authorized node field remain identical to current main. This is
a dependency-ownership and import repair, not a statement correction. No dependency
node or existing library module is edited.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
