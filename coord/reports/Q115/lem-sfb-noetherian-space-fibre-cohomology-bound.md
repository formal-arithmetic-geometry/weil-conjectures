## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianSpaceFibreCohomologyBound` states
`AlgebraicGeometry.AlgebraicSpace.higherDirectImage_isZero_above_geometricFibreDimension`.
Its only theorem has proof `sorry`; it introduces no definitions or auxiliary obligations.
The original statement and accepted proof are unchanged. I read the source in
`literature/stacks-project/spaces-cohomology.tex`, lines 4408–4452, Tag 0A4T,
`lemma-higher-direct-images-zero-above-dimension-fibre`. The source's stalkwise result is
applied at every geometric point, exactly as the node requests. Its natural-language
seven-step proof, including residue-field extension, empty fibres, finite-generation
and Nakayama details, is in the theorem docstring.

Hypothesis and conclusion correspondence:

- The locally Noetherian scheme Y is `(Y : Scheme.{u}) [IsLocallyNoetherian Y]`.
- The space over Y is `(Z : AlgebraicSpace Y)`. The target is the actual representable
  space `schemeSpace (Over.mk (𝟙 Y))`; the named morphism is `p` to that target. Choosing
  Y itself as the common base loses no algebraic space over Y and does not assume
  representability of p or of Z by a scheme.
- Properness is `hp : MapIsProper p`, the already published conjunction of separatedness,
  finite type and universal closedness, not a new or chartwise substitute for properness.
- The nonnegative integer bound is `d : ℕ`. This parametrizes precisely the integers
  d ≥ 0. `q : ℤ` and `hq : (d : ℤ) < q` retain the node's integer cohomological degrees.
- `hdim` quantifies over every field Ω with `[IsAlgClosed Ω]` and every scheme map
  `y : Spec (CommRingCat.of Ω) ⟶ Y`. Its presheaf pullback is literally
  `Limits.pullback p.hom.hom (yoneda.map (Over.homMk y))`. This is the geometric fibre,
  not the set of Ω-valued points of the fibre. Every natural map `a` from the representable
  of `U : Over Y` to that pullback is considered. `IsEtale a` and `IsAffine U.left`
  select exactly its affine étale scheme charts. The inequality is
  `topologicalKrullDim U.left ≤ (d : WithBot ℕ∞)`. Bounding every chart is precisely
  bounding their supremum; it does not select a single atlas or weaken the bound.
- The coefficient is `(F : Z.Modules) [F.IsQuasicoherent]`, using the original
  small étale structure sheaf and Mathlib's local-presentation quasi-coherence predicate.
- The remainder of coherence is `hcoh`: there exists a family `T : ι → Z.EtaleSite`
  with `IsJointlySurjective (fun k ↦ (T k).obj.hom)`, and each chart is affine, its ring
  `Γ(Z.etaleForget.obj (T k), ⊤)` is Noetherian, and its section module
  `F.val.obj (op (T k))` is `Module.Finite` over that very ring. Each affine chart is
  canonically Spec of its global-functions ring. By the published
  `quasiCoherent_affine_chart_calculus`, restriction of a quasi-coherent F is canonically
  the associated sheaf of these sections; on affine étale subcharts its values are the
  usual tensor products. Conversely an associated finite module has finite sections on
  the chart. Thus this is exactly the node's associated-finitely-generated-module clause,
  not merely finiteness of an arbitrary sheaf's global sections. The existential family
  is only one cover, not a stronger requirement on every chart. Its index universe w is
  independent; it is neither finite nor required to be inhabited.
- The conclusion is `IsZero` of degree-q homology of `derivedDirectImage p` applied to
  the degree-zero complex of `Z.smallModuleRestriction.obj F`. The published
  `smallModuleEquivalence` is an equivalence of the original module category with its
  small affine basis model. `smallModuleDirectImage` is explicitly the conjugate of
  `moduleDirectImage`, and `derivedDirectImage` is its canonical right derived functor.
  For a module in degree zero, this homology is R^q p_* F. Equivalences preserve
  injectives, resolutions, homology and zero objects. Thus the conclusion is vanishing
  of the module higher direct image, not just of its global sections or its stalks.
- The two `HasDerivedCategory.{v}` binders specify existence/size of the standard derived
  categories used by the published API; neither specifies a new Abelian instance nor
  restricts p or F. No flatness, quasi-projectivity, connectedness, nonemptiness, finite
  cover or global-Noetherian hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`;
  full declarations and docstrings at lines 33–76.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  lines 56–60, with its every-affine-open interpretation.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `EtaleSite`, `structurePresheaf`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality`:
  `AlgebraicGeometry.AlgebraicSpace.flat_proper_fp_locality`; its public
  `AlgebraicSpaceMorphismProperties` gives `MapIsProper` with the exact conventions.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, lines 35–40,
  supremum of chains of nonempty irreducible closed subsets, with bottom for empty.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  slice-sheafification instances specialize Mathlib's
  `SheafOfModules.IsQuasicoherent` (Quasicoherent.lean, lines 249–261). The theorem
  uses that same predicate on F, rather than requiring a different bundled coefficient.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImageModel`,
  `moduleDirectImage`, their normalized chart-limit universal property, and
  `moduleTensorPullback`; the derived functor below is explicitly built from this image.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, lines 192–200.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, lines 115–119.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the actual Yoneda
  representable sheaf; the owner is `def-trf-scheme-algebraic-space`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallModuleRestriction`, `smallModuleEquivalence`, with coefficient carriers in u.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `smallModuleDirectImage`,
  `smallModuleDirectImage_additive`, `derivedDirectImage`, including their signatures and
  source/proof docstrings. No coefficient or scheme universe is enlarged or identified.

The last three already-landed definition owners were added to `stmt_deps`, as permitted
by brief-stage2 section 5. Their existing records and sources were read; no dependency
records are changed. The original statement dependency imports are public directly or
through their published public imports. Plain proof imports include the recorded affine
chart calculus, module-pullback preservation and upstream geometric-stalk conservativity.
The remaining proof inputs have no Lean records and need no statement in this delivery:
they are proof dependencies, not missing notions needed to type the theorem.

Edge cases checked: d = 0 still asserts every positive degree; q need not be supplied as
nonnegative because q > d ≥ 0 already implies it. Empty geometric fibres have only empty
étale charts and their dimension is bottom, so they satisfy `hdim`. The empty total space
admits the empty jointly surjective chart family; no Nonempty index assumption occurs.
The zero module is finitely generated. The zero ring is allowed as the section ring of
an empty affine chart. The empty target is allowed. Fields and schemes use their original
common universe u, which contains algebraic closures of residue fields; the chart and
point categories keep the larger object universe already present in the dependencies.
There is no independent smaller universe for geometric test fields. The derived-category
universe v and cover-index universe w do not impose equations on site universes.

Searches actually run with msearch.py for Q115 and this item:

- LeanFinder: “For a proper morphism of algebraic spaces to a locally Noetherian scheme
  with geometric fibres of dimension at most d, coherent higher direct images vanish
  above d”. Eight hits, all scheme properness/finite-type/limit lemmas; no exact result.
- Loogle: `topologicalKrullDim, Functor.rightDerived, IsNoetherianRing` returned zero
  hits with diagnostic `unknown identifier 'Functor.rightDerived'`. This query did not
  establish absence; I separately read Mathlib's fully qualified right-derived API.
- Mathlib grep: `higherDirectImage|fibre.*cohomology|cohomology.*dimension` under
  AlgebraicGeometry: zero hits.
- LeanSearch: “Higher direct images of a coherent module under a proper algebraic space
  morphism vanish above the fibre dimension”. Eight hits: scheme pushforward and
  properness declarations, no exact statement.
- Local rg of `lean/WeilConjectures` by this node ID found no statement. Searches for
  algebraic spaces found no competing upstream framework. rg of `lean/Sheaf` located
  the existing dimension, properness, affine-chart and derived-module interfaces; their
  sources were opened. A search for the fibre/cohomology bound found no duplicate.

No new definition nodes, dependency repairs, statement correction or disputed statement.

## Second reading by Q115

This is the author's second reading; independent review is performed by the maintainer.
I reopened the node, Tag 0A4T and the delivered Lean signature. Y is a scheme, not merely
an unspecified base; p has the node's properness predicate. The fibre in `hdim` is a
sheaf/presheaf fibre product with Spec Ω, not a type of rational points. Every affine
étale chart is tested, and the empty case remains bottom. In `hcoh` both Noetherianity and
module finiteness refer to the same chart's actual functions; the `F.IsQuasicoherent`
binder is essential for the associated-sheaf interpretation and is present. The family
is existential and jointly surjective; no all-chart finiteness assumption was added.
The homology object is in the target's module category via its equivalent small model,
using the existing canonical derived direct image on a degree-zero module. It is not
ordinary étale cohomology of F and not derivation in QCoh. The integer inequality is
strict. No flatness binder was introduced. No mismatch or source error was found.
I added the existing definition owners to stmt_deps and added the available proof
imports; I did not change the mathematical node statement or its accepted proof.
