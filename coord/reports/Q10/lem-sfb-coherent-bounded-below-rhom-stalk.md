## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentBoundedBelowRHomStalk` states the derived
comparison itself, with an explicit canonical map and general naturality. All three
new theorem proofs are `sorry`; definitions contain real data. There is no correction
of the informal statement, no dependency replacement, and no new independent notion.
The helpers belong to the canonical comparison already mentioned in this item.

Clause-by-clause correspondence:

- The scheme is `X : Scheme.{u}`. Noetherian means exactly `[CompactSpace X]` and
  `[IsLocallyNoetherian X]`, as the two specified dependency records require. The
  theorem does not impose affineness, separatedness, reducedness, a field, or a
  dimension bound.
- The sheaf is `F : SheafOfModules.{u} (moduleRings X.toRingedSpace)`; coherence is
  `_hF : RingedSpace.IsCoherent X.toRingedSpace F`. The recorded coherence module
  publicly exposes this exact finite-type-and-finite-type-kernels predicate; its
  weaker `IsQuasiCoherentFiniteType` conjunction is not substituted for coherence.
- `E : schemeDerivedCategory X` is unrestricted except for `_hE : ∃ a : ℤ, E.IsGE a`.
  Mathlib's `DerivedCategory.isGE_iff` identifies this with vanishing of every
  cohomology sheaf below a. No quasi-coherence of E, termwise bound on the given
  representative, or upper bound is required.
- `x : X` is any point and `X.presheaf.stalk x` is exactly its local ring A.
- `DerivedCategory.singleFunctor ... 0` embeds F as F[0]. The exact functor
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapDerivedCategory` takes
  stalks termwise; its `mapDerivedCategoryFactors` supplies the canonical
  identification on localization representatives. Thus its image of F[0] is
  precisely F_x[0], expressed functorially rather than by a second definition.
- The source of `derivedInternalHomStalkComparison` is the stalk of
  `derivedInternalHom (Opens.grothendieckTopology X) X.sheaf` evaluated at F[0],E.
  Its target is `ordinaryModuleDerivedInternalHom (X.presheaf.stalk x)` evaluated
  on the two derived stalks. This is the recorded ordinary-module presentation
  of the one-object ringed-site RHom. It is an object of D(A), not a cohomology
  group or a complex over an unrelated ring.
- The main theorem's `IsIso` asserts that this specific comparison is invertible
  in D(A). The comparison is defined by currying the stalk of the canonical
  evaluation `schemeDerivedTensorHomEquiv ... (𝟙 _)`, preceded by the tensor
  comparison. The latter is selected from `exists_rhomStalkTensorComparison`,
  whose `∃!` pins its actual data by a naturality equation and a normalization
  on K-flat representatives, with the actual localization tensor map and
  pure-tensor germ comparison. This is not a choice of an arbitrary isomorphism.
- `derivedInternalHomStalkComparison_naturality` writes the commuting square
  for every `f : K' ⟶ K`, `g : L ⟶ L'`, with contravariance made explicit by
  `f.op`. Set K=K'=F[0], take f to be the degree-zero image of any endomorphism
  of F, and take g to be the identity of E to recover the final precomposition
  clause verbatim. General f,g also give naturality between coherent sheaves
  and bounded-below targets; the naturality of the map requires no such bounds.

The canonical tensor helpers do not assert a second tensor construction. The
sheaf tensor is the existing `SheafOfModules.monoidalCategory`; the derived tensor
is the shared `schemeDerivedTensorMonoidal`. The sheaf comparison comes from
`stalkTensorIso`, which includes its pure-tensor germ equation. Degree comparisons
are fixed by their summand-injection equations, and differential compatibility
assembles these into a complex isomorphism. The `∃!` derived normalization makes
choice from the single postponed helper theorem legitimate: the theorem determines
the chosen data up to equality, not merely existence. Its proof docstring explains
localization and uniqueness. Every helper is recorded in `lean.declarations`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly importing
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`; for scheme module sheaves the shared
  specialization is `RingedSpace.moduleStalkFunctor` in
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`, as the record instructs.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.singleFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `ordinaryModuleDerivedInternalHom`, and its public upstream `derivedInternalHom`.
- `WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport`: the existing
  `SingleComplexBaseChange.comparisonStalkAdditive`, `comparisonStalkHomology`,
  `comparisonStalkLimits`, `comparisonStalkColimits` instances. Its
  `comparisonDerivedStalk` itself requires localizations for every scheme; this
  delivery uses the underlying `mapDerivedCategory` with only X's localization,
  avoiding that unnecessary global assumption. No exactness interface is copied.
- `WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom`:
  `schemeDerivedTensorHomEquiv`, with its canonical representative equation.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `schemeDerivedTensorMonoidal`; the public comparison model also provides
  `pullbackTensorModelMap` and `pullbackTensorTotal`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor`: `stalkTensorIso`.
- `WeilConjectures.Algebra.Homology.StalkTensorComplexDegrees`:
  `CochainComplex.exists_stalk_tensor_degree_iso`.
- `WeilConjectures.Algebra.Homology.StalkTensorComplexDifferential`:
  `CochainComplex.stalk_tensor_degree_differential`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided`:
  `DerivedCategory.braidedCategory'`, the existing Koszul braiding, used inside
  the comparison definition to order the evaluation tensor factors.

The new statement dependencies name the already landed nodes owning the canonical
maps and exact-stalk instances used in the signatures and helper data. They add no
new mathematical hypothesis. All recorded proof dependencies are imported: the
truncation module, affine free resolution, restriction of RHom, finite-free model,
stalk exactness, Hom complex, and derived internal Hom. Proof-only imports are plain.

Source read: `literature/stacks-project/cohomology.tex`,
`lemma-stalk-internal-hom` (0GM8), and `lemma-pullback-internal-hom`; the former
applies the latter to the flat singleton ringed-space inclusion. Also read
`literature/stacks-project/perfect.tex`, `lemma-identify-pseudo-coherent-noetherian`
(08E8): coherent degree-zero objects are pseudo-coherent. The theorem's proof
docstring preserves all five steps of the accepted DAG proof, including the good
truncation needed because E is cohomologically, rather than termwise, bounded below.

Edge cases: zero F and zero E are allowed; any integer lower bound and arbitrary
negative degrees are allowed. For the empty scheme there is no x, so the
point-indexed statement has no instance to check. The first argument need not be
locally free, and E need not have coherent cohomology. The finite interval in the
proof may be empty, giving the zero Hom term. The independent localization
universe w is retained on D(O_X), while D(A) uses its already recorded standard
ordinary-module localization. No equality of universes or localization for every
scheme is assumed. All variables and universes are explicitly bound, and module
mode is used throughout.

Searches actually run through `msearch.py Q10 lem-sfb-coherent-bounded-below-rhom-stalk`:

- LeanFinder: "The stalk functor commutes with derived internal Hom from a coherent
  sheaf into a bounded below complex on a Noetherian scheme". Eight results,
  ordinary smooth-sheaf germ/evaluation lemmas, scheme restriction-stalk natural
  isomorphisms, and tilde stalk maps; none is the derived theorem.
- Loogle: `"stalk", "Hom"`. Twelve ring-homomorphism
  `RingHom.SurjectiveOnStalks` results; no derived-Hom comparison.
- Mathlib grep: `derived.*[Hh]om.*stalk|stalk.*derived.*[Hh]om|stalk.*[Pp]seudo[Cc]oherent`.
  Zero hits.
- LeanSearch: "Derived internal Hom stalk comparison for coherent modules with
  bounded below target and naturality". Eight results on free sheaf Hom,
  restriction-stalk natural isomorphisms, local ring stalk maps, and tilde stalks;
  none states the derived comparison.
- `rg` of the same concepts and canonical-comparison names in `lean/WeilConjectures`
  and `lean/Sheaf`, and item-id search in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json`: no exact theorem or canonical map found.
  `Sheaf.Paper.DerivedInternalHomStalkLocalization` was opened and read: its
  second argument is a degree-zero sheaf G, and it concludes only a separate
  cohomology-module equivalence for each i. It is strictly insufficient here.
  The ordinary evaluation map and existing tensor/stalk comparisons were read
  and reused where applicable. No duplicate declaration was written.

Validation: single-file compilation through the prescribed `scompile.py`; no
local build or direct mutation of the shared checkout. The initial probes found
the explicit root namespace `Opens.grothendieckTopology` and the named derived
braiding, which corrected two elaboration errors. Final compilation and delivery
preflight are recorded below.

## Second reading by Q10

This is the dispatcher's single-worker rereading, not a claim of an independent
agent review; the maintainer supplies the independent review after delivery.
I reread the node, source, and final file together. The main binders have exactly
the node's compactness, local Noetherianity, coherence, bounded-below cohomology,
and arbitrary point. The result is `IsIso` on a concrete arrow in D(A). The
source is the exact stalk of sheaf RHom, and the target is ordinary RHom of the
exact stalks, with F embedded in degree zero. The target is not restricted to
quasi-coherent complexes or replaced by degreewise Ext groups. The separate
square has the correct contravariant orientation and specializes to every
endomorphism of F. I checked the representative normalization: it composes
stalked localization tensor, factorization, and the germ tensor-complex
comparison, with the ordinary Q tensor map on the other side. This pins the
canonical map and excludes an arbitrary natural isomorphism or a sign twist.
No statement mismatch was found. Compiler probes were removed; root Opens
namespace and explicit canonical braiding are the only elaboration corrections.

Dry-run repair: the node signature initially included the `:=` delimiter; the
preflight expects the signature before that delimiter, so the record was corrected.
The Lean statement itself did not change. The preflight also notes the already
landed theorem nodes used to construct the canonical comparison. Those dependencies
are explicit because their exact shared instances and normalized comparisons are
used; no private copy or new independent definition is introduced.
