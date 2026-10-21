## Worker report

Item: `lem-sfb-locally-closed-generator-tensor-intersection`, O2 stage 2.
Module: `Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection`.
Main declaration: `AlgebraicGeometry.ProEtale.CondensedRing.locallyClosedGeneratorTensorIntersection`.
Only the theorem has a postponed proof, written `by sorry`. All six helper declarations
have real data. The original node fields, including its statement and dependencies, are unchanged
except for the new `lean` record. There is no statement correction or disputed assertion.

Source read: the current blueprint `main-20261015`,
`sec-six-functors-basics/sk-thm-sf-pf-field/sk-thm-sf-pf-field-tensor.proof.md`, Proof (1),
which applies two locally closed projection formulas and base change to the intersection
of the supports. The complete seven-step DAG proof and every step's dependency list are
in the theorem docstring. The current node deliberately has no admissibility or base-field
assumption; the older `locallyClosedImmersionTensorProjection` is not a match because it
assumes separated finite-type schemes over a field.

Hypotheses and ambient categories:

| Node clause | Lean rendering |
| --- | --- |
| X is a scheme, and S,T are schemes over it | `{X S T : Scheme.{u}}`, `(a : S ⟶ X)`, `(b : T ⟶ X)` |
| X is Noetherian: locally Noetherian and quasi-compact | `[IsLocallyNoetherian X] [CompactSpace X]` |
| Any commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ] [IsCommMonObj Λ]`; this is the ring-object presentation reexported by the recorded condensed-ring module, not just coefficients arising from topological rings |
| Coefficients R_Y=p_Y^*Λ | `condensedRingObj Λ Y` in every module type and all operations |
| Small pro-etale site | `Scheme.ProEt.topology Y`; no larger site or ordinary Z-module replacement |
| Ordinary unbounded derived categories and relative derived tensor | `DerivedCategory`, `derivedTensor Λ X`; the latter is the recorded relative K-flat tensor, not tensor over Z |
| Constructible locally closed immersions | `[IsImmersion a] [IsImmersion b]`; in a Noetherian space every locally closed subset is constructible, so a further constructibility binder would be redundant |
| L,M are lisse modules, ranks may vary | Objects of `ObjectProperty.FullSubcategory (IsLisseCoefficientModule Λ (X := S))` and the corresponding category for T. The property is the recorded definition, not a new predicate |
| W is the actual scheme fibre product | `pullback a b`; projections `pullback.fst a b`, `pullback.snd a b`, and `c = pullback.fst a b ≫ a`. The second equality `c = pullback.snd a b ≫ b` is the pullback condition, not an additional hypothesis |
| Exact inverse image with pulled-back coefficients | Existing `CondensedRing.upperStar Λ f`, with its canonical `condensedPullbackHom` coefficient transport. This is the module-object realization of the recorded small-site inverse image |
| Locally closed extension by closed direct image and open extension by zero | `generatorExtension`: for `.inl A` it is `lowerStar Λ A.i ⋙ openImmersionLowerShriek Λ A.p`; for `.inr A` it is `openImmersionLowerShriek Λ A.i ⋙ lowerStar Λ A.p` |

Conclusions, in order:

1. `generatorTensorSource Λ A B` is the bifunctor `(a_!L)[0] ⊗ᴸ (b_!M)[0]` on the full lisse
   subcategories. `generatorTensorTarget Λ a b C` applies ordinary relative tensor to the
   two projection pullbacks on W, then the actual module extension from W and
   `DerivedCategory.singleFunctor _ 0`. Thus its value is `c_!(P[0])`: exact extension of a
   complex concentrated in degree zero is precisely degree-zero realization of the module
   extension. The target does not use a derived tensor internally or replace the given W
   by a reduced intersection.
2. `∃ e : ∀ A B C, generatorTensorSource Λ A B ≅ generatorTensorTarget Λ a b C` supplies
   natural isomorphisms of bifunctors, not merely unrelated objectwise isomorphisms. The
   full lisse subcategories have all module morphisms between the allowed objects, so this
   asserts both naturality variables stated in the node.
3. Both orders of open/closed factorization are quantified: `GeneratorFactorization a`
   is the sum of the two existing Mathlib `MapFactorizationData` specializations. This is
   only a transparent parameter abbreviation. It introduces no replacement notion of an
   immersion or of extension by zero.
4. `generatorRestriction Λ A` is a fully defined natural transformation `a^* a_! ⟶ id`.
   In the closed-then-open case it composes inverse-image composition, the inverse open
   adjunction unit, and the closed adjunction counit. In the other order it applies the
   closed counit first, then the inverse open unit. Its type and data use the actual
   canonical adjunctions. No normalization map is an arbitrary parameter.
5. The universal equation after the existential `e` takes comparisons α,β,γ between any
   two choices of the three extensions. Its three premises say precisely that the
   comparisons restrict to the identity: whisker the comparison by inverse image and
   compose the new restriction map to recover the old restriction map. The equation
   tensors the α and β comparisons on the source and the γ comparison on the target.
   This is the stated independence up to normalized extension comparisons, including
   comparisons between the two different orders of factorization. The existing extension
   coherence dependency supplies these comparisons; the theorem does not assume an
   arbitrary noncanonical extension functor.
6. The common-cover clause quantifies a genuine `Scheme.Cover` for `proetalePrecoverage`
   on W and ranks `m n : U.I₀ → ℕ`. For each cover member it gives isomorphisms of the
   restricted r^*L and s^*M with `Mod.finiteFree ... (m k)` and `(n k)` and of P with
   `Mod.finiteFree ... (m k * n k)`. This expresses simultaneous local triviality and the
   rank product using the existing finite-free object, including zero ranks.
7. `∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ q).obj source)` gives
   exactly the cohomological degree-zero concentration.
8. `IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ 0).obj source)`
   is the finite constant local-model constructibility from the dependency, rather than
   the different locally-finitely-presented constructibility predicate.
9. `Nonempty (upperStar c (H^0 source) ≅ P)` gives the stated finite-free module on W.
   For every scheme morphism g whose image is disjoint from W the final `IsZero` clause
   says that the restriction of H^0 is zero. This is the zero model off W, with no
   reduction or arbitrary choice of complement scheme built into its meaning.
10. No `Nonempty`, positive-rank, nonzero-ring, finite-type, separatedness, coefficient
    admissibility or base-field hypothesis occurs. The only universe parameter is u;
    schemes and covers have their recorded universe, and abelian sheaves have u+1.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; its `IsNoetherian` class
  confirms that the two hypothesis binders are exactly the node's convention.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` with `isCompact_univ`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` is the transparent
  `Mon` abbreviation; the theorem uses its underlying ring-object presentation with the
  commutativity instance. No condensed-ring definition is copied.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `condensedRingObj`,
  `coefficientRing`, `condensedPullbackHom` and its isomorphism instance.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module action.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the dependency's
  record also names the standard `DerivedCategory`; this statement needs that ordinary
  unbounded category, not a separate right-derived functor construction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` reexports
  `CondensedRing.derivedTensor` and the ordinary unbounded relative tensor structure.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Sheaf.Paper.CondensedConstantConstructibility`: `IsConstantModelConstructible`,
  with `HasFiniteConstantLocalModel` and `IsFiniteConstantStratified` read in full.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`, its two factorization
  equivalences, its coborder factorization and base-change/composition instances.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`, with scheme pullbacks supplied by the scheme infrastructure.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage` is the
  sheafified left Kan inverse image; the module-object `upperStar` uses this same small
  pro-etale inverse image followed by the canonical coefficient isomorphism.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `openImmersionLowerShriek` is restriction along α then the linear open extension;
  `lowerShriek` is compactification lower shriek. For an immersion the present degree-zero
  extension uses the node's prescribed closed/open operations directly, avoiding an
  extra `HasCompactification` hypothesis.
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`:
  `Scheme.locallyClosedExtensionCoherence`, its exact module-extension data, normalized
  comparisons, derived coherence and restriction-induced Hom bijection. Its coefficient
  category is ring-module sheaves; the statement uses the equivalent already recorded
  internal-module presentation of its closed/open constructions.
- Other actual constructors: `MorphismProperty.MapFactorizationData`, `ObjectProperty.ι`,
  `Functor.whiskeringLeft₂`, `Functor.postcompose₂`, `DerivedCategory.singleFunctor`,
  `MonoidalCategory.curriedTensor`, `Mod.finiteFree`, `CondensedRing.upperStarComp`,
  `CondensedRing.upperStarLowerStarAdjunction`,
  `CondensedRing.openImmersionLowerShriekUpperStarAdjunction`, and the existing fully
  faithful open-extension instances. The two open units are inverted only using these
  existing instances, never by a new proof obligation or a hollow choice.

All recorded statement-dependency signatures and docstrings were read in the local live
source. The proof-only imports supply the existing support projections, coefficient
comparisons, finite-free exactness, flat-single conventions, ring-sheaf base-change mates,
and normalized locally closed extension coherence. No dependency interface is replaced.

Searches actually run through the prescribed msearch wrapper:

- LeanFinder: `derived tensor of extensions by zero of locally free sheaves equals extension
  from fibre product intersection`; eight hits on free module sheaf maps and pullback of
  free module sheaves, no exact tensor-intersection assertion.
- Loogle: `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor, IsImmersion`; no hits;
  the remote index reported unknown identifier for the project-specific derivedTensor.
- Mathlib grep: `locallyClosed.*[Tt]ensor|[Tt]ensor.*[Ii]ntersection`; zero hits.
- LeanSearch: `derived tensor extension by zero locally closed lisse sheaves fibre product`;
  eight unrelated hits, including Cartesian sheaf tensor and zero objects in derived
  categories, no match.
- Mathlib grep, subdirectory CategoryTheory: `MapFactorizationData|finiteFree`; eleven
  hits including the actual MapFactorizationData definition, which was reused.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `locallyClosed.*[Tt]ensor|[Tt]ensor.*[Ii]ntersection|<item id>` found the older
  `locallyClosedImmersionTensorProjection` and unrelated intersections; its field and
  finite-type assumptions were read and disqualify it as an exact existing match.
  No declaration tagged with this node id existed.

Edge cases checked before and after writing:

- W empty, including disjoint supports: no nonemptiness requirement on a cover or on a
  scheme is imposed, and the off-support formula makes H^0 zero. Finite free modules on
  the empty scheme are permitted and the displayed derived objects are zero.
- m=0 or n=0: `ℕ` ranks and `Mod.finiteFree` on `Fin 0` preserve the zero case.
- Zero coefficient ring: no nontriviality assumption, and rank is not claimed unique.
- S=T=X and identity immersions: the assertion specializes to tensor of the two lisse
  modules in degree zero.
- Nonreduced intersection: W is the scheme pullback, not a reduced support substitute.
- Ranks varying over cover members and disconnected schemes: m,n are functions on the
  cover index; no connectedness or globally constant-rank condition is imposed.
- Arbitrary condensed rings and Noetherian schemes not over a chosen field remain in scope.

Validation: the prescribed scompile wrapper compiled both its sandbox copy and the actual
module name cleanly, approximately 5--6 seconds each, under the fixed 60-second limit.

## Second reading by O2

I reopened the completed node and module and reread the seven clauses against the actual
signature. This is a separate pass by this worker; no independent subagent was started,
as the dispatcher explicitly forbids starting other agents. The maintainer's independent
review is still required on the delivery.

This pass caught that a first version quantified only closed-then-open choices. I changed
`GeneratorFactorization` to the sum of both existing Mathlib factorization types and added
the open-then-closed branch of both the actual extension and its canonical restriction map.
The universal comparison equation now ranges over both orders, including mixed comparisons.
The pass also checked that the degree-zero object is extension of the ordinary tensor,
that the relative tensor really has coefficients R_W, and that the common-cover clause
lists all three isomorphisms with ranks m,n,mn. The off-W zero clause and the actual scheme
pullback remain explicit. I checked the source/target orientations in the comparison equation:
source comparison followed by the new isomorphism equals the old isomorphism followed by
the target comparison. Both normalization maps have the same target id, so their premises
say identity after restriction. The completed module then compiled cleanly again.

There are no new nodes, dependency modules, statement changes, definitions containing sorry,
extra axioms, or proved theorem bodies in this delivery.
