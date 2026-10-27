## Worker report

Stage 2, Q33, 2026-10-22. The delivery supplies
`Sheaf.Paper.FieldLisseStratifiedHeartSupport`, with the single theorem
`AlgebraicGeometry.ProEtale.field_lisse_stratified_heart_support`. Its proof is
`sorry`. There are no new definitions, dependency repairs, or statement changes.
The accepted Q101 stage-1 split is used unchanged. The prior worker's refusal to
re-split that accepted node concerns stage 1; this delivery only adds its absent
stage-2 Lean record and statement.

The source places read are main-20261015
`sk-lem-coefficient-heart/sk-lem-coefficient-heart.proof.md` (1) and
`sk-thm-sf-pf-field/sk-thm-sf-pf-field-tensor.proof.md` (1). The theorem's docstring
carries the eight steps of the reviewed DAG proof, with its exact dependency IDs.
No theorem is proved in this delivery.

Clause-by-clause match:

1. The arbitrary condensed ring is `Λ : Profinite.CondensedRing.{u}`; its
   underlying ring object is `Λ.X`, with `[IsCommMonObj Λ.X]` expressing
   commutativity. There is no assumption of a continuous topological presentation,
   admissibility, a particular prime, or an embedding into an adic coefficient ring.
2. `hfield : IsField (...)` says its actual scalar ring is a field. The expression
   is the existing `InternalAbelianSheafModule.sectionRingSheaf` evaluated at
   `Opposite.op (⊤_ Profinite.{u})`, exactly the terminal profinite set *. This
   retains its reconstructed multiplication and unit; it does not install an
   unrelated field structure on the underlying abelian group.
3. `X : Scheme.{u}`, `[IsLocallyNoetherian X]`, and `[CompactSpace X]` are exactly
   the stated Noetherian convention. No separatedness, finite type, or base scheme
   hypothesis is imposed. Site objects retain their full scheme/site universes,
   and the sheaves take values in `Ab.{u + 1}`.
4. Every ambient module category is the existing
   `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)`.
   `condensedRingObj` is the underlying ring object of `coefficientRing T Λ`.
   Thus all coefficients are the prescribed pullback from the point.
5. Lisse is the recorded `IsLisseCoefficientModule Λ.X`, whose definition uses
   a pro-etale cover and `Mod.IsFree`. The latter is explicitly existence of an
   isomorphism to `Mod.finiteFree R n` for `n : ℕ`, not arbitrary-rank freeness.
   Zero rank is permitted and different cover members may have different ranks.
6. Constructible is the recorded `IsConstantModelConstructible Λ.X X` throughout.
   It uses `HasFiniteConstantLocalModel` on a finite constructible scheme
   stratification in the qcqs case. On a Noetherian scheme the qcqs branch applies.
   Its pointwise finite presentations are matrices over the actual scalar ring,
   before pullback to the scheme, so they are precisely scalar constant models,
   rather than arbitrary locally finitely presented coefficient modules.
7. `hclosed` quantifies over every `T : Scheme.{u}` and `a : T ⟶ X` satisfying
   `IsImmersion a`. It asserts `IsClosedUnderKernels`,
   `IsClosedUnderCokernels`, and `IsClosedUnderExtensions` for lisse modules on T.
   The Mathlib closure classes concern maps whose two objects satisfy the
   predicate and short exact sequences whose two ends satisfy it. This is the
   stated three-part assumption, not unconditional closure for every field-valued
   condensed ring. No separate Noetherian hypothesis on T is added.
8. The first conjunct states `IsConstantModelConstructible Λ.X X 0`. The next
   four conjuncts are its `IsClosedUnderIsomorphisms`, `IsClosedUnderKernels`,
   `IsClosedUnderCokernels`, and `IsClosedUnderExtensions` classes. These are
   precisely the five operations requested on the full class in the ambient
   module category. No closure under arbitrary subobjects or quotients is claimed.
9. The final universal clause binds schemes S and Z, `j : S ⟶ Z` with
   `[IsOpenImmersion j]`, and `i : Z ⟶ X` with `[IsClosedImmersion i]`.
   The immersion a with its specified factorization is written as the actual
   composite `j ≫ i`; no equality of arbitrary unrelated maps is assumed.
   `Topology.IsConstructible (Set.range (j ≫ i))` is constructibility of its
   locally closed image.
10. Both extension functors have `PreservesFiniteLimits` and
    `PreservesFiniteColimits`. They are the recorded additive
    `CondensedRing.openImmersionLowerShriek Λ.X j` and
    `CondensedRing.lowerStar Λ.X i`, so this expresses exactness of both.
11. For every L in the actual module category on S with
    `IsLisseCoefficientModule Λ.X L`, the next conjunct is constructibility of
    `(lowerStar Λ.X i).obj ((openImmersionLowerShriek Λ.X j).obj L)`. This is
    exactly the node's G, using its specified extensions.
12. The first restriction is a `Nonempty` isomorphism from the actual
    `(upperStar Λ.X (j ≫ i)).obj G` to L. Tensor pullback already incorporates
    the canonical coefficient identifications, so its codomain is the category
    over `condensedRingObj Λ.X S`.
13. For a closed immersion `k : K ⟶ Z` with range complementary to j, the
    second restriction is `IsZero ((upperStar Λ.X (k ≫ i)).obj G)`.
    This expresses the Z minus S piece as an actual locally closed subscheme.
    It applies in particular to the reduced induced closed complement used in
    the DAG proof; no reducedness restriction is imposed on a representation
    of this piece. Vanishing is independent of its thickening, as restriction
    of open extension by zero vanishes along every disjoint closed immersion.
14. For an open immersion `v : U ⟶ X` with range complementary to i, the
    third restriction is `IsZero ((upperStar Λ.X v).obj G)`. This is the
    X minus Z piece, without making a noncanonical copy of the open-complement
    construction. The two universal complement clauses allow the canonical
    complement schemes and every isomorphic realization; they introduce no
    assumption that such complements need to be supplied before the theorem
    yields constructibility or the restriction on S.
15. The last conjunct is an isomorphism in the ordinary unbounded
    `DerivedCategory`, rather than only an assertion about its homology.
    `HomologicalComplex.single _ (ComplexShape.up ℤ) 0` is L[0] as a Z-indexed
    cochain complex. The two actual functors act termwise using
    `mapHomologicalComplex`; `DerivedCategory.Q.obj` then takes their result
    into the localization. The other side is
    `(DerivedCategory.singleFunctor _ 0).obj G`, exactly G[0]. Exactness was
    stated separately above; no unproved exactness instance is chosen in the
    construction of either derived object.

Dependencies read and used (module, declaration):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and the
  coefficient identifications.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its action.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and its topology.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`; its finite-free notion
  was also checked in `WeilConjectures.CategoryTheory.ModuleObjects.Free`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible` and its finite
  scalar-model and stratification definitions.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`.
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`. This dependency
  is a Mathlib leaf whose `mathlib_match` is its recorded interface.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar` and `upperStar`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  derived-category conventions; `DerivedCategory.Q` and `singleFunctor` use
  the Mathlib localization, not a second derived category.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf`, used to write
  the actual scalar-ring evaluation without introducing a duplicate notion.

Every recorded statement-dependency module is publicly imported. The recorded
proof-dependency modules are imported privately when present. For the Mathlib
leaves, the matching `Module.Free.of_divisionRing` and
`Functor.preservesHomologyOfExact` modules are imported. The three proof nodes
`lem-sfb-coefficient-heart-locally-closed-extension`,
`lem-sfb-lisse-module-inverse-image`,
and `lem-sfb-noetherian-complementary-stratifications` have no published
Lean records and are left as the existing proof plan, not re-stated here.
Their statements are not needed to type this stage-2 assertion.

Edge cases were checked before writing: X empty; L zero; rank zero and ranks
varying between cover members; S empty; S=X; j an identity (closed support);
i an identity (open support); empty complementary pieces; nonreduced X and Z;
a field of any characteristic. The quantified complement schemes can be empty.
There is no connectedness assumption or positive-rank condition. A zero scalar
ring is excluded exactly by the source's field hypothesis. The closure assumption
is substantial and is not inferred from the field hypothesis.

Searches made for this delivery, with their actual outputs retained in the
launcher's `searches.jsonl`:

- msearch LeanFinder: “Constructible internal modules with field scalars closed
  under kernels cokernels extensions and locally closed extension by zero”.
  Eight hits: condensed/light condensed modules, their abelian and Grothendieck
  structures, and `ObjectProperty.IsSerreClass`. None states the node. The last
  property would assert additional subobject/quotient closure and is not used.
- msearch Loogle: `IsConstantModelConstructible, IsLisseCoefficientModule`.
  Zero hits, with the service reporting the first identifier unknown. This was
  not treated as evidence that the local project's definitions were absent.
- msearch grep: `IsConstantModelConstructible|IsLisseCoefficientModule|constructible.*[Ss]erre`.
  Zero Mathlib hits. Project rg searches of `lean/Sheaf/Paper` and
  `lean/WeilConjectures` found the recorded notions and many specialized consumers.
- msearch LeanSearch: “Constructible modules locally closed extension by zero
  kernels cokernels extensions”. Eight hits about ordinary module kernels and
  cokernels and their universal properties, none about this stratified assertion.
- Direct rg of both project roots for the node ID and chosen declaration name
  found no existing theorem. The coefficient-heart closure declaration was read:
  it is specialized to continuous E/Qbar coefficients; the integral-heart
  declarations are specialized to integral coefficients and arithmetic schemes.
  None states this arbitrary condensed ring with scalar field and the explicitly
  assumed stratumwise lisse closure together with the support assertion.

No STATEMENT-DISPUTED flag or node fault was found. In particular the field
hypothesis is not silently used to deduce unconditional lisse closure.

## Second reading by Q33

This is a second pass by the same isolated worker; no independent worker or
sub-agent was started. The maintainer's independent review remains the independent
reading, as specified by the dispatcher brief.

With the current node and module open, I checked the fifteen correspondences
above again, the right-associated conjunction scopes, and the type of every
restriction. The complement clause for K is inside Z before composition with i;
the complement clause for U is inside X. Thus neither zero restriction uses the
wrong ambient complement. All coefficients are `Λ.X` pulled to the appropriate
scheme, and G uses lower-star after open lower-shriek in the correct order.
The zero and isomorphism clauses are present as well as the three closure clauses.
The conclusion does not impose the closure assumption on arbitrary unrelated
schemes, only on the locally closed subschemes named by the node. No source
hypothesis is omitted or supplied by a hollow hypothesis.

Two compiler-detected API corrections were made: `DerivedCategory.Q` has an
implicit category argument, and `CochainComplex.single₀` is N-indexed, so it was
replaced by the Z-indexed `HomologicalComplex.single` at degree zero. These
corrections preserve the intended derived statement. A line-length warning was
fixed by wrapping that expression. No mathematical correction was required.
