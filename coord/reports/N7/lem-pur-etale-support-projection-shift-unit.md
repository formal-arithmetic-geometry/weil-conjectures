## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit` states
`AlgebraicGeometry.Etale.etaleSupportProjectionShiftUnit`, with proof `sorry`.
Its nine supporting declarations contain real constructions or predicates; no data is
postponed. The node is unchanged except for its `lean` record. There are no new nodes,
dependency repairs, statement corrections, or disputed statements.

I read the node, all ten statement dependencies and their recorded interfaces, the
available proof-dependency modules, Zheng Theorem 2.18(2) (printed p. 12) and
Construction 2.26 (printed p. 15). The former gives exactly the coefficient-first
projection. The latter explains why its inverse and its coherence are needed by the
exceptional-inverse-image consumer. The node's six proof steps are reproduced, with
all cited node names, in the theorem docstring. The old CompactObject example module
is withdrawn; its node now records the upstream declaration.

Hypothesis and clause correspondence:

- Algebraically closed field of positive characteristic: `(k : Type u) [Field k]
  [IsAlgClosed k] (p ell : ℕ) [CharP k p] (_hp : 0 < p)`.
  The prime different from the characteristic is `(_hell : ell.Prime) (_hne : ell ≠ p)`.
- Finite commutative coefficient ring annihilated by a power of ell: `(C : Type (u + 1))
  [CommRing C] [Finite C] (_hC : ∃ N : ℕ, (ell ^ N : C) = 0)`.
- Finite-type k-schemes: `{X Y : Scheme.{u}}` with `X.Over (Spec (.of k))`,
  `Y.Over (Spec (.of k))`, and `LocallyOfFiniteType` and `QuasiCompact` on both
  structure maps. There is no separatedness assumption on either structure map.
- The separated finite-type k-morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
- The chosen factorization is `(c : Compactification f)`: its `i` is the open
  immersion, `g` is proper, and `comm` is `f = c.i ≫ c.g`.
- The category is the recorded ordinary unbounded `DerivedCategoryModule C T`,
  definitionally `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat C))`.
  There are no boundedness, constructibility, perfectness, or Tor-amplitude restrictions.
- `F = Rr_* j_!` is the existing `rightDerivedLowerShriekOfCompactification A c`,
  definitionally the exact derived open extension followed by the right derived
  proper direct image. This is not the right derived functor of their underived composite.
- `supportProjectionSource A c` has value `L ⊗^L F K` at `(K,L)`;
  `supportProjectionTarget A c` has value `F(f^* L ⊗^L K)`.
  Both are actual bifunctors, including their action on morphisms.
- `supportProjectionMap A c` is the existing `projectionMapOfCompactification A c`
  preceded by the inverse of `derivedTensorSymmetry A Y` and followed by the image
  of `derivedTensorSymmetry A X`. The existing projection is exactly proper counit
  projection, inverse open tensor projection, and pullback composition transport.
  Naturality of the signed symmetry moves the final swap through the open map,
  giving precisely the two coefficient-first arrows in the node, including the
  canonical `j^*r^* ≅ f^*` identification. No arbitrary morphism is supplied.
- `∃ e : supportProjectionSource ... ≅ supportProjectionTarget ...` together with
  `SupportProjectionCoherent ... e` asserts a bifunctor natural isomorphism whose
  hom is exactly `supportProjectionMap`. Thus it is natural in both variables and
  exists on the localized categories, independently of resolution choices.
- The source/target CommShift instances are inherited from first-factor derived
  tensor and the composite of exact pullback, first-factor tensor and `F`.
  They are canonical instances, with no existential choice of shift structures.
  `NatTrans.CommShift (e.hom.app K) ℤ` is precisely
  `P_(L[n],K) ≫ c_B = c_A ≫ (shiftFunctor _ n).map P_(L,K)` for every integer n.
  The predicate also asserts this for `e.inv.app K`.
- `supportProjectionTargetUnit A c K` is `F` applied to the pullback unit isomorphism
  tensored on the right with `K`, followed by the canonical left tensor unitor.
  The two unit equations in `SupportProjectionCoherent` say that the hom and inverse
  become identity maps on `F K` under these fixed source/target unit identifications.
- The ordinary termwise constant complex functor is the existing `constantFunctor C T`,
  namely `(constantSheaf T.smallEtaleTopology (ModuleCat C)).mapDerivedCategory`.
  `constantFunctorCompLeftDerivedUpperStarIso C f` is the existing canonical natural
  isomorphism `constantFunctor C Y ⋙ Lf^* ≅ constantFunctor C X`, applying to every
  object of `DerivedCategory (ModuleCat C)`.
- `SupportConstantPullbackCoherent ...` asserts that this particular comparison and
  its inverse commute with every integer shift. Its unit equation identifies the
  component at the regular coefficient module in degree zero with
  `leftDerivedUpperStarUnitIso`, using `supportConstantUnitIso` on both schemes.
  The latter is constructed from the exact-functor/single comparison, the monoidal
  constant-sheaf unit and `singleFunctorObjUnitIso`; it is not chosen from existence.
- The two `NatTrans.CommShift (Functor.whiskerLeft (constantFunctor C Y) ...) ℤ`
  clauses explicitly specialize the hom/inverse projection to every constant derived
  coefficient. Their unit property is the already stated hom/inverse unit equation
  transported along `supportConstantUnitIso`. Thus the specialization retains both
  shift and unit properties without restricting the coefficient complex.

Dependency declarations used (namespace `AlgebraicGeometry.Etale` unless specified):

- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  its finite-type, separatedness, and over-base properties are the existing Mathlib
  scheme morphism classes listed above, imported through compactification.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and the upstream `Compactification`
  from `WeilConjectures.Compactification.Defs`. The category/refinement part of the
  dependency is not redefined; the item uses only its compactification objects.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `DerivedCategoryModule`, using its recorded module-sheaf encoding.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`: `derivedTensorSymmetry`,
  the descended Koszul-signed braiding, rather than the old Nonempty wrapper.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`, identifying the exact pullback
  with the constant-ring module inverse image used by the derived framework.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap`, the counit-defined projection.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, the actual sheafified extension by zero.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection`:
  `projectionMapOfCompactification`, with its proper/open component formula;
  `...LowerShriekProjectionShift` supplies the canonical derived shift interfaces.
- `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`: `constantFunctor`,
  `constantFunctorCompLeftDerivedUpperStarIso`; `...TensorStructure`:
  `derivedTensorLeftUnitor`; `...UpperLowerStar.FlatModuleCat`:
  `upperStarPreservesFlat_moduleCat` supplies the structural instance, not a new hypothesis.

All available remaining proof dependencies are ordinary, non-public imports:
`Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
(`isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion`),
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
(`derivedOpenImmersionLowerShriekProjectionIso`),
`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
(`canonicalDerivedPullbackCompositionMonoidal`),
`Sheaf.Paper.ProjectionMateExact` (`SheafOfModules.ringedProjectionMateExact`),
`Sheaf.Paper.DerivedAdjunctionShift` (`CategoryTheory.derivedAdjunctionShiftCompatible`),
`Sheaf.CategoryTheory.FiniteTypeConstantExact`
(`SheafOfModules.strictPerfectConstantSheaf_exact`), and
`Sheaf.AlgebraicGeometry.PullbackConstantModule`
(`AlgebraicGeometry.Scheme.pullback_constantModule_isIso`).
The tensor symmetry and unit proof dependencies are also statement-construction imports.
No import cycle is introduced.

Edge cases checked before finalizing:
empty schemes and empty open immersion; zero K and zero L; the zero coefficient ring
(allowed also when N=0); identity open or proper factors; arbitrary positive and negative
integer shifts, and shift zero; genuinely unbounded coefficient complexes; nonseparated
finite-type X or Y. None is excluded by the signatures. The Koszul shift calculation in
the docstring cancels `(-1)^(n*p)` against the shifted swap, including odd p,q,n.
The field and coefficient universes follow the published small-etale-site convention;
they do not identify its object and morphism universes.

Searches actually run (including the retained search log from before interruption):

- `msearch.py leanfinder`: "Unbounded etale compact support projection formula commutes
  with coefficient shifts and preserves the tensor unit" returned eight algebraic-etale
  or Kaehler-differential hits, none the specified statement.
- `msearch.py loogle`: `"projection", "CommShift"` returned zero hits.
- `msearch.py grep`: `projection.*(commShift|shift|unit)|[Ll]ower[Ss]hriek.*[Pp]rojection`
  in Mathlib CategoryTheory returned zero hits.
- The retained `leansearch` query "Canonical compact support projection formula in the
  unbounded etale derived category commutes with coefficient shifts and preserves tensor
  units" returned eight shift/adjunction/t-structure declarations, no exact statement.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for projection and shift/unit
  found the upstream proper/open compactification projection and its shift instances,
  which are reused here. Existing ordinary compact-support projection interfaces omit
  the full coefficient-first unit and constant-pullback normalization of this item;
  pro-etale, adic and coefficient-system results concern different categories.
- Direct node-id search in `lean/WeilConjectures` returned no item declaration. Searches
  for all ten proposed full declaration suffixes in both Lean roots returned no collision.

Validation: `scompile.py N7 lem-pur-etale-support-projection-shift-unit <module>` succeeded
for both sandbox and library module names (37.4 s and 23.2 s), without errors or warnings.
Earlier probes diagnosed a missing in-scope `UpperStarPreservesFlat` structural instance
and expensive comparison of concrete monoidal instances. The final helper constructions
work over a general coefficient category before specializing to modules, following
`TensorStructure.lean`'s implementation note. The module has explicit universe binders,
`autoImplicit false`, no local notation or local instance, no diagnostic commands and
no data-level sorry. Only the named main theorem is postponed.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
