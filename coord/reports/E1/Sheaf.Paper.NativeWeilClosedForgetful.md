## What changed

Proved the four ordinary tensor/internal-Hom additivity instances in
`Sheaf.Paper.NativeWeilClosedForgetful`, without changing their signatures, attributes,
visibility or definitions. Source-variable additivity uses `Mod.ihomMap_add` and
`Mod.tensorLeftMap_add`. Target-variable additivity uses the existing `Mod.ihom`
instance and `(Mod.ihomAdjunction P).left_adjoint_additive`.

Marked `NativeAdjunctionNormalization` and `native_closed_forgetful` with
`STATEMENT-DISPUTED` comments. The main theorem requires a chain-level normalization
that fails the chain-map equation; the precise example is below. The disputed
formula and the theorem statement were preserved, rather than replaced with a
weaker assertion. This is a partial proof delivery under the several-sorries rule.

Validation: the delivered module compiles cleanly through `lcompile.py` after removal
of all eight unused private proof imports (23.0 seconds). Separate sandbox experiments
also compiled the first four clauses of the main theorem from the existing exact
forgetful-functor API. The scalar chain-square obstruction was checked in Lean as well;
these scratch files are not library additions or claimed proofs of the main theorem.
Searches used the required `msearch.py` LeanFinder, Loogle and grep routes, followed by
source inspection of both library roots. The main comparison has no one-line match;
the additivity results are already available in `Mod/Tensor.lean`.

## Proved and sorry left

Closed four existing holes, all attached to `lem-sf-weil-native-closed-forgetful`:

- `AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryIhomBifunctor_additive`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryIhomBifunctor_obj_additive`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryTensorBifunctor_additive`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.ordinaryTensorBifunctor_obj_additive`.

The only remaining hole is
`AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`, attached to the same node.
Its proof remains exactly `by sorry`. Five original holes, four closed, one retained;
zero new holes, zero split-off statements. No axiom or hollow definition was introduced.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.Paper.CompletedCondensedCoefficients`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`.

No public import, node or module is withdrawn. In particular the three assembly
obligations and the unit route are retained: the unfinished main proof still needs
its mathematical dependencies. Removing unused private imports does not assert that
those dependencies have become globally unnecessary. The main proof plan was not
changed, so no node proof/dependency update is included.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the extra `(-1)^(p*q)` in
`NativeAdjunctionNormalization` is incompatible with the native Hom differential.
This propagates through `NativeOrdinaryTensorModels` into the last existential clause
of `native_closed_forgetful`.

The source code gives the native differential on a source-index-p projection as
`(-1)^p (d_I f - f d_P)`: see
`WeilConjectures/Algebra/Homology/BifunctorHomComplex.lean`,
`CochainComplex.bifunctorHomObj_d_π`. The total tensor with first curried degree p
has differential `d_P + (-1)^p d_Q`: see Mathlib's `mapBifunctor.d₁_eq`,
`mapBifunctor.d₂_eq` and the `ComplexShapeSigns` instance with ε₁=1, ε₂=(-1)^p.
These conventions require unsigned componentwise uncurrying for maps of complexes.
An underived reversal of the actual tensor factors changes no degree convention in
`mapBifunctor P Q T`.

For an explicit local test, work with a nonzero characteristic-zero coefficient
module R. Let P be R concentrated in degree 1. Let Q be the contractible disk
R --id--> R in degrees 0 and 1. Put V = (T.obj R).obj R, and take the contractible
K-injective disk I = (V --id--> V) in degrees 1 and 2. P is K-flat for the coefficient
unit, and Q is contractible, hence K-flat. The native Hom from P to I has differential
minus the identity in degrees 0 and 1. If c is the adjunction transpose of id_V, then
φ: Q --> Hom_native(P,I) with components c in degree 0 and -c in degree 1 is a chain
map. All other components vanish.

The disputed formula requires the restriction of ψ to the (p,q)=(1,0) summand to
be id_V. On the (1,1) summand it also requires id_V: the prescribed minus sign
cancels the minus in φ¹. But the total tensor differential between these summands
is -id_V, whereas the differential in I is id_V. Thus the chain-map equation for ψ
would be id_V = -id_V. This is false for the coefficient unit in characteristic zero.
Both disks are contractible, so imposing K-injectivity or simultaneous K-flatness
does not remove the example. The obstruction precedes any derived adjunction or
representative isomorphism and cannot be fixed by choosing those isomorphisms.

The adopted source independently confirms the sign computation:
`WeilConjectures/Algebra/Homology/InternalHom.lean`, its Sign conventions paragraph
and proved `CochainComplex.ιTensorObj_internalHomEquiv_symm_f`, give plain uncurrying
for the same row-sign differential. A factor `(-1)^(p*n)` occurs for cochains of
cohomological degree n, and disappears for degree-zero chain maps. A factor
`(-1)^(p*q)` instead appears when uncurrying the standard-sign Hom complex; it
must not be applied again to the native row-sign Hom complex.

The existing stage-2 reader's claim that the signs were checked misses this
differential test. The likely repair is to remove the factor from this native
normalization and adjust its explanatory docstring, or consistently change both
Hom and tensor conventions. This packet leaves the interface untouched so the
independent reader can assess that repair before it is used in a proof. No claim
is made that a lack of proved dependencies obstructs assembly: their stated
lemmas are usable, but none can establish this incompatible chain-map condition.

The non-closed clauses do have a direct route: exact forgetting already localizes
triangulatedly; `mapDerivedCategoryHomologyFunctorIso` supplies the cohomology
comparison; `DerivedCategory.isIso_iff` and ordinary conservativity give derived
conservativity; `bounded_mapDerivedCategory_obj` and invariance of constructibility
under that cohomology isomorphism give the restriction to Weil complexes. This was
checked in the sandbox, not left as additional library holes.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
