## Worker report

Module: `Sheaf.Paper.ContinuousAlgClOpenScalarComparison`.
Declaration: `AlgebraicGeometry.ProEtale.CondensedRing.continuousAlgClOpenScalarComparison_isIso`.
This is a statement-only delivery, with its sole proof `sorry`. The mathematical statement
is unchanged. The item gains only `lean` and a citation of the already landed definition
node `def-sfb-all-continuous-scalar-mate`; no new node or dependency module is needed.

Hypothesis and clause correspondence:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The algebraic closure with its extended ell-adic norm topology is the existing
  `PadicAlgCl ℓ`. Its canonical normed-field instance comes from
  `WeilConjectures.NumberTheory.Padics.Extension`; it is the algebraic closure,
  not its completion.
- Positive characteristic p different from ell: `(p : ℕ) [Fact p.Prime] (_hpℓ : p ≠ ℓ)`
  and `(k : Type u) [Field k] [CharP k p]`. A positive field characteristic is prime,
  so the prime instance excludes no source case.
- Schemes separated and finite type over k: `{U X : Scheme.{u}}`, their `Over (Spec (.of k))`
  instances, and `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` of both structure maps.
  As in the setting node, these are explicit binders; no unused compactification choice
  is added to the statement.
- One finite intermediate field: `(E : PadicAlgCl.FiniteIntermediateField ℓ)`.
  This is the subtype of intermediate fields equipped with finite dimensionality over
  `Padic ℓ`; it includes the bottom field E = Q_ell.
- A_E(S) = C(S,E) is `Profinite.continuousMapRingObj E.1`. The target coefficient B(S) =
  C(S,Omega) in `tameBoundaryScalarComparison` is
  `Profinite.continuousMapRingObj (PadicAlgCl ℓ)`.
  The recorded `continuousMapRingObjOfUniverse` specializes definitionally to these
  upstream constructors for the Type-zero coefficient fields. These are all continuous
  maps, with their pointwise ring structures. In particular the target is not
  `Profinite.padicAlgClRingObj`, which imposes finite-subextension-valued sections.
- Their coefficient map is `tameBoundaryScalarMap ℓ E`: postcomposition by `E.1.subtype`
  using `continuous_subtype_val`, followed by `coefficientMap` to each scheme. Thus
  `condensedRingObj` supplies exactly p_T^* A_E and p_T^* B.
- The geometric morphism is `(j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
  [QuasiCompact j]`, retaining both the k-linearity and the quasi-compact open condition.
- The ambient input is `(C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U)
  Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj E.1) U)))`:
  internal module objects, in the ordinary unbounded derived category.
- Bounded cohomology with finite constant local models on finite constructible
  stratifications is precisely the recorded
  `constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) U C`,
  passed as `_hC`. Its definition is the intersection of boundedness and
  `IsConstantModelConstructible` of every homology object. Its qcqs branch uses
  `Scheme.Stratification` and `HasFiniteConstantLocalModel`.
- Derived scalar extension is the existing `tameBoundaryScalarExtension ℓ E T`,
  defined as `(Mod.extendScalars (coefficientMap (tameBoundaryScalarMap ℓ E) T)).leftDerivedFunctor`.
  Direct image in the mate is `moduleObjectDerivedPushforward`, literally the total
  right derived functor of the full `CondensedRing.lowerStar` composite.
- The conclusion `IsIso (tameBoundaryScalarComparison ℓ E j C)` asserts invertibility
  of that arrow, rather than merely existence of some isomorphism between its endpoints.
  Reading its definition: `homEquiv` for the B geometric derived adjunction is applied
  to `(tameBoundaryScalarPullIso ℓ E j).hom.app (Rj_* C)` followed by the scalar extension
  of the A_E geometric counit. Its pullback is the exact levelwise pullback identified
  with total left derived pullback by `leftDerivedUpperStarIsoMapDerivedCategory`.
  `tameBoundaryScalarPullIso` is determined by the unique K-flat representative square
  `TameBoundaryScalarPullNormalized`, using the ordinary balanced tensor `pullIso` and
  preserving the scalar unit. This is exactly the two arrows and adjunct normalization
  in the node. The conclusion is already in the derived category, not just per degree.
- There is no completion, no interpretation of B as a filtered union, and no
  constructibility assertion on either result. No perfectness, finite Tor amplitude,
  tameness, smoothness, or properness hypothesis has been imposed on C or j.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, whose setting
  is rendered by explicit scheme structure-map binders. Imported for the recorded
  setting dependency; the compactification is not an input to this ordinary Rj_*.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, `continuousMapRingObjOfUniverse`;
  `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjMapOfUniverse` and the postcomposition formula.
  Their Type-zero upstream specializations are used by the existing mate definition.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj` and coefficient pullback.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and their action laws.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`; their full definitions were read.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction`, with its full ambient
  section hypotheses and `extendScalars.leftDerivedFunctor`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback`, together with the publicly exported
  `derivedUpperStarLowerStarAdjunction` and `leftDerivedUpperStarIsoMapDerivedCategory`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`:
  the general unique representative-normalized tensor compatibility. The already
  landed mate specializes the canonical scalar/pullback comparison to these coefficients.
- `Sheaf.Paper.AllContinuousScalarMate`: all six recorded declarations were read;
  `tameBoundaryScalarMap`, `tameBoundaryScalarExtension`, `TameBoundaryScalarPullNormalized`,
  `tameBoundaryScalarPullIso_existsUnique`, `tameBoundaryScalarPullIso`, and
  `tameBoundaryScalarComparison` are reused without any private copy.

All recorded, stated proof dependencies are imported without `public`.
The unstated proof nodes `lem-sfb-tame-pair-proper-generators`,
`lem-weil-pbc-mate-pasting`, and `lem-sfb-continuous-algcl-proper-scalar-comparison`
have no recorded module to import. They are still named at their exact uses in the
five-step theorem docstring. They are proof prerequisites, not prerequisites to type
this statement, and no proof or substitute for them is included here.

Edge cases checked before writing: C = 0 and arbitrary shifts remain permitted; a
bounded complex may have any integer amplitude and need not be a degree-zero sheaf.
Empty U, empty X, and the identity open immersion are not excluded. E = Q_ell is allowed.
The prime p is positive, including p = 2 when ell differs. No tame-pair hypotheses leak
from the proof generators into the input. The scheme universe u is arbitrary and the
small pro-etale site's abelian coefficient universe remains u+1; no site object/Hom
universe equality or size restriction has been introduced. The coefficient fields are
the fixed standard algebraic-closure model, so their Type-zero representation is no
restriction on the finite intermediate fields of that fixed closure.

Validation: `scompile.py O2 lem-sfb-continuous-algcl-open-scalar-comparison` compiled
both its private sandbox and library-module paths cleanly (4.9 and 4.7 seconds).
No errors or unexpected warnings were printed.

Searches actually run:

- `msearch.py ... leansearch`: "Open immersion derived direct image commutes with all
  continuous algebraic closure scalar extension on constructible l adic sheaves".
  Eight hits, all ordinary open-immersion definitions, stalk/section comparisons or the
  preimmersion instance. None states the coefficient-specific derived comparison.
- `rg` for the new full declaration suffix and item id in `lean/Sheaf`,
  `lean/WeilConjectures` and `dag/lean_names_upstream.json`: zero hits, so the declaration
  name does not collide with a published project or upstream name.

- `msearch.py ... leanfinder`: "Derived direct image along a quasi compact open immersion
  commutes with extension from finite l adic coefficients to all continuous algebraic
  closure coefficients". Eight hits: normalization/affine-transition-limit sections,
  structure-sheaf maps, and the ordinary module pushforward right-adjoint instance.
  None is the stated coefficient-specific derived mate theorem.
- `msearch.py ... loogle`: `"rightDerivedFunctor", "extendScalars"`: zero hits.
- `msearch.py ... grep`: `ScalarComparison|scalarComparison|derivedPushHom|derivedPullIso`:
  zero Mathlib hits.
- `rg` on `lean/WeilConjectures` with those names and the item id: the generic
  `ChangeOfCoefficients.derivedPullIso` and `derivedPushHom` exist, but they require
  exact scalar extension, and the published finite-extension/finite-subextension-union
  results do not assert the present all-continuous open comparison on these inputs.
  Other hits concern raw ordinary/etale coefficient comparisons.
- `rg` on `lean/Sheaf` with scalar comparison names: the exact arrow already exists in
  `AllContinuousScalarMate`; `TameBoundaryScalarComparison` states a restricted regular
  tame-boundary case, not the arbitrary bounded constructible input of this node.
  Thus the canonical map is reused, but no existing theorem states this item.
- The blueprint source file was opened, especially paragraph (3). The node explicitly
  records this as a separately stated all-continuous coefficient obligation; the
  blueprint's filtered-union Qbar finiteness is not substituted for it.

No statement correction or STATEMENT-DISPUTED finding is asserted. This delivery
formalizes the separately recorded obligation; it does not claim its analytic proof
is established by the existing finite-subextension coefficient framework.

## Second reading by O2

The dispatcher forbids starting another agent; this is a separate self-reading, with
independent review reserved for the maintainer as instructed in the worker brief.
I reopened the node, the theorem signature, and the existing mate definition. Each
geometric, characteristic and coefficient hypothesis is present as listed above.
The sole conclusion is invertibility of the prescribed adjunct, not constructibility
of its endpoints. The B constructor in the underlying map is the all-continuous
constructor, and the K-flat uniqueness condition fixes the tensor/pullback comparison.
The only extra dependency is the already landed node owning exactly that map; no
additional mathematical assumption or new definition was needed. The five-step proof
docstring retains the proper-generator reduction and canonical mate-pasting rather
than assuming invertibility of a generic projection map. No mismatch was found in this
reading and no statement correction was made.
