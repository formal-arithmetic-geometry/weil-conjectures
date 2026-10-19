## Worker report

The single delivered module is
`Sheaf.AlgebraicGeometry.ProEtale.BasisDerivedDetection`, with primary declaration
`AlgebraicGeometry.Scheme.ProEt.isIso_of_isIso_basis_derivedEvaluation`.
The theorem has proof `sorry`; all definitions and instances contain real data.
The node statement and all statement/proof dependency lists are unchanged.
There are no new nodes or dependency modules in the repaired delivery.

The blueprint source was reopened on the project server at
`literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-basis-derived-detection.md`,
order 1288. Its proof takes a cone, computes derived sections using injective
representatives, sheafifies section-complex cohomology and uses basis vanishing.
The expanded six-step DAG proof is included in the theorem docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Affine scheme: `(X : Scheme.{u}) [IsAffine X]`.
- Arbitrary commutative ring: `(R : Type u) [CommRing R]`, using the recorded
  coefficient-size convention of `Scheme.proEtaleDerivedCategory`. There is no
  finite, nontrivial, torsion, characteristic or invertibility assumption.
- Chosen small presentation: `proEtaleSiteModel X`, the existing
  `AsSmall.{u+1} X.ProEt`, with the existing `proEtaleModelTopology X`.
  This transports along `AsSmall.down`; the original site has object universe
  u+1 and morphism universe u. The small model enlarges only Hom sizes.
- Constant coefficient sheaf: `smallConstantRing X R` transports the existing
  `proEtaleConstantRing X R`, forgetting commutativity, by the existing continuous
  pushforward along `AsSmall.down`. It is the specified constant sheaf, rather
  than an arbitrary supplied ring sheaf or a new constant-sheaf construction.
- Category A = Mod(R_X): `smallModules X R` abbreviates the recorded
  `CategoryTheory.ringedSiteModules.{u+1}` of that transported ring sheaf.
  This is Mathlib's `SheafOfModules`, with its actual abelian structure.
- D+(A): `smallDerivedPlus X R` is Mathlib's `DerivedCategory.Plus` with
  `HasDerivedCategory.standard`. It includes every object with some cohomological
  lower bound and has no fixed lower bound or upper bound.
- Arbitrary morphism u: `{K L : smallDerivedPlus X R} (f : K ⟶ L)` quantifies
  over all localized morphisms, not only selected representative chain maps.
- Affine ind-etale basis: `W : X.AffineProEt`, embedded into `X.ProEt` by the
  recorded `AffineProEt.toProEt X`. On affine X these are exactly the affine
  ind-etale objects, with the induced coverings.
- Derived evaluation RΓ(W,-): `smallDerivedEvaluation X R W` is Mathlib's
  `rightDerivedFunctorPlus` of the actual `SheafOfModules.evaluation` at
  `AsSmall.up.obj W`, with target Plus of modules over the evaluated coefficient
  ring. Its unit is invertible on bounded-below injective representatives, so
  it computes the stated section complexes and their morphisms.
- Hypothesis: `h : ∀ W : X.AffineProEt, IsIso
  ((smallDerivedEvaluation X R ((AffineProEt.toProEt X).obj W)).map f)` tests
  precisely every basis object and the same morphism f.
- Conclusion: `IsIso f` in the same bounded-below derived category.

`smallModulesEnoughInjectives` applies the existing
`SheafOfModules.isGrothendieckAbelian` and
`IsGrothendieckAbelian.enoughInjectives` on the small presentation. It is not
an extra hypothesis or a choice from an unspecified existence theorem.
All variables/universes are explicit, and `autoImplicit` is disabled.
The `letI` expressions occur only in the derived-evaluation definition body,
never in the theorem signature. No theorem is proved in this delivery.

Recorded dependency declarations read:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` supplies site, coefficient
  and derived localization conventions.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` is the general ringed-site module category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory` and `HasDerivedCategory.standard`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.Plus`, the standard bounded-below full subcategory.
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `Scheme.AffineProEt`, `AffineProEt.toProEt`, and the induced topology.
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`:
  `AlgebraicGeometry.proEtale_restriction_injectives`, the currently published
  Q25 declaration for `lem-weil-pbc-proetale-restriction-injectives`.
  Its full signature and docstring were read locally and confirmed using
  `scompile.py --source`; its source blueprint, order 1280, was reopened.
  This theorem is cited by name in the stage-3 proof plan. Its proof-only
  module import has an upstream duplicate conflict, detailed below.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleConstantRing`, `Scheme.proEtaleSiteModel` and
  `Scheme.proEtaleModelTopology` supply the existing coefficient and transport
  constructions. The statement uses their recorded constructions unchanged.

Edge cases checked: the empty affine scheme and empty basis object; empty
covering families; zero rings and zero objects; disconnected affine schemes;
infinite coefficient rings; arbitrary characteristics; negative lower bounds;
and arbitrary derived morphisms. No nonempty, bounded-above or quasi-coherent
hypothesis is added. Evaluation is not asserted exact on sheaves, and the
cohomology sheaf is not identified with section-complex cohomology before
sheafification.

Searches (the original successful searches are in searches.jsonl, and the
following three Mathlib searches were repeated during this repair):

- LeanFinder: "Derived evaluation on all affine ind etale objects detects
  isomorphisms in the bounded below derived category of pro etale module
  sheaves" returned eight generic derived-representative/K-injective results,
  including `DerivedCategory.exists_iso_Q_obj_of_isGE` and
  `CochainComplex.IsKInjective.Qh_map_bijective`, not basis detection.
- Loogle: `DerivedCategory.Plus, "isIso"` returned three results.
  `DerivedCategory.Plus.isIso_iff` tests cohomology objects rather than derived
  evaluation on basis objects; the other two concern units on injectives.
- Prescribed grep: `isIso.*[Bb]asis|[Bb]asis.*isIso|derived.*[Ee]valuation`
  in `Algebra/Homology` returned no hits.
- `rg` for the item id in upstream `WeilConjectures` returned no hit.
  Searches in upstream and project Lean for the declaration name, basis-derived
  detection and derived evaluation found generic comparisons and unrelated
  evaluation constructions, but no existing statement of this theorem.
- The original LeanSearch query for derived sections detecting isomorphisms
  returned `Internal Server Error`: unavailable, not a negative mathematical
  result. Original independent LeanFinder/Loogle/grep searches and framework
  inspection are preserved in `scratchpad/report-before-return-repair.md`.

There is no statement correction or STATEMENT-DISPUTED issue.

## Repair of return L

The immutable-head return for c3329fbb5632 identified a stale overwrite of the
`lean` record of `lem-weil-pbc-proetale-restriction-injectives`. The current
published Q25 record is retained in full: the sandbox dependency JSON and its
old `ProEtale/RestrictionInjectives.lean` module were removed. This delivery
therefore cannot overwrite that dependency. The main theorem signature and
all five helper declaration names are unchanged; the stage-3 proof docstring
now names the published `AlgebraicGeometry.proEtale_restriction_injectives`.

The published theorem quantifies over every weakly etale object W and every
ring in Type (u+1), with no finite-coefficient hypothesis. It supplies the
site equivalence with underlying-object/morphism and covering-sieve formulas,
exactness of localization restriction, preservation of injective module
sheaves, and the canonical unbounded derived comparison specified by its
ordinary sectionwise isomorphism and derived-functor unit equation. This
provides the restriction fact used in step 2 of this item's proof. The
published fixed-ring-module encoding is canonically equivalent to modules
over the constant ring sheaf; the item itself continues to use precisely its
recorded ringed-module category and right derived evaluation.

Import repair: initially changing the old dependency import to the published
`Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives` produced this confirmed
compiler failure:

```
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs failed,
environment already contains 'AlgebraicGeometry.ProEtale.«term(_)_*[_]»'
from WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
```

The published theorem's import closure uses the reorganized finite-coefficient
Defs, whereas the existing `ProEtaleInverseImage` constructions used by the
statement import native Defs. Following the explicit duplicate-declaration
repair instruction, the module retains the native API needed to state the
item and omits this conflicting proof-only dependency import. It neither
reintroduces a private restriction theorem nor changes the published record.
Stage 3 must resolve that upstream import overlap before invoking the named
proof dependency in this module.

The previous independent second reading applied to the returned two-module
version. Its report is archived in the sandbox scratchpad, not presented as a
review of this repaired one-module delivery. A fresh second reader will check
this repair and perform the actual delivery. Compilation and the no-push dry
run are performed by the worker before returning READY.

## Second reading by Q31

I independently reopened the item node, its source place (blueprint order 1288), the
current sandbox module, and every recorded statement dependency. The six clauses of
the node match the Lean signature as follows.

- The affine scheme is `(X : Scheme.{u}) [IsAffine X]`; no separatedness,
  Noetherianity, nonemptiness, or characteristic hypothesis is added.
- The coefficient is an arbitrary `(R : Type u) [CommRing R]`. This is the recorded
  pro-etale coefficient convention, with no finite, torsion, field, invertibility, or
  nonzero assumption.
- `proEtaleSiteModel X` and `proEtaleModelTopology X` are the existing `AsSmall`
  presentation and transported topology. `smallConstantRing X R` is the existing
  `proEtaleConstantRing X R`, after the recorded commutative-to-ring forgetful map and
  canonical continuous pushforward along `AsSmall.down`; it is not a private constant
  sheaf. The original pro-etale object and morphism universes remain distinct.
- `smallModules X R` is `ringedSiteModules` (Mathlib's `SheafOfModules`) over that
  transported ring sheaf, with its existing abelian structure. The actual instance
  `smallModulesEnoughInjectives` supplies enough injectives from the existing
  Grothendieck-abelian theorem and is not an extra theorem hypothesis.
- `smallDerivedPlus X R` unfolds to `DerivedCategory.Plus` with
  `HasDerivedCategory.standard`; this is the standard full bounded-below derived
  subcategory, with an arbitrary cohomological lower bound. The broader bounded-
  subcategory dependency has no recorded Lean declaration, but the required D+ notion
  is the exact Mathlib `DerivedCategory.Plus` used here; no private replacement is
  introduced.
- `{K L : smallDerivedPlus X R} (f : K ⟶ L)` quantifies over an arbitrary morphism in
  the localized category, as the node requires.
- The basis variable is `W : X.AffineProEt`, embedded into the ambient site by the
  existing `(AffineProEt.toProEt X).obj W`; this is the affine ind-etale basis and has
  the induced coverings.
- `smallDerivedEvaluation X R W` is the actual right derived evaluation functor on
  `SheafOfModules.evaluation` at `AsSmall.up.obj W`, into the standard D+ of modules
  over the evaluated coefficient ring. Thus `h` tests exactly `RΓ(W,f)` for every
  basis object, and the conclusion `IsIso f` is in the same D+ category.

I checked the theorem docstring against the source proof: injective representatives,
restriction/evaluation on the basis, the evaluated mapping cone, exact module
sheafification, basis separation, and the cone/localization criterion occur in that
order. No clause of the conclusion is weakened or strengthened. `letI` terms occur
only inside the derived-evaluation definition, all variables and universes are bound,
and every postponed proof is a theorem proof consisting solely of `sorry`.

The edge cases include the empty affine scheme and empty basis object, empty covering
families, the zero ring and zero derived objects, disconnected affine schemes,
arbitrary infinite rings and characteristics, arbitrary integer lower bounds (including
negative bounds), and arbitrary derived morphisms. No `Nonempty`, `n = 0`, bounded-above,
quasi-coherent, or finite-coefficient assumption is present.

I repeated searches with different wording: LeanFinder for quasi-isomorphism detection
by hypercohomology on a basis; Loogle for `DerivedCategory.Plus` and `isIso`; grep in
Mathlib derived-category sources for conservative/evaluation/isomorphism criteria; and
`rg` in both `WeilConjectures` and project `lean/Sheaf` for basis detection and derived
evaluation. These found only generic cohomology, K-injective, and derived-functor
results, not this pro-etale basis theorem. The prescribed LeanSearch service was
unavailable, as recorded in the worker search log.

The only delivery mismatch was the stale dependency overwrite identified on return L:
the old private restriction-injectives copy and its node record were removed, the
published Q25 `AlgebraicGeometry.proEtale_restriction_injectives` record was retained,
and the main proof docstring names that declaration. Its `Λ : Type (u+1)` interface
applies to the transported `ULift` coefficient used by this statement. The attempted
proof-only import caused a duplicate upstream declaration, so it remains omitted; this
does not alter the item's statement or introduce another definition. After that repair
I found no remaining mismatch and changed no Lean signature or node statement.
