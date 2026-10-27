## Worker report

The module `Sheaf.AlgebraicGeometry.NoncommutativeRingedOpenClosed` states
`AlgebraicGeometry.ProEtale.noncommutative_ringSheaf_open_closed` with `sorry`.
Two transparent helpers belong to this assertion: `ringSheafOpenClosedAssertions`
spells out its conclusions once so the identical assertions apply after transport;
`ringSheafScalarEquivalence` constructs the specified restriction-of-scalars equivalence.
Neither helper contains postponed data. No statement correction or new DAG node is needed.

### Hypotheses and objects

- An arbitrary scheme and the two pieces are `{X Z V : Scheme.{u}}`.
  The arrows `(i : Z ⟶ X) (j : V ⟶ X)` carry `[IsClosedImmersion i]`,
  `[IsOpenImmersion j]`, `[QuasiCompact j]` and the complement equality
  `_hV : Set.range j = (Set.range i)ᶜ`. There is no compactness,
  quasi-separatedness, Noetherian or commutativity binder.
- The small sites are `Scheme.ProEt.topology X`, and analogously for Z,V.
  These retain the site's object universe u+1 and arrow universe u. Coefficients
  are `Ab.{u+1}`. Universe variables are explicit and `autoImplicit` is false.
- The ring object is `(B : Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) [MonObj B]`.
  `Ab` has the integer tensor, and sheaves have its canonical sheafified tensor.
  This is the monoidal structure packaged by `sfbSheafTensorStructure`, not a
  second tensor construction or the cartesian tensor.
- The module categories are exactly Mathlib's `Mod`, inferred by the canonical
  operations; the pulled-back coefficients are `(upperStar Ab i).obj B` and
  `(upperStar Ab j).obj B`. The existing `Mod.instAbelian` supplies abelianity;
  `Mod.forget` preserves finite limits and finite colimits, hence kernels and
  cokernels are computed on carriers. These are available instances, not added
  assumptions in the theorem.
- `ringSheafInverseImage`, `ringSheafDirectImage`, `ringSheafOpenExtension`,
  `ringSheafAdjunction` and `ringSheafOpenAdjunction` are the dependency's existing
  operations. They use mapMod, restriction along the actual ring unit, and
  mapModLeft of the abelian extension-by-zero adjunction, respectively.

### Every conclusion

- The three canonical adjunctions are the three explicit arguments to the first
  `ringSheafOpenClosedAssertions`. Their types fix the asserted functors and maps;
  there is no existential choice of an adjunction.
- The next six conjuncts equate `.hom` of each actual module unit/counit with
  `.unit.app M.X` / `.counit.app N.X` of the corresponding abelian adjunction.
  They cover both closed maps, both open inverse/direct maps, and both open
  extension/restriction maps.
- Expanding `ringSheafOpenClosedAssertions`, its first five conjuncts state
  additivity of i-star, i-lower-star, j-star, j-lower-star and j-shriek.
- Its next eight conjuncts state `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for i-star, j-star, i-lower-star and j-shriek.
- Three universal `IsIso` clauses state invertibility of the actual closed
  counit, actual open inverse/direct counit, and actual open extension unit.
- Two universal `IsZero` clauses give j-star i-lower-star=0 and i-star j-shriek=0.
  They assert vanishing on every object, the invariant meaning of zero functors.
- The universal clause on M uses `Mono (ae.counit.app M)`, `Epi (ai.unit.app M)`
  and `(ComposableArrows.mk₂ (ae.counit.app M) (ai.unit.app M)).Exact`.
  This is the short exact sequence with precisely the node's arrows. The arrows
  are components of natural transformations, so the sequence is natural in M.
- The next clause is `IsIso (jL.map (aj.unit.app M))`, using the actual open unit.
- The last two clauses are joint zero detection and joint reflection of
  monomorphisms, as implications on every object and every arrow, respectively.
- The final conjunct quantifies over arbitrary RZ,RV, their `MonObj` structures,
  and specified isomorphisms eZ,eV with `IsMonHom eZ.hom` / `IsMonHom eV.hom`.
  This means ring-object isomorphisms, not arbitrary abelian-sheaf isomorphisms.
  The identical assertion bundle is applied to i-star and j-star composed with
  restriction through eZ,eV; the other functors compose with inverse restriction.
  The three adjunctions are explicitly composed with the equivalence adjunctions,
  in the correct directions. Thus every localization conclusion, including the
  short exact sequence's actual transported arrows, is asserted again. Both
  directions of restriction and their comparison maps have identity carriers;
  transport therefore also retains the abelian unit/counit interpretation.

### Dependency declarations used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (the quasi-compact portion of the finite-type node).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
  The size-convention node is a metatheoretic convention; explicit universes implement it.
- `Sheaf.CategoryTheory.SheafTensor`: `CategoryTheory.sfbSheafTensor_properties`,
  using the existing canonical `sfbSheafTensorStructure` of SheafTensorStructure.
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`: the dependency's
  MonObj/Ab tensor imports and `Functor.monObjCompForget₂` / sheaf ring-object interface.
  The theorem takes an arbitrary MonObj, not just rings in the essential image.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`.
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`:
  `CategoryTheory.Mod.instAbelian`; the existing module-limit/colimit instances
  and `WeilConjectures.CategoryTheory.ModuleObjects.Abelian` give the carrier kernels/cokernels.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction` and their base-change description.
  The recorded ring operations use the canonical upperStar/lowerStar interfaces.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`: all five operations and
  both adjunctions named above. Their full signatures and definitions were read.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; the geometric operations already implement
  its abelian sheafified extension and lift that adjunction by mapModLeft.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`:
  restriction `Mod.comap`; `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`:
  `Mod.comapId`, `Mod.comapComp`, `Mod.comapCongr`.
  `MapMod.comapEquivalenceOfIsIso` was read but requires a commutative source ring,
  so it is not used to impose an unauthorized commutativity hypothesis. The helper
  constructs precisely restriction and inverse restriction from the existing comparisons.

Recorded proof-dependency modules are imported without `public` where not already
publicly available: GrothendieckAbelian.Sheaf, ModuleObjects.KernelStructure,
ModuleObjectCokernelAction, ProEtaleRingedOpenClosed, pro-etale upper/lower-star
Defs and Monoidal, open Projection, and ModuleObjects.LiftExact. The generic
MapMod/ProjectionFormula and scalar modules are already public dependencies of the
operations. The abstract-iso adjunction lemma currently has no recorded module;
no unrecorded private replacement theorem was introduced.

### Edge cases and source check

Read Stacks proetale.tex labels lemma-closed-immersion (09AA),
lemma-closed-immersion-complement-retrocompact-exact (09BM), lemma-open-immersion
(09BN), lemma-ses-associated-to-open (09AH); also the current blueprint's
sk-lem-formal-closed-support unit and adjunction proof. Their hypotheses do not
require X to be qcqs. The complement's quasi-compactness is exactly the hypothesis
used by 09BM and 09AH. The generic module-object lifts never use commutativity.

Checked Z empty (open part is all of X), V empty (closed part has all support),
X empty, the zero ring object (every unital module is zero), and a noncommutative
matrix ring object. The statement admits all of them. Arbitrary non-qcqs X is
retained. The assertions use IsZero rather than equality to a particular chosen
zero object, so different chosen zero modules do not exclude cases. Identity and
nonidentity scalar isomorphisms are both included. The scalar inverse is the
inverse of the specified isomorphism, not an arbitrary equivalence.

### Searches

The prescribed msearch wrapper recorded the following results in searches.jsonl:

- LeanSearch: `Open closed localization exact sequence for module objects over a
  noncommutative ring sheaf`: eight hits concerning ordinary localized modules
  (IsLocalizedModule.map_exact, LocalizedModule.map_exact and related results),
  no matching sheaf/module-object localization statement.
- LeanFinder: `Exact open closed localization for internal left modules over a
  noncommutative ring object on the small proetale site`: eight hits concerning
  condensed modules and ordinary localization, no exact matching statement.
- Loogle: `CategoryTheory.Mod.comap, CategoryTheory.Adjunction`: no hits.
- Mathlib grep: `open.closed|closed.*localization|ringSheaf` under CategoryTheory:
  no hits. Local rg of the project WeilConjectures and Sheaf trees for ringSheaf
  and noncommutative localization found the canonical operations and the existing
  `ringSheaf_closed_localization` in ProEtaleRingSheafClosedLocalization.
  Its signature was read in full: it assumes CompactSpace X and
  QuasiSeparatedSpace X and states only a subset of this node. It is not an exact
  existing match. Grep for the item's DAG id in WeilConjectures found no match.
- Scalar-equivalence rg over the project and Mathlib found
  `Mod.comapEquivalenceOfIsIso`. Its full signature includes `[IsCommMonObj R]`;
  hence it cannot handle this node's noncommutative coefficients. The elementary
  restriction comparisons used by the new helper already exist and are reused.

No disputed statement or node fault was found. Only the named theorem is postponed.
The module passed scompile.py's sandbox and actual-library-path checks cleanly.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
