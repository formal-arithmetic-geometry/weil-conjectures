## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent`, declaration
`AlgebraicGeometry.Etale.smooth_punctual_purity_ascent`. Its only theorem has proof `sorry`.
The natural-language statement is unchanged. Its full seven-step proof plan is in the
Lean docstring. All variables and the universe `u` are explicit, with `autoImplicit false`.

Source checked: ILO, Exposé XVI, Definitions 3.2.1--3.2.2, printed p.244, and Corollary
3.5.6, printed p.249, in the repository's PDF. The corollary says a smooth scheme over
a regular finite-type S-scheme is punctually pure when the base is punctually pure.
The node's finite-type and Noetherian hypotheses are retained exactly.

Clause-by-clause correspondence:

- Prime and coefficients: `(ℓ : ℕ) (hℓ : ℓ.Prime)`. The canonical class uses
  `regularClassCoefficients ℓ 1 = ULift (ZMod (ℓ ^ 1))`, the published coefficient
  ring for F_ell in the site coefficient universe. This is the same coefficient ring
  up to the canonical ULift identification and `pow_one`; no coefficient enlargement
  or characteristic case is excluded.
- Ordinary small-etale derived categories and Tate twists: `regularClassTwist`,
  `_root_.DerivedCategory.Plus.singleFunctor`, and the published closed support adjunction.
  D+ is the fully faithful bounded-below subcategory of the stated ordinary derived
  category. Isomorphism of this bounded-below class is equivalent in D+ and D.
- Regularity of X: `(hX : IsRegularScheme X)`, precisely locally Noetherian plus
  regular local rings, using the recorded definition, not a private stalk predicate.
- Trait: `R : Type u`, `[CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]`,
  `hDim : ringKrullDim R = 1`, and
  `hPrincipal : (IsLocalRing.maximalIdeal R).IsPrincipal`. Its scheme is literally
  `Spec (.of R)`. The node describes a uniformizer but does not use a chosen one in
  the hypotheses or conclusion; `IsPrincipal` is the existence of a generator of
  exactly that maximal ideal. No particular generator is added as independent data.
- Invertibility on the trait: `(hInv : IsUnit (ℓ : R))`. Under the canonical
  global-section isomorphism of an affine spectrum this is precisely invertibility
  on S; it pulls back to X and Y.
- X over S: `[X.Over (Spec (.of R))]` with structure morphism `X ↘ Spec (.of R)`.
  Finite type is the recorded conjunction of `LocallyOfFiniteType` and `QuasiCompact`
  on this very structure morphism.
- Smooth finite-type morphism: `(q : Y ⟶ X) [Smooth q] [LocallyOfFiniteType q]
  [QuasiCompact q]`. These are the dependency declarations, with no separatedness,
  excellence, flatness, chosen factorization, or fixed relative dimension imposed.
- Noetherian Y: `[IsNoetherian Y]`, exactly as stated.
- Punctual purity of X: `(hPure : IsPunctuallyPure ℓ hℓ X)`. Its new shared definition
  is detailed below and renders the local closed-point Kummer map, not weight purity.
- Both conclusions are present: `IsRegularScheme Y ∧ IsPunctuallyPure ℓ hℓ Y`.

Punctual-purity clauses, implemented in the new definition module:

- A point `w : W` gives local ring `W.presheaf.stalk w`, local scheme
  `Spec (W.presheaf.stalk w)`, residue field `W.residueField w`, and closed immersion
  `Spec.map (W.residue w)`; these are the recorded Mathlib declarations. In particular
  the closed point is in the local scheme, not the possibly nonclosed point of W.
- The actual dimension is witnessed by `d : ℕ` and
  `ringKrullDim (W.presheaf.stalk w) = (d : WithBot ℕ∞)`. Regular local Noetherian
  rings have finite dimension. No arbitrary codimension is substituted.
- The witnesses `_hN`, `hi`, `hInv` provide Noetherianity of the local scheme,
  regularity of the closed-point immersion of codimension d, and invertibility
  needed to evaluate the published class family. These hold independently of purity
  for every regular Noetherian W with ell invertible. They are not assumptions added
  to the theorem. Proof irrelevance removes dependence on these evidence terms.
- `regularImmersionClasses` selects the family from the recorded *unique*-existence
  theorem `regular_immersion_class_calculus`; no arbitrary map or Nonempty class
  is supplied as a hypothesis or chosen from an undetermined existence assertion.
- `supportedExtPlusHom` is an actual construction using `Ext.hom`, the canonical
  degree-zero inclusion comparison, the shift comparison and the fully faithful
  `DerivedCategory.Plus.ι.preimage`. It has no postponed proof or unspecified data.
- `punctualPurityClassMap` transposes the level-1 class with signed tensor parameter
  zero through `closedSupportPlusAdjunction`, transporting the left adjoint by
  `Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`. Its map on degree-zero
  sheaves uses `Functor.mapDerivedCategoryPlusSingleFunctor`. Thus it is exactly
  A_kappa(w) -> j_w^! A_W_w(d)[2d] with the fixed Kummer normalization.
- `IsPunctuallyPureAt` tests `IsIso` of this canonical map, not mere isomorphism of
  the objects. `IsPunctuallyPure` quantifies over every `w : W`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read with `scompile.py --source`
  because the older local upstream checkout lacks it): ordinary etale derived categories;
  `AlgebraicGeometry.Etale.DerivedCategoryModule` comes from the public coefficient import.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateTwist`, used by
  the published signed `Scheme.finiteEtaleTateSheaf` underlying `regularClassTwist`.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`: `regularClassCoefficients`,
  `regularClassTwist`, `RegularImmersionClassFamily`, `RegularImmersionClassLaws`, and
  `regular_immersion_class_calculus` in namespace `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange`: the recorded
  `closedSupportPlus` and `closedSupportPlusAdjunction`, with their canonical counit.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`
  (the quotient map), and the closed-immersion instance for its spectrum map.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Smooth`:
  `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`.

The recorded proof-dependency modules that already have declarations are imported:
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`,
`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`,
`Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.AlgebraicGeometry.Noetherian`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
The class-calculus, regular-scheme and closed-support modules already enter through
public statement dependencies. The three proof-only nodes
`lem-per-prime-field-punctual-purity`, `lem-per-punctual-purity-two-of-three`, and
`lem-per-regular-supported-base-change` currently have no Lean declarations, so there
are no modules to import for them. Their mathematical use is retained in the proof plan.

Edge cases checked before writing: empty Y makes the purity predicate vacuous;
identity q and relative dimension zero do not require special data; generic and nonclosed
points use their full local rings; d = 0 gives the identity local closed immersion and
its normalized identity class; no perfect-residue-field or mixed-characteristic hypothesis
was imposed. A trait is a domain with nonzero one-dimensional maximal ideal, so neither
the zero ring nor a field is accidentally admitted as a trait. Arbitrary scheme universe
u and coefficient universe u+1 match the published etale constructions.

Searches (all three required kinds, and both project trees):

- `msearch.py`, LeanFinder: “Smooth ascent of punctual purity of regular schemes
  fundamental class of the closed point of a local scheme is an isomorphism”. Eight
  results, principally `stalkClosedPointIso` and `SpecToEquivOfLocalRing`; no match.
- `msearch.py`, Loogle: `AlgebraicGeometry.Smooth, IsIso`. Zero hits; the service reports
  `IsIso` unknown, so this is a failed query rather than negative mathematical evidence.
- `msearch.py`, Mathlib grep `Punctual|punctual` in AlgebraicGeometry: zero hits.
- `msearch.py`, LeanFinder: “canonical supported fundamental class map from constant
  sheaf to exceptional inverse image twisted shifted derived category”. Eight hits
  include `Sheaf.H`, derived single functors and t-structure predicates, none the notion.
- `msearch.py`, LeanSearch: “punctual purity regular local scheme supported fundamental
  class isomorphism”. Eight hits on stalk spectra and local schemes; no predicate match.
- `rg` in Mathlib, upstream `WeilConjectures` and side `lean/Sheaf`, including
  `Punctual|punctual`, `IsPunctuallyPure|PunctualPurity|punctual.*purity` and
  `supportedClassMap|fundamentalClassMap`. Upstream weight purity is a different notion.
  The upstream smooth fundamental-class map assumes smooth schemes over a field and
  cannot express these arbitrary regular local schemes.
- Search for the item id in upstream `WeilConjectures`: no existing declaration.
- DAG definition-node search and `tools/blueprint_refs.py search punctual purity`:
  no definition node for purity of regular local pairs. The 15 blueprint results
  concern purity of Frobenius weights. The existing class-calculus node supplies the
  class, but not the predicate saying its local closed-point transpose is invertible.

The exact msearch results, including hit names and digests, are preserved in the new
node's `mathlib_searches`. No statement correction or dispute of this item is needed.
The dependency class-calculus docstring already carries a dispute about uniqueness of
its family from the stated laws. This delivery uses that dependency's published unique-
existence interface; it does not independently resolve or strengthen its assertion.

Validation: both delivered modules compiled independently through `scompile.py`,
including the dependency-order private-library and sandbox checks, with no warnings,
in 40.5/39.0 seconds for PunctualPurity and 4.9/4.8 seconds for the ascent theorem.
The initial ordinary call without that source failed while compiling the pre-existing
RegularImmersionClassCalculus module: lines 69 and 80 could not find
`AlgebraicGeometry.Scheme.finiteEtaleTwistPullbackData`. That helper is present in the
recorded dependency's published source (read with `scompile.py --source`) but absent in
the compiled interface selected by the default overlay. The unchanged source is now
included in this delivery as the authorized dependency-interface repair; no launcher
tools, source-selection manifests or live modules were edited, and no mathematical
change was made to the dependency.

## New nodes

`def-per-punctual-purity` introduces the shared predicates
`AlgebraicGeometry.Etale.IsPunctuallyPureAt` and `IsPunctuallyPure`, with their concrete
canonical class map and Ext-to-D+ transport. Source: ILO XVI 3.2.1--3.2.2, p.244;
the class normalization is XVI 2.3.1--2.3.2. The module imports the recorded definitions
and supplies actual constructions; it introduces no new theorem with `sorry`. The
node cites exactly the existing notions its statement uses. Its ancestry is that of
this item, prefixed with the item id. The searches above found no existing predicate
for the regular-local-pair notion, and the item gains this node in `stmt_deps`.

Final dry-run result: after adding the authorized dependency-interface repair,
`deliver2.py Q03 lem-per-smooth-punctual-purity-ascent --no-push` exited 0. It compiled
the three delivered modules (including the repaired Tate pullback source), passed packet
preflight, and reported commit `1eb963a8ae`; nothing was pushed by the dry run. The
repair supplies the structured `finiteEtaleTwistPullbackData` interface that the default
overlay lacked, so `RegularImmersionClassCalculus` now compiles through the same source
selection used by delivery.

## Second reading by Q03

I reread the item, the new punctual-purity node and the dependency repair against their
Lean files. The ascent theorem keeps every original hypothesis and both conclusions. The
new definition's local-ring, residue-field, dimension and canonical-class clauses match
its statement; the three cited local notions are separately bracketed in the node. The
Tate-pullback dependency source is unchanged mathematically and only exposes the
structured declarations needed by its recorded consumer. No mismatch or statement change
was found.

## Dependency modules

`lem-asd-etale-finite-twist-pullback` is copied with its unchanged mathematical source and a lean-only interface repair. The server-published interface selected by the default overlay omitted `AlgebraicGeometry.Scheme.FiniteEtaleTwistPullbackData` and `finiteEtaleTwistPullbackData`, so the recorded consumer `RegularImmersionClassCalculus` failed at lines 69 and 80 with unknown constants. The delivered module retains the original theorem and adds the structured declarations already present in the published source; the only source change is this repair note comment. Its node record keeps all original fields except the required `lean` record, which records the usable declaration list and this reason.
