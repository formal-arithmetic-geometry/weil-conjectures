## Worker report

This stage-2 delivery states
`AlgebraicGeometry.Scheme.isZero_higherDirectImage_cartesianOpen_injective` in
`Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic`.
Its proof is `sorry`. The mathematical statement and all dependency lists of the
item are unchanged. The inherited stage-1 report and historical second-reading
text are replaced by this worker report; an independent second reader still needs
to read and deliver the files.

I read the item, every statement-dependency node and its Lean or Mathlib binding,
the current blueprint proof of `prop-exc-base-change-proper` Steps 2–4, and the
local Stacks texts `more-etale.tex`, `lemma-shriek-proper-and-open` (0F7B), and
`proetale.tex`, `definition-extension-zero` (09AE), `lemma-open-immersion` (09BN).
The item is an extracted pro-etale obligation; 0F7B is its etale analogue, not a
claimed proof of this whole-category pro-etale statement.

Every hypothesis and clause is represented as follows:

| Node clause | Lean rendering |
| --- | --- |
| Finite commutative ring A | `(A : Type u) [CommRing A] [Finite A]` |
| Schemes and named morphisms | `{V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)` |
| Proper p | `[IsProper p]`, including quasi-compactness through Mathlib instances |
| Arbitrary open immersion i | `[IsOpenImmersion i]`, with no quasi-compactness assumption |
| Cartesian U, projections k and r | `pullback p i`, `pullback.fst p i`, `pullback.snd p i`; r is contextual notation |
| Module category on each H | `proEtaleRingModules H (proEtaleConstantRing H A)` |
| Constant ring sheaf | `proEtaleConstantRing H A` is the sheafification of constant `ULift A` on `Scheme.ProEt.topology H` |
| Ordinary uncompleted Rp_* | `proEtaleConstantDerivedDirectImage p A`, the K-injective right-derived functor of canonical sectionwise module direct image |
| F[0] | `(DerivedCategory.singleFunctor _ 0).obj F` |
| R^q p_*F = H^q(Rp_*(F[0])) | `(DerivedCategory.homologyFunctor _ (q : ℤ)).obj` applied to that derived image |
| Uniform bound d >= 0 for every module F and q > d | `hcd : ∃ d : ℕ, ∀ (F : proEtaleRingModules V (proEtaleConstantRing V A)) (q : ℕ), d < q → IsZero ...`; a nonnegative integer bound is precisely a natural-number bound |
| Any injective J on U | `(J : proEtaleRingModules (pullback p i) (proEtaleConstantRing (pullback p i) A)) [Injective J]` |
| k_!J | `(sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J` |
| R^q p_*(k_!J) = 0 for q > 0 | `∀ q : ℕ, 0 < q → IsZero ...`, using the identical single-object and homology functors |
| Contextual i^*, k^*, r_*, i_! | The recorded canonical operation/extension modules provide them; no independent maps, identifications or assumptions are supplied |
| No etale-origin restriction | J ranges over all intrinsic constant-ring module sheaves |

I read `CategoryTheory.Functor.rightAcyclic` in the recorded upstream
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`: it is positive
right-derived vanishing on objects. The theorem expands the node's displayed
vanishing equation directly with its prescribed `H^q(Rp_*(F[0]))` convention;
no private acyclicity predicate or second derived direct image is introduced.
The module now publicly imports this recorded acyclicity dependency as well.
The theorem docstring explicitly follows all six proof steps of the current node.

Dependency declarations used (all signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; scheme limits come from `Mathlib.AlgebraicGeometry.Limits`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` on the original small site.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  a transparent abbreviation of Mathlib `SheafOfModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`: the current recorded
  operations module, reexporting `proEtaleRingModules` and the arbitrary-coefficient
  operations. The canonical `proEtaleConstantModuleDirectImage` is defined in
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`; its unbounded right-derived
  abbreviation `proEtaleConstantDerivedDirectImage` is in the directly imported
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`. Its fixed-scalar middle
  functor is the actual open left Kan extension and sheafification in
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`;
  canonical realization equivalences transport the coefficient actions.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, the cohomology-sheaf node's Mathlib binding.

Stated proof dependencies are imported without `public`: K-injective resolutions,
bounded-below injective representatives and right-derived computation, exact
weakly contractible evaluation, restriction of injectives, normalized open base
change, localization and realization transport, the intrinsic open adjunction,
bounded continuity and vanishing detection. Mathlib stability/quasi-compactness
modules cover the geometric leaves. `lem-sp-proetale-open-injective-proper-acyclic`
has no recorded Lean declaration yet, so no module exists to import for it; this
does not prevent stating this item. No other DAG theorem is newly stated here.

Edge cases checked: empty base open (empty pullback and zero extension), whole
base open (identity open), zero ring, zero injective, identity proper morphism,
q=1, and d=0. q=0 is intentionally excluded. The finite-cd bound is retained even
though the node's proof plan does not use it. The old affine-line counterexample
is irrelevant: an open in the proper source need not be the inverse image of a
base open. No Noetherian, characteristic, nonzero-ring, quasi-compact-open or
etale-origin restriction is introduced. Universes follow the recorded convention:
schemes/coefficients use u, site objects/module values use u+1, site morphisms
use u; no equality between the two site universes is imposed.

Searches, including fresh continuation searches, are logged in `searches.jsonl`:

- `msearch.py leanfinder`: “proper direct image extension by zero injective
  pro-etale module”, and the expanded query beginning “An injective sheaf of finite
  ring modules on the inverse image of an arbitrary base open”. Returned scheme
  section-map, Zariski module and condensed-category facts do not state this lemma.
- `msearch.py loogle`: the earlier short `rightDerivedFunctor Injective` and
  unqualified name queries failed to resolve identifiers. Fresh query
  `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` succeeds. I read
  the complete signature in Mathlib `CategoryTheory/Abelian/RightDerived.lean`:
  its functor input itself must be injective, whereas k_!J is not assumed
  injective. Thus it does not specialize directly to this assertion.
- `msearch.py grep`: `extensionByZero|proper.*acyclic|acyclic.*proper` in
  `AlgebraicGeometry` and `CategoryTheory` found no match.
- `rg` over upstream `WeilConjectures` and shared `lean/Sheaf`, for the item id,
  proposed declaration name and proper/acyclic terms, found no matching pro-etale
  statement. `OpenExtendedInjectiveProperAcyclic` uses the etale site and is an
  analogue, not a duplicate.

No statement correction, new notion, helper theorem or statement dispute is needed.
All item metadata except `lean` is preserved. `lean.statement` is extracted verbatim
from the theorem signature, and UTC dates come from `date -u +%F`.

## Dependency modules

`def-weil-pbc-proetale-modules` receives an import-only repair in its existing
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` module. The published source imports
both `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` and
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, which collide on
`AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf._proof_2` and prevent
importing the extension-by-zero dependency. The repair removes only the direct
`WeilConjectures` import. The recorded `Sheaf` owner and its import through
`BoundedConstructibleComplexes` retain constructibility. Every declaration,
signature, body and docstring is unchanged. The dependency node copy changes only
its `lean` record, including an explanatory `note` and worker/date fields.

Both delivered files compile cleanly with `scompile.py` in its authorized local
overlay mode (`NT_SCOMPILE_LOCAL=1`), with the unchanged 60-second per-file limit.
The continuation recompiled both files after adding the acyclicity import and
expanding the proof docstring: the library-file checks took 2.6 seconds for the
item and 7.6 seconds for the repaired dependency, with no warnings or errors.
Server mode was also tried and confirms the old duplicate: its overlay recursively
compiles the published dependency before considering a delivered same-path
replacement. Local mode accepts that replacement. Server preflight still runs
through `deliver2.py`. No compiler/delivery tool or live source was edited.
The continuation retried server compilation with both sibling paths explicitly
supplied in dependency order. It exited 75 while compiling the published overlay
`ProEtaleFiniteModules`, still importing the removed upstream constructibility
module. Reading that upstream module with `scompile.py --source` confirmed the
same declaration name; its stratification predicate differs from the project's
recorded predicate, so substituting its definition would change the dependency.
The repair therefore retains the project's owner and removes only the conflicting
upstream import. A direct source diff confirms this is its only source change;
both node copies differ from the repository only in `lean`.

Final validation command:
`NT_SCOMPILE_LOCAL=1 python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q52
lem-exc-proetale-cartesian-open-injective-acyclic --no-push`.
This worker returns READY only after that dry run prints OK.
The continuation's first preflight accepted the dependency repair's scope but
requested two bookkeeping fixes: its signature parser records
`abbrev FiniteCoefficientModules` without the `noncomputable` modifier, and its
report shape requires the second-reading section. The dependency record now uses
that parser signature; the section below explicitly records that the independent
reading is pending, without claiming that this worker performed one.

## New nodes

None. This worker does not push or claim an independent second reading.

## Earlier second reading (a previous round; superseded)

Pending independent second reader. This is the stage-2 worker's draft and dry run;
the second reader must replace this paragraph with their own hypothesis-by-hypothesis
review of the item, the import-only dependency repair, and the final compilation
and preflight results before delivering. No independent second reading has been
performed or asserted by this worker.

## Second reading by Q52

Independent second reader, 2026-10-16 UTC. I did not write the statement. I read
both delivered node records and modules, the twelve statement-dependency records,
their actual declarations, the six current proof steps, and the source places.
This section supersedes the pending-reader paragraph above. The Lean statement
says exactly what the current node says; no statement correction is required.

My object/hypothesis/conclusion inventory and its comparison with Lean:

| Node item | Lean rendering and verdict |
| --- | --- |
| A finite commutative ring A | `(A : Type u) [CommRing A] [Finite A]`; exact, including the zero ring and every characteristic. |
| Schemes V, T, W and morphisms p, i | `{V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)`; exact Mathlib schemes and morphisms. |
| Proper p | `[IsProper p]`; exact. Its universally-closed instance supplies quasi-compactness, so Mathlib's locally finite type clause agrees with finite type here. |
| An arbitrary base open i | `[IsOpenImmersion i]`; exact. No quasi-compactness or other condition is imposed on i. |
| U = V times_T W, k and r | `pullback p i`, `pullback.fst p i`, `pullback.snd p i`; exact chosen fibre product and projections. Only k occurs in the conclusion; r is contextual and need not be separately bound. |
| All modules over the constant ring on the small pro-etale site | `proEtaleRingModules H (proEtaleConstantRing H A)`; exact. I unfolded these to Mathlib `SheafOfModules` over the forgotten-commutative constant ring sheaf. |
| Ordinary direct image and constant-ring identifications | `proEtaleConstantModuleDirectImage p A` in the definition of the derived operation; exact sectionwise precomposition with canonical constant-section scalar map. No freely chosen coefficient isomorphism is a hypothesis. |
| Ordinary uncompleted derived direct image | `proEtaleConstantDerivedDirectImage p A`; exact K-injective `rightDerivedFunctor` in the unbounded category of all module sheaves. |
| F[0] and H^q | `DerivedCategory.singleFunctor _ 0` and `DerivedCategory.homologyFunctor _ (q : ℤ)`; exact cochain conventions and actual cohomology sheaves. |
| There exists a single nonnegative d, uniform in every F and q > d | `hcd : ∃ d : ℕ, ∀ (F : proEtaleRingModules V ...) (q : ℕ), d < q → IsZero ...`; exact quantifier order. A nonnegative integer is equivalently a natural number; q > d cannot be negative. |
| Every injective J on U | `(J : proEtaleRingModules (pullback p i) ...) [Injective J]`; exact Mathlib categorical injectivity, with no etale-origin restriction. |
| Extension k_!J | `(sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J`; exact canonical open extension, whose pullback open-immersion instance comes from base change. |
| p_*-acyclicity | `∀ q : ℕ, 0 < q → IsZero ...`; exact displayed positive-degree vanishing. Every positive integer is represented, and the node explicitly specifies this derived-cohomology formulation. |
| Contextual i_!, i^*, k^*, r_* | Supplied by the recorded operation and extension modules. They are not additional arbitrary input functors or hypotheses and do not occur in the final vanishing formula. |

I opened `ProEtaleDerivedCategory`, `ProEtaleOperations`,
`ProEtaleInverseImage`, `ProEtaleConstantDerivedDirectImage`,
`ProEtaleIntrinsicFiniteOperations`, `ProEtaleIntrinsicExtensionByZero`,
`ProEtaleFiniteModuleIntrinsicComparison`, and `RingedSiteModules`. I also read
Mathlib's scheme, proper/open, pullback and projections, constant sheaf,
`Injective`, `homologyFunctor`, and the recorded upstream `Functor.rightAcyclic`.
The latter uses positive ordinary right-derived vanishing; the item expands the
node's specified H^q(Rp_*(F[0])) expression without defining another acyclicity
notion. Module values live in u+1, small-site objects in u+1 and morphisms in u.
No equality of these universes is assumed; schemes and finite coefficient rings
can be placed in a common universe without excluding a mathematical case.

I read Stacks `more-etale.tex`, `lemma-shriek-proper-and-open` (0F7B), including
the section preamble and the injective-acyclicity argument in case (b). It concerns
etale sheaves and torsion coefficients; it is an analogue, as the node and module
explicitly say. I read `proetale.tex`, `definition-extension-zero` (09AE), and
`lemma-open-immersion` (09BN). Neither imposes quasi-compactness on an open
immersion. The subsequent complementary-closed short exact sequence does impose
quasi-compactness, and that condition has correctly not been imported into this
statement. I read the blueprint source and the current parent node's Steps 2--4;
the current DAG extracts the whole-category pro-etale obligation explicitly.
The item's six-step proof docstring follows evaluation, finite principal-open
exhaustion, the existing quasi-compact obligation, the open-adjunction colimit,
bounded continuity, and vanishing detection in that order. It does not claim
geometric stalk conservativity on the whole pro-etale category.

For the extension's actual construction I read the exact shared framework file
`lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Open/Defs.lean`
and `coord/pefw-upstream-framework.md`. Its middle functor is left Kan extension
along the localization followed by sheafification. For an open, the unique
factorization summand or empty sum gives precisely the node's presheaf. The
intrinsic realization extends fixed scalar actions along the sheafification
unit; its equivalence inverse is determined by that functor. No object data is
chosen from a bare existence theorem.

Edge cases: W empty makes U empty and gives zero extension; W = T specializes
to the identity open; an empty scheme and a zero injective are allowed. The zero
ring is allowed and forces zero modules. d = 0 and q = 1 are covered, while q = 0
is intentionally excluded. There is no index set in the signature; the empty
finite subset in the proof's exhaustion is included. No Noetherian, finiteness of
the schemes, characteristic, nonzero coefficient, or quasi-compact-open condition
has appeared. The uniform hcd hypothesis is retained even though the stronger
quasi-compact obligation makes it unnecessary in this proof plan.

Fresh independent searches (also logged by msearch in `searches.jsonl`):

- LeanFinder: `Injective module on a cartesian base open extends by zero to an
  acyclic object for a proper proetale pushforward`. Eight hits, chiefly scheme
  pushforward faithfulness, section-map facts, and
  `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`; none is this
  theorem.
- Loogle: `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`.
  I opened its full Mathlib signature. It requires the input of the functor to
  be injective; here only J is injective, not its open extension. It is a tool,
  not an existing match.
- msearch grep: `proper.*[Aa]cyclic|[Aa]cyclic.*proper|cartesianOpen` in
  AlgebraicGeometry returned no hit. Independent rg over upstream
  `WeilConjectures`, project `lean/Sheaf`, and Mathlib CategoryTheory searched
  `openExtendedInjectiveProperAcyclic`, `isZero_higherDirectImage_cartesianOpen`,
  `cartesian.*acyclic`, `acyclic.*cartesian`, and
  `extension.*zero.*injective`. The relevant project hit was
  `OpenExtendedInjectiveProperAcyclic`. I read it: its category is the small
  etale site and its derived category is Plus, so it is not this statement.

There are no new nodes or a `statement_change` to audit. For the sibling
`def-weil-pbc-proetale-modules` repair, I read its complete definition and module:
continuous functions on the quotient connected-component space, presheaf
restrictions, sheafification, left modules, ordinary derived localization, D+,
and the full essential image of bounded constructible etale complexes. Each
clause matches the node, including noncommutative finite rings. A source diff
shows the only Lean change is deletion of
`public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
The recorded Sheaf owner and its `BoundedConstructibleComplexes` import remain.
I fetched the current upstream declaration with `scompile.py --source`: it uses
`Stratification T`, whereas the project's owner uses the node's locally closed
strata with constructible images. Keeping the project owner both avoids the
colliding generated proof declaration and preserves the recorded notion. This
is an import repair, not a new copy or a weakened constructibility predicate.
No declaration, body, signature, proof or docstring of that dependency changes.

No H3/H4/H5/H6/H8/H9 mismatch was found in the proposed Lean files, so I left
both files intact. I replaced the absence of an independent reading by appending
this actual review. Both delivered node copies differ from the shared base only
in `lean`; the item's `lean.statement` is byte-for-byte the theorem signature.
All variables/universes are explicitly bound and there is no file-local notation,
private notion, hollow definition, or newly proved theorem.

Validation: I compiled both sibling modules together through
`NT_SCOMPILE_LOCAL=1 python3 /home/ubuntu/weil-launcher-nt/scompile.py Q52
lem-exc-proetale-cartesian-open-injective-acyclic` followed by both file paths.
The library checks finished in 2.8 seconds (item) and 8.1 seconds (dependency),
with exit status 0 and no warnings or errors. The prescribed per-file timeout
remained 60 seconds. Delivery preflight and push results are recorded below.

The independent reader's prescribed `deliver2.py --no-push` run returned
`OK (dry run): commit 59dc6afba9 passes the preflight and compiles; nothing pushed`.
Both sibling modules and both lean-only node deltas passed. The authorized final
delivery is performed with the same wrapper and local compilation mode.
