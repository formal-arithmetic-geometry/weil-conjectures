## Worker report

The module lean/Sheaf/AlgebraicGeometry/QcOpenDerivedLift.lean states
AlgebraicGeometry.exists_qc_derived_lift_of_isCompact_open, with sorry as its only proof.
No definition is introduced and the mathematical statement of the node is unchanged.

Clause-by-clause correspondence:

- "X be an affine scheme": `(X : Scheme.{u}) [IsAffine X]`.
- "U be a quasi-compact open subscheme": `(U : X.Opens)` gives the open subscheme
  `U.toScheme`; `(hU : IsCompact (U : Set X))` is precisely quasi-compactness of
  its underlying open subset. Mathlib's IsCompact does not require Hausdorffness.
- "E be an object of D_QCoh(O_U)": `(E : schemeDerivedQCohCategory U.toScheme)`.
  This uses the dependency's full subcategory, whose property requires quasi-coherent
  cohomology in every integer degree. There is no boundedness hypothesis.
- "There exists E' in D_QCoh(O_X)": `∃ E' : schemeDerivedQCohCategory X`.
- "whose restriction to U is isomorphic to E": the `Nonempty (... ≅ E.obj)` conclusion.
  Its left side applies `mapDerivedCategory` to the composite of the existing
  `SheafOfModules.overFunctor` and the functor of `Scheme.Modules.overEquiv U`.
  The former restricts to Opens(X)/U and the latter identifies that site with Opens(U).
  Mathlib's `Scheme.Modules.overFunctorEquiv` identifies this composite with ordinary
  restriction along U.ι. The `show` annotation makes the equivalence use the shared
  SheafOfModules category instances, instead of the separately packaged X.Modules
  instances; it introduces no chosen object, functor, or extra hypothesis.

The two HasDerivedCategory.{w} binders provide the shared localization models already
required by def-pc-derived-category, on X and U respectively. They impose no geometric
hypothesis and allow every scheme universe u and localization morphism universe w.
All variables and universes are explicitly bound; autoImplicit is disabled.

Dependency declarations used:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Scheme and AlgebraicGeometry.Scheme.Hom; affine structure is
  Mathlib.AlgebraicGeometry.AffineScheme, AlgebraicGeometry.IsAffine.
- def-pc-derived-category: Sheaf.AlgebraicGeometry.DerivedCategory,
  AlgebraicGeometry.schemeDerivedCategory, schemeDerivedQCohProperty, and
  schemeDerivedQCohCategory, whose signatures and docstrings were read in full.
- The dependency's import Sheaf.Paper.DerivedHomMayerVietoris supplies the shared
  AlgebraicGeometry.moduleRings and moduleOverFunctor_additive/limits/colimits instances.
- Mathlib.AlgebraicGeometry.Modules.Sheaf supplies Scheme.Modules.overEquiv and
  overFunctorEquiv. The equivalence is explicitly viewed between the shared module-sheaf
  carriers; this avoids a second HasDerivedCategory on Scheme.Modules.
- CategoryTheory.Functor.mapDerivedCategory is the exact-functor construction.
  Local instance registration of the existing theorem
  Functor.additive_of_preserves_binary_products derives additivity of the equivalence;
  comp_preservesFiniteLimits/comp_preservesFiniteColimits derive exactness of the composite.
  No new theorem or proof is introduced for those already-proved categorical facts.

Edge cases checked before finalizing:

- U empty: allowed; the unique derived object on the empty scheme lifts to the zero object.
- U = X: allowed; ordinary restriction is the identity up to its canonical equivalence.
- X empty: affine and allowed, reducing to the preceding two cases.
- E zero: allowed and lifted by zero; no nonzero assumption is present.
- E unbounded in either direction: allowed; the proof uses unbounded Rj_* and the
  quasi-coherent preservation theorem, rather than a bounded-below replacement.
- No characteristic, Noetherian, integrality, finite-presentation, or connectedness
  condition is imposed. Quasi-compactness is on U, not a vacuous identity morphism.

Sources read: the local Stacks checkout is absent on this machine, so read the official
pages https://stacks.math.columbia.edu/tag/08EE,
https://stacks.math.columbia.edu/tag/08ED and https://stacks.math.columbia.edu/tag/08D5.
08EE invokes 08ED, whose first assertion is exactly the lifting input used here;
08D5(1) is the unbounded quasi-coherent preservation fact. The node's proof_origin
calls lemma-lift-quasi-coherent "36.13.5", whereas the current official page is
36.13.1, Tag 08ED; this is a source-numbering fault only, not a statement correction.
The full two-step node proof is recorded in the theorem docstring (with its geometric
quasi-compactness justification and both named proof dependencies).

Searches for an existing statement:

- msearch.py leanfinder, query "quasi-coherent derived objects lift from quasi-compact
  open subscheme of affine scheme": eight hits, on section extension, quasi-separated
  schemes, site equivalences, and affine limits; none states derived-object lifting.
- msearch.py loogle, query "DerivedCategory, SheafOfModules.overFunctor": zero hits.
- msearch.py grep, query "lift.*quasi|quasi.*lift|mapDerivedCategory", subdirectory
  AlgebraicGeometry: fourteen unrelated quasi-compact-cover and quasi-separated hits.
- msearch.py leansearch, query "derived quasi-coherent sheaves extend from quasi-compact
  open": unavailable, Internal Server Error. No absence verdict inferred from this.
- rg on WeilConjectures/, lean/Sheaf/, and dag/lean_names_upstream.json for
  "lem-sc-qc-open-derived-lift|lift.*quasi.?coherent|quasi.?coherent.*lift": zero hits.
- rg for mapDerivedCategory/restriction and overEquiv in both project source trees
  found the exact-functor construction, shared open-site restriction, and Mathlib's
  existing overEquiv; these are used, not duplicated.
- rg for the proposed theorem name in dag/nodes and lean/Sheaf: no existing declaration.

Validation: scompile.py G1 lem-sc-qc-open-derived-lift compiled the statement cleanly
in 2.7 seconds before the final autoImplicit setting; the delivery dry run recompiles
that final version. Earlier elaboration checks exposed the separate Scheme.Modules
category instance, fixed by the explicit shared-carrier annotation, and missing local
instance registration for additivity and composition, fixed using Mathlib declarations.
No STATEMENT-DISPUTED issue, new nodes, or dependency replacement modules.

## Second reading by G1

Independently opened the delivered node and all 55 lines of QcOpenDerivedLift.lean,
then both statement-dependency nodes and their recorded source modules. Read the
Stacks perfect.tex source online because literature/stacks-project is absent here:
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex,
Conventions, section-lift, lemma-lift-quasi-coherent (Tag 08ED), and
lemma-lift-pseudo-coherent (Tag 08EE). The first assertion of 08ED supplies exactly
the lifting step invoked in 08EE. Its stronger general-scheme version does not
require broadening this affine-specialized node. No standing Noetherian, base-field,
characteristic, boundedness, or finiteness hypothesis was omitted.

Object/hypothesis/conclusion checklist, in the node's quantifier order:

- X is a scheme: `(X : Scheme.{u})`. PASS: the recorded def-pc-scheme declaration
  extends LocallyRingedSpace with local affine charts, not a variety or integral scheme.
- X is affine: `[IsAffine X]`. PASS: Mathlib's canonical map to Spec of global sections
  is an isomorphism; Scheme.isoSpec exhibits the expected affine presentation.
- U is an open subscheme of X: `(U : X.Opens)`, with `U.toScheme` in E's category.
  PASS: this is the canonical open subscheme with restricted structure sheaf, not
  an arbitrary map or an affine open. An isomorphic presentation gives the same notion.
- U is quasi-compact: `(hU : IsCompact (U : Set X))`. PASS: IsCompact is the finite
  subcover property without a Hausdorff assumption. For an open subset it agrees
  with quasi-compactness of the subspace. It does not assume U affine.
- E is any object of D_QCoh(O_U): `(E : schemeDerivedQCohCategory U.toScheme)`.
  PASS: the dependency defines the full subcategory of DerivedCategory of the
  shared O_U-module sheaves by `forall n : Int`, IsQuasicoherent of homology n.
  This is not the derived category of the abelian category of quasi-coherent sheaves.
- There exists E' in D_QCoh(O_X): `exists E' : schemeDerivedQCohCategory X`.
  PASS: the existential follows E, and includes quasi-coherence in every degree.
- E' restricted to U is isomorphic to E: `Nonempty (...obj E'.obj ≅ E.obj)`.
  PASS: opened SheafOfModules.overFunctor, Scheme.Modules.overEquiv and
  overFunctorEquiv, and Functor.mapDerivedCategory. The composite first restricts
  to Opens(X)/U, then transports to O_U-modules; overFunctorEquiv identifies it
  with restrictFunctor U.ι. mapDerivedCategory is induced by applying this exact
  functor termwise to integer cochain complexes. Since D_QCoh is full, an ambient
  isomorphism to E is exactly the required isomorphism, with no extra conclusion.
- The two HasDerivedCategory.{w} binders specify localization models already used
  by the dependency. PASS: they add no geometric property. The explicit `show`
  uses the shared SheafOfModules instances, avoiding a different D(O_X).

Edge cases: U empty, U top, X empty, and E zero are all admitted; the zero object
lifts in the empty-open case, while top restriction is canonically the identity.
There is no Nonempty condition or index family. The cohomology predicate ranges
through all integer degrees, including 0 and negative degrees, without truncation.
No characteristic is fixed. u and w are explicitly declared and generalized;
there is no finite-universe test-object hypothesis. No variable is auto-implicit.

Independent searches with different wording:

- msearch leanfinder: "essential surjectivity restriction derived categories quasi
  coherent sheaves open embedding": eight hits, on localization essential
  surjectivity and sheaf/change-of-rings facts; no derived open lifting statement.
- msearch loogle: "SheafOfModules, DerivedCategory": zero hits.
- msearch grep: "essentially.*surjective|derived.*extend|derived.*lift" in
  AlgebraicGeometry: one group-scheme hit, unrelated to module derived categories.
- rg across Mathlib AlgebraicGeometry, the whole WeilConjectures and lean/Sheaf
  trees, and dag/lean_names_upstream.json for derived extension/lifting and
  restriction/overFunctor essential surjectivity: only unrelated localization,
  ring-derived-map lifting, and six-functor material. No matching theorem found.
  The existing site equivalence and exact-functor construction are reused.

H4/H5/H6/H8/H9: no new definition, private copy, hollow data, extra theorem or proof
is delivered. The sole theorem has sorry as its proof. Local instance attributes
register existing Mathlib results rather than prove anything. Both imports serve
used notions. The source and blueprint tags are present in both docstrings; the
proof gives the finite-affine-cover justification for j quasi-compact, applies
lem-pc-derived-direct-image-preserves-qcoh to Rj_*E, and applies
lem-pc-restrict-derived-direct-image-open with V = U and g = id_U. All lines satisfy
the width convention. No new nodes, replacement dependency modules, or statement
correction are present, so H12/H13 and correction-citer checks do not arise.

Mismatches and changes: none in the Lean or mathematical node statement. Retained
both verbatim; appended this independent review and search evidence only. The old
numerical source reference in proof_origin is historical metadata; the stable tag
and label in the delivered docstrings correctly identify the source.

Validation: scompile.py with the absolute sandbox module path returned exit code 0,
compiled in 2.7 seconds, with no warnings. The first invocation used a relative path
from the read-only checkout and failed before compilation; corrected the invocation
without changing any file. The recorded lean.statement was compared with the file's
entire signature, including binders, existential, restriction composite and isomorphism.
